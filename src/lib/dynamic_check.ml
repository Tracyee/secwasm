open Ast
open Sec

let rec log2 x = match x with 1 -> 0 | _ -> 1 + log2 ((x + 1) / 2)

type context = { locals : labeled_value_type list; memory : wasm_memory }

let translate_store (c : context) (encoded_lbl : int) :
    context * wasm_instruction =
  (* We extend the list of locals with two extra items,
         for saving the value to be stored and address to
         stored into *)
  let idx_val = List.length c.locals in
  let idx_addr = List.length c.locals + 1 in
  let new_ctxt =
    {
      c with
      locals =
        (* labels don't matter *)
        c.locals @ [ { t = I32; lbl = Secret }; { t = I32; lbl = Secret } ];
    }
  in
  ( new_ctxt,
    WI_Block
      ( BlockType
          (* labels don't matter *)
          ([ { t = I32; lbl = Secret }; { t = I32; lbl = Secret } ], []),
        [
          (* save value *)
          WI_LocalSet idx_val;
          (* save address *)
          WI_LocalSet idx_addr;
          (* === BEGIN STORE VALUE *)
          WI_LocalGet idx_addr;
          (* Start of BITMASK#0 *)
          WI_Const (-1);
          WI_Const 31;
          WI_Const c.memory.size;
          WI_BinOp Sub;
          WI_BinOp Shr_u;
          (* Top of the stack: 01111111 where 0 is at index mem_size (from the right) *)
          (* Next element    : addr *)
          (* Force addres into lower part of memory *)
          WI_BinOp And;
          (* Get value *)
          WI_LocalGet idx_val;
          (* Store it - label doesn't matter *)
          WI_Store Secret;
          (* === BEGIN STORE LABEL *)
          WI_LocalGet idx_addr;
          (* Start of BITMASK#1 *)
          WI_Const 1;
          WI_Const 15;
          WI_Const c.memory.size;
          WI_BinOp Add;
          WI_BinOp Shl
          (* Top of the stack: 1000000 where 1 is at index mem_size (from the right) *);
          (* Next element    : addr *)
          (* Force address into upper part of memory *)
          WI_BinOp Or;
          (* Push label on stack *)
          WI_Const encoded_lbl;
          (* Store it - label doesn't matter *)
          WI_Store Secret;
        ] ) )

let translate_load_secret (c : context) : context * wasm_instruction =
  (* We extend the list of locals with two extra items,
         for saving the value to be stored and address to
         stored into *)
  let idx_val = List.length c.locals in
  let idx_addr = List.length c.locals + 1 in
  let new_ctxt =
    {
      c with
      locals =
        (* labels don't matter *)
        c.locals @ [ { t = I32; lbl = Secret }; { t = I32; lbl = Secret } ];
    }
  in
  ( new_ctxt,
    WI_Block
      ( BlockType (* labels don't matter *) ([ { t = I32; lbl = Secret } ], []),
        [
          (* save value *)
          WI_LocalSet idx_val;
          (* save address *)
          WI_LocalSet idx_addr;
          (* === BEGIN CHECK LABELS *)
          WI_LocalGet idx_addr;
          (* Start of BITMASK#1 *)
          WI_Const 1;
          WI_Const 15;
          WI_Const c.memory.size;
          WI_BinOp Add;
          WI_BinOp Shl
          (* Top of the stack: 1000000 where 1 is at index mem_size (from the right) *);
          (* Next element    : addr *)
          (* Force address into upper part of memory *)
          WI_BinOp Or;
          (* Load labels from memory (4 bytes, i.e. 4 labels) - label doesn't matter*)
          WI_Load Secret;
          (* push 0b00000001000000010000000100000001*)
          WI_Const 16843009;
          (* TODO : Do we even need to check anything here, or is it just for translate_load_public? *)
          WI_BinOp Eq;
        ] ) )

let transform_instr (c : context) (i : wasm_instruction) :
    context * wasm_instruction =
  match i with
  | WI_Load l -> (
      match l with
      | Public -> failwith "TODO"
      | Secret -> translate_load_secret c)
  | WI_Store l -> translate_store c (SimpleLattice.encode l)
  | _ -> (c, i)

let rec transform_seq (c : context) (seq : wasm_instruction list) :
    context * wasm_instruction list =
  match seq with
  | [] -> (c, [])
  | i :: rest ->
      (* transform the instruction and get a new context with updated locals *)
      let c', i' = transform_instr c i in
      (* transform the rest and get a new context again *)
      let c'', rest' = transform_seq c' rest in
      (* return the newest context and transformed list of instructions *)
      (c'', i' :: rest')

let transform_func (m : wasm_memory) (f : wasm_func) : wasm_func =
  let ctxt = { locals = f.locals; memory = m } in
  (* transform the body of f*)
  let ctxt', new_body = transform_seq ctxt f.body in
  { f with body = new_body; locals = ctxt'.locals }

let transform_module (m : wasm_module) : wasm_module =
  match m.memory with
  (* if module doesn't use a memory it doesn't typecheck *)
  | None -> m
  | Some mem ->
      (* double the size of the memory and make sure it's a multiple of 2
         This makes splitting an address up into low/ high addresses easier *)
      let mem' = { size = log2 mem.size * 2 } in
      {
        m with
        memory = Some mem';
        functions = List.map (transform_func mem') m.functions;
      }
