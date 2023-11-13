open Ast
open Sec

let rec log2 x = match x with 1 -> 0 | _ -> 1 + log2 ((x + 1) / 2)

type context = {
  locals : labeled_value_type list (* params and locals *);
  memory : wasm_memory;
}

let push_bitmask0 (c : context) =
  [
    (* push 1111...111 *)
    WI_Const (-1);
    WI_Const 16;
    WI_Const (log2 c.memory.size);
    (* compute 16 - (log mem_size) *)
    WI_BinOp Sub;
    (* shift 11111 right with 32 - (log mem_size) *)
    WI_BinOp Shr_u
    (* = 01111111 where 0 is at index mem_size + 1 (from the right) *);
  ]

let push_bitmask1 (c : context) =
  [
    (* Size of memory in bytes = mem_size * 64 * 2^10 = 2^(16 + log mem_size) *)
    WI_Const 1;
    WI_Const 16;
    WI_Const (log2 c.memory.size);
    WI_BinOp Add;
    WI_BinOp Shl
    (* = 100000 where 1 is at index log mem_size + 16 (from the right) *);
  ]

let push_store_interleaved (idx_val : int) (idx_addr : int)
    (lbl : SimpleLattice.t) =
  let mask_lbl =
    match lbl with
    | Public -> []
    | Secret -> [ WI_Const 0x01000100; WI_BinOp Or ]
  in
  [
    (* === BEGIN THE FIRST STORE *)
    WI_LocalGet idx_addr;
    (* Get value *)
    WI_LocalGet idx_val;
    (* Push 0xFF *)
    WI_Const 0xFF;
    (* val & 0xFF *)
    WI_BinOp And;
    (* Get value again *)
    WI_LocalGet idx_val;
    (* Push 8 *)
    WI_Const 8;
    (* val << 8 *)
    WI_BinOp Shl;
    (* Load 0xFF0000 *)
    WI_Const 0xFF0000;
    (* (val << 8) & 0xFF0000 *)
    WI_BinOp And;
    (* (val & 0xFF) | ((val << 8) & 0xFF0000) *)
    WI_BinOp Or;
  ]
  @ mask_lbl
  @ [
      (* Store value - label doesn't matter *)
      WI_Store Secret;
      (* === BEGIN THE SECOND STORE *)
      WI_LocalGet idx_addr;
      (* Push 4 *)
      WI_Const 4;
      (* 2*addr + 4 *)
      WI_BinOp Add;
      (* Get value *)
      WI_LocalGet idx_val;
      (* Push 16 *)
      WI_Const 16;
      (* val >> 16 *)
      WI_BinOp Shr_u;
      (* Push 0xFF *)
      WI_Const 0xFF;
      (* (val >> 16) & 0xFF *)
      WI_BinOp And;
      (* Get value again *)
      WI_LocalGet idx_val;
      (* Push 8 *)
      WI_Const 8;
      (* val >> 8 *)
      WI_BinOp Shr_u;
      (* Load 0xFF0000 *)
      WI_Const 0xFF0000;
      (* (val >> 8) & 0xFF0000 *)
      WI_BinOp And;
      (* ((val >> 16) & 0xFF) | ((val >> 8) & 0xFF0000) *)
      WI_BinOp Or;
    ]
  @ mask_lbl
  @ [ (* Store value - label doesn't matter *) WI_Store Secret ]

let push_load_interleaved (idx_addr : int) (idx_tmp : int) =
  [
    (* === Load the first value *)
    WI_LocalGet idx_addr;
    (* Load from memory - label doesn't matter *)
    WI_Load Secret;
    (* Store the first half in a local variable (tee_local idx_fst) *)
    WI_LocalSet idx_tmp;
    WI_LocalGet idx_tmp;
    (* Push mask for 0xFF *)
    WI_Const 0xFF;
    (* fst & 0xFF *)
    WI_BinOp And;
    (* Load the first half from local variable *)
    WI_LocalGet idx_tmp;
    (* Push 8 *)
    WI_Const 8;
    (* fst >> 8 *)
    WI_BinOp Shr_u;
    (* Push mask for 0xFF00 *)
    WI_Const 0xFF00;
    (* (fst >> 8) & 0xFF00 *)
    WI_BinOp And;
    (* Combine the two parts *)
    WI_BinOp Or;
    (* === Load the second value *)
    WI_LocalGet idx_addr;
    (* Push 4 *)
    WI_Const 4;
    (* 2*addr + 4 *)
    WI_BinOp Add;
    (* Load from memory - label doesn't matter *)
    WI_Load Secret;
    (* Store the second half in a local variable (tee_local idx_snd) *)
    WI_LocalSet idx_tmp;
    WI_LocalGet idx_tmp;
    (* Push 16 *)
    WI_Const 16;
    (* snd << 16 *)
    WI_BinOp Shl;
    (* Push mask for 0xFF0000 *)
    WI_Const 0xFF0000;
    (* (snd << 16) & 0xFF0000 *)
    WI_BinOp And;
    (* Load the second half from local variable *)
    WI_LocalGet idx_tmp;
    (* Push 8 *)
    WI_Const 8;
    (* snd << 8 *)
    WI_BinOp Shl;
    (* Push mask for 0xFF000000 *)
    WI_Const 0xFF000000;
    (* (snd << 8) & 0xFF000000 *)
    WI_BinOp And;
    (* Combine the two parts *)
    WI_BinOp Or;
    (* === Combine the first and second part results *)
    WI_BinOp Or;
  ]

(* Improved version of translate_store that has better cache locality
 * e.g.
 * (i32.const i) (i32.const c) i32.store L ~~>
 * (i32.const 2*i) (i32.const ((c & 0xFF) | ((c << 8) & 0xFF0000))) i32.store
 * (i32.const (2*i + 4)) (i32.const (((c >> 16) & 0xFF) | ((c >> 8) & 0xFF0000))) i32.store
 *
 * Effectively, we store the bytes w/ labels in the following way:
 * Address	  Original Value	New Value
 * addr	      0xDD	          0xDD
 * addr + 1	  0xCC	          0x00 or 0x01 if secret
 * addr + 2	  0xBB	          0xCC
 * addr + 3	  0xAA	          0x00/0x01
 * addr + 4	  (not used)	    0xBB
 * addr + 5	  (not used)	    0x00/0x01
 * addr + 6	  (not used)	    0xAA
 * addr + 7	  (not used)	    0x00/0x01
 *)
let translate_store_interleaved (c : context) (lbl : SimpleLattice.t) :
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
          (* Push 1 *)
          WI_Const 1;
          (* 2*addr *)
          WI_BinOp Shl;
          (* save 2*addr *)
          WI_LocalSet idx_addr;
        ]
        @ push_store_interleaved idx_val idx_addr lbl ) )

let translate_store (c : context) (lbl : SimpleLattice.t) :
    context * wasm_instruction =
  (* We extend the list of locals with two extra items,
         for saving the value to be stored and address to
         stored into *)
  let encoded_lbl = SimpleLattice.encode lbl in
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
        ]
        @ push_bitmask0 c
        @ [
            (* Top of the stack: 01111111 where 0 is at index mem_size (from the right) *)
            (* Next element    : addr *)
            (* Force addres into lower part of memory *)
            WI_BinOp And;
            (* Get value *)
            WI_LocalGet idx_val;
            (* Store value - label doesn't matter *)
            WI_Store Secret;
            (* === BEGIN STORE LABEL *)
            WI_LocalGet idx_addr;
          ]
        @ push_bitmask1 c
        @ [
            (* Top of the stack: 1000000 where 1 is at index mem_size (from the right) *)
            (* Next element    : addr *)
            (* Force address into upper part of memory *)
            WI_BinOp Or;
            (* Push label on stack *)
            WI_Const encoded_lbl;
            (* Store it - label doesn't matter *)
            WI_Store Secret;
          ] ) )

let translate_load_public (c : context) : context * wasm_instruction =
  (* We extend the list of locals with two extra items,
         for saving the value to be stored and address to
         stored into *)
  let idx_addr = List.length c.locals in
  let new_ctxt =
    {
      c with
      locals = (* labels don't matter *)
               c.locals @ [ { t = I32; lbl = Secret } ];
    }
  in
  ( new_ctxt,
    WI_Block
      (* labels don't matter *)
      ( BlockType ([ { t = I32; lbl = Secret } ], [ { t = I32; lbl = Secret } ]),
        [
          (* save address *)
          WI_LocalSet idx_addr;
          (* === BEGIN CHECK LABEL*)
          WI_Block
            ( BlockType ([], []),
              (* push address and 100000 *)
              (WI_LocalGet idx_addr :: push_bitmask1 c)
              @ [
                  (* Top of the stack: 1000000 where 1 is at index mem_size (from the right) *)
                  (* Next element    : addr *)
                  (* Force address into upper part of memory *)
                  WI_BinOp Or;
                  (* Load labels from memory (4 bytes, i.e. 4 labels) - label doesn't matter*)
                  WI_Load Secret;
                  (* Assert that all labels are 0 *)
                  WI_Const 0;
                  WI_BinOp Eq;
                  (* branch conditionally to the end of the block*)
                  WI_BrIf 0;
                  (* attempt to load secret into public value, trap! *)
                  WI_Unreachable;
                ] );
        ]
        (* === BEGIN LOAD VALUE *)
        @ (WI_LocalGet idx_addr :: push_bitmask0 c)
        @ [
            (* Top of the stack: 01111111 where 0 is at index mem_size (from the right) *)
            (* Next element    : addr *)
            (* Force addres into lower part of memory *)
            WI_BinOp And;
            (* load value - label doesn't matter *)
            WI_Load Secret;
          ] ) )

let translate_load_secret (c : context) : context * wasm_instruction =
  ( c,
    WI_Block
      (* labels don't matter *)
      ( BlockType ([ { t = I32; lbl = Secret } ], [ { t = I32; lbl = Secret } ]),
        (* addr is on the stack, force it down in lower half *)
        push_bitmask0 c
        @ [
            (* Top of the stack: 01111111 where 0 is at index mem_size (from the right) *)
            (* Next element    : addr *)
            (* Force addres into lower part of memory *)
            WI_BinOp And;
            (* Load labels from memory (4 bytes, i.e. 4 labels) - label doesn't matter*)
            WI_Load Secret;
          ] ) )

let translate_load_public_interleaved (c : context) : context * wasm_instruction
    =
  (* We extend the list of locals with two extra items,
         for saving the address to load from and the temparary fisrt/second half values *)
  let idx_tmp = List.length c.locals in
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
      (* labels don't matter *)
      ( BlockType ([ { t = I32; lbl = Secret } ], [ { t = I32; lbl = Secret } ]),
        [
          (* Push 1 *)
          WI_Const 1;
          (* 2*addr *)
          WI_BinOp Shl;
          (* save 2*addr *)
          WI_LocalSet idx_addr;
          (* === BEGIN CHECK LABEL*)
          WI_Block
            ( BlockType ([], []),
              [
                WI_Block
                  ( BlockType ([], []),
                    [
                      (* (fst & 0xFF00FF00) *)
                      WI_LocalGet idx_addr;
                      WI_Load Secret;
                      WI_Const 0x01000100;
                      WI_BinOp And;
                      WI_BrIf 0;
                      WI_LocalGet idx_addr;
                      WI_Const 4;
                      WI_BinOp Add;
                      WI_Load Secret;
                      WI_Const 0x01000100;
                      WI_BinOp And;
                      WI_BrIf 0;
                      WI_Br 1;
                    ] );
                WI_Unreachable;
              ] );
        ]
        @ push_load_interleaved idx_addr idx_tmp ) )

let translate_load_secret_interleaved (c : context) : context * wasm_instruction
    =
  (* We extend the list of locals with two extra items,
         for saving the address to load from and the temparary fisrt/second half values *)
  let idx_tmp = List.length c.locals in
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
      (* labels don't matter *)
      ( BlockType ([ { t = I32; lbl = Secret } ], [ { t = I32; lbl = Secret } ]),
        [
          (* Push 1 *)
          WI_Const 1;
          (* 2*addr *)
          WI_BinOp Shl;
          (* save 2*addr *)
          WI_LocalSet idx_addr;
        ]
        @ push_load_interleaved idx_addr idx_tmp ) )

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

and transform_instr (c : context) (i : wasm_instruction) :
    context * wasm_instruction =
  match i with
  | WI_Load l -> (
      match l with
      | Public -> translate_load_public_interleaved c
      | Secret -> translate_load_secret_interleaved c)
  | WI_Store l -> translate_store_interleaved c l
  | WI_Block (bt, instr) ->
      let c', instr' = transform_seq c instr in
      (c', WI_Block (bt, instr'))
  | WI_Loop (bt, instr) ->
      let c', instr' = transform_seq c instr in
      (c', WI_Loop (bt, instr'))
  | _ -> (c, i)

let transform_func (m : wasm_memory) (f : wasm_func) : wasm_func =
  let params = match f.ftype with FunType (st_in, _, _) -> st_in in
  let ctxt = { locals = params @ f.locals; memory = m } in
  (* transform the body of f*)
  let ctxt', new_body = transform_seq ctxt f.body in
  { f with body = new_body; locals = ctxt'.locals }

let transform_module (m : wasm_module) : wasm_module =
  let rec f x acc =
    if x <= acc then acc else match x with 0 -> 0 | _ -> f x (2 * acc)
  in
  match m.memory with
  (* if module doesn't use a memory it doesn't typecheck *)
  | None -> m
  | Some mem ->
      (* Make sure the memory is a multiple of 2, for bitmasking operation to actually split the memory *)
      let nearest_power_of_two = f mem.size 1 in
      {
        m with
        memory = Some { size = nearest_power_of_two * 2 };
        functions =
          List.map (transform_func { size = nearest_power_of_two }) m.functions;
      }
