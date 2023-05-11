
type value_type = I32

(* This is equivalent to tau in the paper (typing judgements) *)
type 'a labeled_value_type = 
  {t: value_type; lbl: 'a}

type stack_type = value_type list
type fun_type = FunType of stack_type * stack_type
type global_type = GlobalType of value_type

type binop = Add | Eq 

type wasm_instruction = 
  | WI_Unreachable                              (* trap unconditionally *)
  | WI_Nop                                      (* do nothing *)
  | WI_Drop                                     (* drop value *)

  | WI_Const of int32                             (* constant *)
  | WI_BinOp of binop                             (* binary numeric operator *)

  | WI_Call of int32                              (* call function *)

  | WI_LocalGet of int32                          (* read local variable *)
  | WI_LocalSet of int32                          (* write local variable *)
  | WI_GlobalGet of int32                         (* read global variable *)
  | WI_GlobalSet of int32                         (* write global variable *)

  | WI_Load                                       (* read memory at address *)
  | WI_Store                                      (* write memory at address *)

  | WI_If of wasm_instruction list * wasm_instruction list
  

type wasm_global = {
  gtype : value_type;
  const : wasm_instruction list;
}

type wasm_func = {
  ftype : fun_type;
  locals : value_type list;
  body : wasm_instruction list;
  export_name : string option;                  (* export name, should start with '$' *)
}

type wasm_module = {
  globals : wasm_global list;
  functions : wasm_func list;
}

(************************* EXAMPLE ************************************)

let example_module: wasm_module = {
  globals = [];
  functions = [
    {
      ftype = FunType ([I32; I32], []);
      locals = [I32];
      body = [
        WI_Nop; 
        WI_LocalGet 0l; 
        WI_LocalGet 1l; 
        WI_BinOp Add; 
        WI_Const 0l; 
        WI_BinOp Eq; 
        WI_If (
          [WI_Nop; WI_Const 2l; WI_LocalSet 0l],
          [WI_Const 42l; WI_LocalSet 0l])
      ];
      export_name = Some "$hello"
    }
  ]
}


(************************* PRETTY PRINTING ************************************)

let pp_type (t : value_type) =
  match t with
  | I32 -> "i32"

let nl = "\n"

let pp_binop (bop : binop) =
  match bop with 
  | Add -> "i32.add"
  | Eq -> "i32.eq"

let rec pp_instruction (indent : int) (instr : wasm_instruction) =
  let pp_instructions (indent' : int) (instructions : wasm_instruction list) =
    List.fold_left (fun _s i -> _s ^ (pp_instruction indent' i) ^ nl) "" instructions in

  let rec spaces (n : int) =
    match n with
    | 0 -> ""
    | _ -> " " ^ (spaces (n-1)) in

  spaces indent ^
  (match instr with 
  | WI_Unreachable        -> "unreachable"
  | WI_Nop                -> "nop"
  | WI_Const v            -> "i32.const " ^ Int32.to_string v
  | WI_BinOp op           -> pp_binop op
  | WI_Call idx           -> "call " ^ (Int32.to_string idx)
  | WI_Drop               -> "drop"

  | WI_LocalGet idx       -> "local.get " ^ (Int32.to_string idx)
  | WI_LocalSet idx       -> "local.set " ^ (Int32.to_string idx)
  | WI_GlobalGet idx      -> "global.get " ^ (Int32.to_string idx)
  | WI_GlobalSet idx      -> "global.set " ^ (Int32.to_string idx)

  | WI_Load               -> "i32.load"
  | WI_Store              -> "i32.store"

  | WI_If (b1, b2)    -> "if" ^ nl ^
                            pp_instructions (indent + 2) b1 ^ nl ^ (spaces indent) ^
                         "else" ^ nl ^
                            pp_instructions (indent + 2) b2 ^ nl ^ (spaces indent) ^
                         "end" ^ nl
  )

let pp_function (f : wasm_func) =
  let ps = match f.ftype with
           | FunType (plist, _) -> plist in

  let locals = if List.length f.locals > 0
               then " (local" ^ (List.fold_left (fun _s l -> " " ^ pp_type l ^ _s) "" f.locals) ^ ")"
               else ""

  and params = if List.length ps > 0
               then (" (param" ^ (List.fold_left (fun _s l -> " " ^ pp_type l ^ _s) "" ps) ^ ")")
               else ""

  and result = match f.ftype with
               | FunType (_, [res]) -> " (result " ^ (pp_type res) ^ ")"
               | _ -> ""

  and export = match f.export_name with
               | Some name -> " (export \"" ^ name ^ "\")"
               | None -> ""

  and body = List.fold_left (fun _s i -> _s ^ nl ^ (pp_instruction 2 i)) "" f.body
  in "(func" ^ export ^ params ^ result ^ nl ^ locals ^ nl
  ^ body ^ nl
  ^ ")"

let pp_module (m : wasm_module) = 
  "(module" ^ nl
  ^ (List.fold_left (fun _s f -> _s ^ nl ^ (pp_function f)) "" m.functions)
  ^ nl ^ ")"