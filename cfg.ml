
module MixVarSet = Set.Make(String)
module PointSet = Set.Make(Int)

type block = {
	(* Pred info *)
	pred_phi_defs: MixVarSet.t;

	(* Sigmas *)
	sigmas: (string * string) list;

	(* Body *)
	uses: MixVarSet.t;
	defs: MixVarSet.t;
	instrs: int list;

	(* Copies *)
	copies: (string * string * string) list;

	(* Phi *)
	phis: (string * string) list;

	id: int;
	contains_conditional: bool;
  assume_is_negation: bool;
}

let new_block id first cond neg = {
		pred_phi_defs =  MixVarSet.empty;
		sigmas = [];
		uses = MixVarSet.empty;
		defs = MixVarSet.empty;
		instrs = [first];
    copies = [];
		phis = [];
		id = id;
		contains_conditional = cond;
    assume_is_negation = neg;
	}

let block_fusion b b' = { b with instrs = b.instrs @ b'.instrs }

let block_index b new_id = { b with id = new_id }

let block_add_instr b instr = { b with instrs = instr :: b.instrs }

let block_update b def use = { b with uses = use; defs = def }

let block_update_pred_phi b pred = { b with pred_phi_defs = pred }

let block_update_phi b phi = { b with phis = phi }

let block_add_copy_phi b copy phi =
  { b with copies = copy :: b.copies; phis = phi :: b.phis }

let block_add_copy b copy = { b with copies = copy :: b.copies }

let block_use_replace b u u' = { b with 
		sigmas = List.map
      (fun (x, y) -> if y = u then (x, u') else (x, y))
      b.sigmas;
		uses = MixVarSet.add u' (MixVarSet.remove u b.uses);
    copies = List.map
      (fun (x, y, z) -> if z = u then (x, y, u') else (x, y, z))
      b.copies;
		phis = List.map
      (fun (x, y) -> if y = u then (x, u') else (x, y))
      b.phis
}

(*let abs_all_uses block =
  let from_sigmas = MixVarSet.of_list (List.map snd block.sigmas) in
  let from_copies = MixVarSet.of_list (List.map (fun (_,_,u) -> u) block.copies) in
  let from_phis = MixVarSet.of_list (List.map snd block.phis) in
  MixVarSet.union (MixVarSet.union block.uses from_sigmas) (MixVarSet.union from_copies from_phis)*)

let block_ext_uses b =
  let used_in_phis = MixVarSet.of_list (List.map snd b.phis) in
  let (def_in_copies', used_in_copies') =
    List.split (List.map (fun (d,_,u) -> (d, u)) b.copies)
  in
  let def_in_copies = MixVarSet.of_list def_in_copies' in
  let used_in_copies = MixVarSet.of_list used_in_copies' in
  let real_before_copies =
    MixVarSet.union used_in_copies (MixVarSet.diff used_in_phis def_in_copies)
  in
  let real_before_body =
    MixVarSet.union b.uses (MixVarSet.diff real_before_copies b.defs)
  in
  let (def_in_sigmas', used_in_sigma') = List.split b.sigmas in
  let def_in_sigmas = MixVarSet.of_list def_in_sigmas' in
  let used_in_sigma = MixVarSet.of_list used_in_sigma' in
  MixVarSet.union used_in_sigma (MixVarSet.diff real_before_body def_in_sigmas)



let abs_all_defs block =
  let from_sigmas = MixVarSet.of_list (List.map fst block.sigmas) in
  let from_copies = MixVarSet.of_list (List.map (fun (d,_,_) -> d) block.copies) in
  let from_phis = MixVarSet.of_list (List.map fst block.phis) in
  MixVarSet.union (MixVarSet.union block.defs from_sigmas) (MixVarSet.union from_copies from_phis)

let ext_defs b = MixVarSet.diff (abs_all_defs b) (block_ext_uses b) (*TODO : repalce with real liveness *)

let block_string b = 
	let print_var_list l =
		MixVarSet.fold (fun x s -> s ^ "  " ^ x) l ""
	in
	let print_functions l =
		List.fold_right (^) (List.map (fun (u,v) -> "[" ^ u ^ " <- " ^ v ^ "]") l) "" 
	in
	let print_copies l =
		List.fold_right (^) (List.map (fun (u,v,w) -> "[" ^ u ^ " <- " ^ v ^ " -- " ^ w ^ "]") l) "" 
	in
  [ "+-------";
  "| Block " ^ (string_of_int b.id);
  "| " ^ (List.fold_left (fun acc -> fun i -> acc ^ (string_of_int i) ^ " ") "" b.instrs);
  if b.contains_conditional
  then "| Conditional " ^ (if b.assume_is_negation then "Neg" else "Aff")
  else "| ";
  "|  Phi-defs in predecessors : " ^ print_var_list b.pred_phi_defs;
  "|  Copies: " ^ print_copies b.copies;
  "|  Defs:" ^ print_var_list b.defs;
  "|  Uses:" ^ print_var_list b.uses;
  "|  Phis: " ^ print_functions b.phis;
  "+-------";
  "|  All defs: " ^ print_var_list (abs_all_defs b);
  "|  External uses:" ^ print_var_list (block_ext_uses b);
  "+-------"]