open Javalib_pack
open Sawja_pack

open Cfg
open Dom

module IR = JBirSSA

let phi_uses (phi : IR.phi_node) = phi.use
let phi_def (phi : IR.phi_node) = phi.def

(* Given a BirSSA program, build the blocks of the cfg *)
let blocks_separation ssa_prog =
  (* A block is maximal if it cannot be joined with its predecessor *)
  let is_maximal block =
    let first = List.hd block.instrs in
    let preds = (IR.preds ssa_prog).(first) in
    if (Array.length preds != 1)
    then true
    else (preds.(0) == -1)
  in
  (* Non-maximal block have not been join to their predecessor's block *)
  let non_maximal_blocks = ref [] in
  let maximal_blocks = ref [] in
  (* Collect initial blocks *)
  let id = ref 0 in
  let collect pc =
    let is_cond =  match (IR.code ssa_prog).(pc) with
      | IR.Ifd _ -> true
      | _ -> false
    in
    let b = (new_block !id pc is_cond false) in
    incr id;
    if is_cond then begin
        let b' = (new_block !id pc true true) in
        incr id;
        maximal_blocks := b :: !maximal_blocks;
        maximal_blocks := b' :: !maximal_blocks
      end
    else begin
        if is_maximal b
        then maximal_blocks := b :: !maximal_blocks
        else non_maximal_blocks := b :: !non_maximal_blocks
      end
  in
  Array.iteri (fun i _ -> collect i) (IR.code ssa_prog);
  (* Fuse blocks with their predecessor block *)
  let is_pred_block pred pc b =
    if List.mem pred b.instrs
    then match (IR.code ssa_prog).(pred) with
      | IR.Ifd (_, target) -> ((target == pc) == b.assume_is_negation)
      | _ -> true
    else false
  in
  while !non_maximal_blocks != [] do
    let b = List.hd !non_maximal_blocks in
    non_maximal_blocks := List.tl !non_maximal_blocks;
    let first = List.hd b.instrs in
    let pred = (IR.preds ssa_prog).(first).(0) in
    let pred_max_block =
      List.find_opt
        (is_pred_block pred (List.hd b.instrs))
        !maximal_blocks
    in
    match pred_max_block with
      | None -> begin
          let pred_non_max_block =
            List.find_opt
              (is_pred_block pred (List.hd b.instrs))
              !non_maximal_blocks
          in
          match pred_non_max_block with
            | None -> ()
            | Some m -> begin
                non_maximal_blocks := List.filter (fun b' -> b'.id != m.id) !non_maximal_blocks;
                non_maximal_blocks := (block_fusion m b) :: !non_maximal_blocks
              end
        end
      | Some m -> begin
          maximal_blocks := List.filter (fun b' -> b'.id != m.id) !maximal_blocks;
          maximal_blocks := (block_fusion m b) :: !maximal_blocks
        end;
  done;
  List.mapi (fun i b -> block_index b i) !maximal_blocks

let to_blocks ssa_prog =
	(* Fill informations (defs, use, etc) *)
	(* Succ / Pred *)
	let blocks = Array.of_list (blocks_separation ssa_prog) in
  let block_to_pred =
    Array.map
      (fun b ->
        let pred_instrs = (IR.preds ssa_prog).(List.hd b.instrs) in
				Array.of_list (List.flatten (Array.to_list (Array.map
					(fun pred_instr ->
						List.filter_map (fun b' ->
							if List.mem pred_instr b'.instrs
							then match (IR.code ssa_prog).(pred_instr) with
                | IR.Ifd (_, target) ->
                  if ((target == (List.hd b.instrs)) == b'.assume_is_negation) 
                  then Some b'.id else None
                | _ -> Some b'.id
							else None)
							(Array.to_list blocks)
					)
					pred_instrs)))
        )
      blocks
  in
	(* An array where a.(i) is the succ block of block i *)
	let block_to_succ = Array.make (Array.length blocks) [] in
	Array.iteri
		(fun i preds ->
			Array.iter
				(fun pred -> block_to_succ.(pred) <- i :: block_to_succ.(pred)) 
				preds
		)
		block_to_pred;
	let fill_info block =
		(* Use def*)
		let defs = ref MixVarSet.empty in
		let uses = ref MixVarSet.empty in
		let rec add_use_expr = function
			| IR.Var (_, x) -> begin
				(if not (MixVarSet.mem (IR.var_name x) !defs)
				then uses := MixVarSet.add (IR.var_name x) !uses)
        end
			| IR.Unop (_, e) -> add_use_expr e
			| IR.Binop (_, e1, e2) -> (add_use_expr e1; add_use_expr e2)
			| IR.Field (e, _, _) -> (add_use_expr e)
			| _ -> ()
		in
		let add_use_check = function
			| IR.CheckNullPointer e -> add_use_expr e
			| IR.CheckArrayBound (e1, e2) -> (add_use_expr e1; add_use_expr e2)
			| IR.CheckArrayStore (e1, e2) -> (add_use_expr e1; add_use_expr e2)
			| IR.CheckNegativeArraySize e -> add_use_expr e
			| IR.CheckCast (e, _) -> add_use_expr e
			| IR.CheckArithmetic e -> add_use_expr e
			| _ -> ()
		in
		let def_use_assume pc =
			match (IR.code ssa_prog).(pc) with
				| IR.Ifd ((_, e1, e2), _) -> (
					add_use_expr e1;
					add_use_expr e2
				)
				| _ -> ()
		in
		let def_use i = match i with
			| IR.AffectVar (x, e) -> (
				defs := MixVarSet.add (IR.var_name x) !defs;
				add_use_expr e
			)
			| IR.AffectArray (x, idx, e) -> (
				add_use_expr x;
				add_use_expr idx;
				add_use_expr e
			)
			| IR.AffectField (x, _, _, e) -> (
				add_use_expr x;
				add_use_expr e
			)
			| IR.Ifd _ -> ()
			| IR.Throw e -> add_use_expr e
			| IR.Return (Some e) -> add_use_expr e
			| IR.New (x, _, _, e_list) -> (
				defs := MixVarSet.add (IR.var_name x) !defs;
				List.iter add_use_expr e_list
			)
			| IR.InvokeStatic (None, _, _, e_list) -> List.iter add_use_expr e_list
			| IR.InvokeStatic (Some x, _, _, e_list) -> (
				defs := MixVarSet.add (IR.var_name x) !defs;
        List.iter add_use_expr e_list
      )
			| IR.InvokeNonVirtual (Some x, e , _, _, e_list)
			| IR.InvokeVirtual (Some x, e , _, _, e_list) -> (
				defs := MixVarSet.add (IR.var_name x) !defs;
				List.iter add_use_expr (e :: e_list)
			)
			| IR.InvokeNonVirtual (None, e , _, _, e_list) 
			| IR.InvokeVirtual (None, e , _, _, e_list) ->
				List.iter add_use_expr (e :: e_list)
			| IR.MonitorEnter e -> add_use_expr e
			| IR.MonitorExit e -> add_use_expr e
			| IR.Check c -> add_use_check c
			| _ -> ()
		in
    let first = List.hd block.instrs in
		def_use_assume first;
    List.iter (fun i -> def_use (IR.code ssa_prog).(i)) block.instrs;
		blocks.(block.id) <- block_update block !defs !uses;
		(* Phis from pred *)
		Array.iter
			(fun b ->
				let all_phi_nodes = (IR.phi_nodes ssa_prog).(List.hd b.instrs)
				in
				let all_defs = List.fold_right
					(fun node defs ->
						MixVarSet.add (IR.var_name (phi_def node)) defs)
					all_phi_nodes
					MixVarSet.empty
				in
				blocks.(b.id) <- block_update_pred_phi b all_defs
			)
			blocks;
		(* Phis from last *)
		Array.iter
			(fun b ->
        let last = List.hd (List.rev b.instrs) in 
				let firsts_succ =
					List.map (fun succ -> List.hd blocks.(succ).instrs) block_to_succ.(b.id)
				in
				let all_phis = List.flatten (List.map
					(fun first -> List.flatten
						(List.map
							(fun node -> List.flatten (List.mapi
								(fun i u ->
									if (IR.preds ssa_prog).(first).(i) == last
									then [(IR.var_name (phi_def node), IR.var_name u)]
									else []
								)
								(Array.to_list (phi_uses node)))
							)
							(IR.phi_nodes ssa_prog).(first)
						)
					)
          (List.sort_uniq compare firsts_succ))
				in
				blocks.(b.id) <- block_update_phi b all_phis
			)
			blocks;
    
	in
	Array.iter fill_info blocks;
	(blocks, block_to_succ, block_to_pred)

let to_graph ssa_prog = 
	(* Blockify *)
	let (blocks, succ_map, pred_map) = to_blocks ssa_prog in

  let succ_array_set = Array.map PointSet.of_list succ_map in
  let pred_array_set = Array.map (fun a -> PointSet.of_seq (Array.to_seq a)) pred_map in

  (* Program points *)
  (* Add an entry and exit point to each blocks *)
  let entry_points = Array.mapi (fun i -> fun _ -> 2*i) blocks in
  let exit_points  = Array.mapi (fun i -> fun _ -> 2*i + 1) blocks in

  let merge a b b' =
    let shared = min b.id b'.id in
    let old = max b.id b'.id in
    a.(old) <- a.(shared)
  in
  let merge_entry_if b b' =
    if PointSet.equal pred_array_set.(b.id) pred_array_set.(b'.id)
    then merge entry_points b b'
  in
  Array.iter (fun b -> Array.iter (merge_entry_if b) blocks) blocks;
  let merge_exit_if b b' =
    if PointSet.equal succ_array_set.(b.id) succ_array_set.(b'.id)
    then merge exit_points b b'
  in
  Array.iter (fun b -> Array.iter (merge_exit_if b) blocks) blocks;

  let merge_exit_entry exit_block entry_block =
    exit_points.(exit_block) <- entry_points.(entry_block)
  in
  Array.iter
    (fun b -> List.iter (merge_exit_entry b.id) succ_map.(b.id))
    blocks;

	(* Dom graph *)
  let program_points =
    List.sort_uniq compare
      ((Array.to_list entry_points) @ (Array.to_list exit_points) )
  in

  let old_pp_new_pp = Array.make (2 * (Array.length blocks)) (-1) in
  List.iteri (fun i pp -> old_pp_new_pp.(pp) <- i) program_points;

	let nodes =
    List.map (fun pp -> string_of_int old_pp_new_pp.(pp)) program_points
  in

  let new_entry_points = Array.map (fun e -> old_pp_new_pp.(e)) entry_points in
  let new_exit_points  = Array.map (fun e -> old_pp_new_pp.(e)) exit_points in

  let association = Array.make (List.length program_points) [] in
  Array.iter
    (fun b ->
      let entry = new_entry_points.(b.id) in
      association.(entry) <- new_exit_points.(b.id) :: association.(entry)
    )
    blocks;

  let edges = Array.to_list (Array.mapi 
    (fun i b -> (string_of_int i, List.map string_of_int b))
    association)
  in

	let g = create_graph nodes edges in

	let dom = immediate_dominator 
		(Array.length g.name) 
		g.succ
		g.pred
		(Dict.find "0" g.index) in
  (blocks, pred_map, dom, new_entry_points, new_exit_points, List.length program_points)

let to_fic (ssa_time, ssa_prog) =
  let (blocks, pred_map, dom, entry_points, exit_points, nb_pp) = to_graph ssa_prog in

  let pp_to_pred' = Array.make (Array.length dom) [] in
  Array.iteri (fun id_b -> fun pp -> pp_to_pred'.(pp) <- id_b :: pp_to_pred'.(pp)) exit_points;
  let pp_to_pred = Array.map (List.sort_uniq compare) pp_to_pred' in

	(* Iterations *)
	let block_to_check = ref (List.map (fun b -> b.id) (List.rev (Array.to_list blocks))) in

	(* Count variables *)
	let vars_function l =
		List.flatten (List.map
			(fun (u, v) -> [u; v])
			l
		)
	in
	let vars = List.flatten (Array.to_list (Array.map
		(fun b -> (vars_function b.sigmas) @ (MixVarSet.elements b.defs) @(MixVarSet.elements b.uses) @ (vars_function b.phis)
		)
		blocks
	))
	in
	let unique_vars = List.fold_right (fun v s -> MixVarSet.add v s) vars MixVarSet.empty in

  let get_source m =
    let def =
      List.find_map
        (fun b ->
          List.find_map
            (fun (u, v, _) ->
              if (u = m) then Some v else None
            )
            b.copies
        )
        (Array.to_list blocks)
    in match def with
    | None -> m
    | Some v -> v
  in

  let get_common u p =
    (* Get the potential copies of each predecessors *)
    let phis_copies = 
      List.map
        (fun id_b'' ->
          let copy =
            List.find_opt
              (fun (_, x, _) -> x = u)
              blocks.(id_b'').copies
          in
          match copy with
          | None -> None
          | Some (x, y, _) -> 
            List.find_map
              (fun (z, w) -> if (x = w) then Some z else None)
              blocks.(id_b'').phis
        )
        pp_to_pred.(p)
    in
    let version =
      List.fold_left
        (fun acc vers ->
          match (acc, vers) with
            | (_, None) -> None
            | (None, _) -> None
            | (Some v, Some u') -> if u' = v then Some v else None)
        (List.hd phis_copies)
        phis_copies
    in match version with
    | Some u' -> (u', [])
    | None -> begin
      let u' = u ^ "fresh" ^ (string_of_int p) in
      List.iter
        (fun id_b'' ->
          let u'' = u ^ "local" ^ (string_of_int id_b'') in
          blocks.(id_b'') <- block_add_copy_phi blocks.(id_b'') (u'', u, u) (u', u'')
        )
        pp_to_pred.(p);
      (u', pp_to_pred.(p))
    end
  in

  let get_copy u p =
    if List.length pp_to_pred.(p) > 1
    then get_common u p
    else let id_b = List.hd pp_to_pred.(p) in
      let def = List.find_opt
        (fun (_, y, _) -> u = y)
        blocks.(id_b).copies
      in
      match def with
      | Some (u', _, _) -> (u', [])
      | None -> begin
          let u' = u ^ "fresh" ^ (string_of_int id_b) in
          blocks.(id_b) <- block_add_copy blocks.(id_b) (u', u, u);
          (u', [id_b])
        end
  in

  let add_missing_vars p id_b' =
    let defs_at_p =
      List.fold_left
      (fun acc id_b -> MixVarSet.union (abs_all_defs blocks.(id_b)) acc)
      MixVarSet.empty
      pp_to_pred.(p)
    in
    let uses_b' = block_ext_uses blocks.(id_b') in
    let missings = MixVarSet.diff uses_b' defs_at_p in
    MixVarSet.fold
      (fun m acc ->
        let u = get_source m in
        let (u', modified) = get_copy u p in
        blocks.(id_b') <- block_use_replace blocks.(id_b') m u';
        (modified @ acc)
      )
      missings
      []
  in

  let rec check_point p id_b' =
    if p < 0 then [] else
      if List.length pp_to_pred.(p) > 1
      then (* joining point *)
        if List.exists
            (fun id_pred ->
              not (MixVarSet.is_empty (MixVarSet.inter
                (abs_all_defs blocks.(id_pred))
                (block_ext_uses blocks.(id_b'))))
            )
            pp_to_pred.(p)
        then add_missing_vars p id_b'
        else check_point dom.(p) id_b'
      else if List.length pp_to_pred.(p) = 1
      then let id_b = List.hd pp_to_pred.(p) in
        if (blocks.(id_b).contains_conditional
          || MixVarSet.subset
              (block_ext_uses blocks.(id_b'))
              (abs_all_defs blocks.(id_b)))
        then add_missing_vars p id_b'
        else check_point dom.(p) id_b'
    else []
  in

  let block_dom = Array.make_matrix nb_pp nb_pp false in
  let rec mark_dom p id_dom =
    if id_dom > 0
    then (
      block_dom.(id_dom).(p) <- true;
      mark_dom p dom.(id_dom)
    )
  in
  List.iter (fun b -> mark_dom entry_points.(b) entry_points.(b)) !block_to_check;

  let blocks_compare b1 b2 =
    if b1 = b2
    then 0
    else
    let e1 = entry_points.(b1) in
    let ex1 = exit_points.(b1) in
    let e2 = entry_points.(b2) in
    let ex2 = exit_points.(b2) in
    if block_dom.(ex1).(e2)
    then
      (if block_dom.(ex2).(e1)
      then b1 - b2
      else 1)
    else 
      (if block_dom.(ex2).(e1)
      then -1
      else b1 - b2)
  in

  let l = 10 * (List.length !block_to_check) in
	let limit = ref l in
  let block_checked = Array.make (List.length !block_to_check) 0 in
  let t = Sys.time () in
	while !block_to_check <> [] && (!limit > 0) do
	begin
		decr limit;
    (* TODO: select the lowest *)
    let b' = (List.hd !block_to_check) in
    block_checked.(b') <- block_checked.(b') + 1;
		let modified = check_point entry_points.(b') b' in
		block_to_check := List.tl !block_to_check;
    block_to_check := List.sort_uniq blocks_compare (modified @ !block_to_check)
	end
	done;
  let iter_time = Sys.time() -. t in
  Array.iteri
    (fun i cpt ->
      if cpt > 3
      then Printf.printf "\nReselect the same block %d %d times !! \n" i cpt)
    block_checked;

	(* Count variables *)
	let varsSSI = List.flatten (Array.to_list (Array.map
		(fun b -> (vars_function b.sigmas) @ (MixVarSet.elements b.defs) @(MixVarSet.elements b.uses) @ (vars_function b.phis)
		)
		blocks
	))
	in
	let unique_varsSSI = List.fold_right (fun v s -> MixVarSet.add v s) varsSSI MixVarSet.empty in
	Printf.printf "Done\n";
	
	let joining_points = Array.fold_right
		(fun b acc ->
			if (Array.length (IR.preds ssa_prog).(List.hd b.instrs)) > 1
			then acc + 1 else acc
		)
		blocks
		0
	in

  let all_vars = List.map snd (Javalib_pack.Ptmap.elements (IR.vars ssa_prog)) in
  let orig_vars = List.map (fun x -> IR.var_name (IR.var_origin x)) all_vars in
  let data_file = open_out_gen [Open_append] 0 "results.csv" in
  let nb_ori_var = MixVarSet.cardinal (MixVarSet.of_list orig_vars) in
  let nb_fic_var = MixVarSet.cardinal unique_varsSSI in
  let nb_ssa_var = (MixVarSet.cardinal unique_vars) in
  output_string data_file (
  (string_of_float (Unix.time ())) ^ " ; " ^
  (string_of_int joining_points) ^ " ; " ^
  (string_of_int (Array.length blocks)) ^ " ; " ^
  (string_of_int nb_pp) ^ " ; " ^
  (string_of_int nb_ssa_var) ^ " ; " ^
  (string_of_int nb_fic_var) ^ " ; " ^ 
  (string_of_int (nb_fic_var * nb_pp)) ^ " ; " ^ 
  (string_of_int nb_ori_var) ^ " ; " ^
  (string_of_int (nb_ori_var * nb_pp)) ^ " ; " ^ 
  (string_of_int (nb_ori_var * joining_points)) ^ " ; " ^
  (if !limit > 0 then "Finished" else "Interrupted") ^
  "; " ^
  (string_of_float ssa_time) ^ " ; " ^
  (string_of_float iter_time) ^ " ; " ^
  (string_of_float (log ssa_time)) ^ " ; " ^
  (string_of_float (log iter_time)) ^ " ; ");
  close_out data_file

let transform ?(bcv=false) ?(ch_link=false) (cm : JCode.jcode Javalib.concrete_method) c =
  let t' = Sys.time () in
  let res = IR.transform ~bcv:bcv ~ch_link:ch_link  cm c in
  let t = Sys.time () -. t' in
  (t, res)

let run filename = 
  Javalib.iter
    (fun j_iorc ->
      try
      let ssa_prog =
            Javalib.map_interface_or_class_context
        (transform ~bcv:true)
        j_iorc
      in
      Javalib.cm_iter
        (fun cm ->
          let (_, signature) = JBasics.cms_split cm.cm_class_method_signature in
          Printf.printf "Function %s  " (JBasics.ms_name signature);
          let t' = Sys.time () in
          ignore(Javalib.map_concrete_method ~force:true to_fic cm);
          let time = Sys.time() -. t' in
          let data_file = open_out_gen [Open_append] 0 "results.csv" in
          output_string data_file (
          (string_of_float time) ^ " ; " ^
          (JBasics.ms_name signature) ^ " \n");
          close_out data_file)
        ssa_prog
      with IR.Subroutine -> 
        Printf.printf "Subroutine found in %s\n"
          (Javalib.JPrint.class_name (Javalib.get_name j_iorc)))
    filename


let _ =
  let data_file = open_out_gen [Open_append ; Open_creat] 666 "results.csv" in

  output_string data_file (
    " Exp time ; " ^
    " Joining points ; " ^
    " Blocks ; " ^
    " Program points ; " ^
    " SSA variables ; " ^
    " FIC variables ; " ^ 
    " FI invariant size ; " ^ 
    " Origin variables ; " ^
    " FS size ; " ^
    " Sparse FS size ; " ^
    " Execution completed ; " ^
    " SSA transformation ; " ^
    " FIC transformation ; " ^
    " Log(SSA time) ; " ^
    " Log(FIC time) ; " ^
    " Total transformation ; " ^
    " Function name\n");

  close_out data_file;
   if not !Sys.interactive then (
     let target = ref "" in
     Arg.parse [] (fun s -> target := s) "usage: while option prog";
     run !target
   )
