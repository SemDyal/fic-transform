
(** [add v t w] adds integer [v] to the list in [t.(w)] *)
let add v t w =
  t.(w) <- v :: t.(w)

(* We follow 'A Fast Algorithm for Finding Dominators in a Flowgraph'
   by Lengauer and Tarjan *)
(* nodes are in [0..n-1] *)
(* [succ] maps nodes to successors *)
(* [pred] maps nodes to predecessors *)
(* [r] is an entry point in [0 .. n-1] *)
(* returns idom where, idom.(w) is the immediate dominator of w. *)
let immediate_dominator (n:int) (succ:int list array) (pred:int list array) (r:int) =
  let semi = Array.make n (-1) in
  let vertex = Array.make n (-1) in
  let label = Array.make n (-1) in
  let dom = Array.make n (-1) in
  let ancestor = Array.make n (-1) in
  let parent = Array.make n (-1) in
  let bucket = Array.make n [] in
  let nb_dfs = ref 0 in
  let nb_dead = ref 0 in
  let rec dfs v =
    semi.(v) <- !nb_dfs;
    vertex.(!nb_dfs) <- v;
    label.(v) <- v;
    incr nb_dfs;
    List.iter
      (fun w -> 
	 if semi.(w) = -1 then 
	   begin
	     parent.(w) <- v;
	     dfs w
	   end)
      succ.(v) in
  let rec compress v =
    if not (ancestor.(ancestor.(v)) = -1) then
      begin
	compress ancestor.(v);
	if semi.(label.(ancestor.(v))) < semi.(label.(v)) then
	  label.(v) <- label.(ancestor.(v));
	ancestor.(v) <- ancestor.(ancestor.(v))
      end in 
  let eval v =
    if ancestor.(v) = -1 then v
    else begin
      compress v;
      label.(v)
    end in 
  let link v w = ancestor.(w) <- v in
    dfs r;
    Array.iteri
      (fun i w -> if (w = -1) then incr nb_dead)
      semi;
    for i= !nb_dfs-1 downto 1 do 
      let w = vertex.(i) in
	List.iter 
	  (fun v -> 
	     if semi.(v) >=0 then
	       let u = eval v in 
		 if semi.(u) < semi.(w) then semi.(w) <- semi.(u))
	  pred.(w);
	add w bucket vertex.(semi.(w));
	link parent.(w) w;
	List.iter 
	  (fun v ->
	     let u = eval v in
	       dom.(v) <- if semi.(u) < semi.(v) then u else parent.(w))
	    bucket.(parent.(w));
	bucket.(parent.(w)) <- []
 done;
 for i=1 to !nb_dfs-1 do
   let w = vertex.(i) in
     if w>=0 && not (dom.(w) = vertex.(semi.(w))) then
       dom.(w) <- dom.(dom.(w))
 done;
 dom (* , (fun i -> semi.(i)<0), vertex) *)

module Dict = Map.Make(struct type t = string let compare = compare end)

type string_graph = {
  name: string array;
  index: int Dict.t;
  succ: int list array;
  pred: int list array;
}

let create_dict l =
  let idx = ref (-1) in
  let nth = Array.make (List.length l) "" in
  let dict =
    List.fold_left (fun dict s -> 
		      incr idx; 
		      nth.(!idx) <- s; 
		      Dict.add s !idx dict) Dict.empty l in
    (dict,nth)

let create_graph nodes edges =
  let (dict,nth) = create_dict nodes in
  let n = List.length nodes in
  let pred = Array.make n [] in
  let succ = Array.make n [] in
  List.iter
    (fun (s,succs) ->
      let s_idx = Dict.find s dict in 
      List.iter 
        (fun s_succ ->
          let succ_idx = Dict.find s_succ dict in
          succ.(s_idx) <- succ_idx :: succ.(s_idx);
	  pred.(succ_idx) <- s_idx :: pred.(succ_idx))
	succs)
    edges;
  { name = nth;
    index = dict;
    succ;
    pred }