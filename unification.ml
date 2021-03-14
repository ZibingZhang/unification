(* https://link.springer.com/chapter/10.1007/978-3-030-24986-1_48 *)

type term =
  | TConst of int
  | TVar of string
  | TCons of string * term list

type node =
  | NConst of int * int ref * string list ref * node option ref
  | NVar of string * int ref * string list ref * node option ref
  | NCons of string * node list * int ref * string list ref * node option ref

type subst = (string * node) list
;;

let rec node_to_string (s : node) =
  match s with
    | NConst(n, _, _, _) -> Printf.sprintf "%d" n
    | NVar(l, _, _, _) -> Printf.sprintf "%s" l
    | NCons(s, l, _, _, _) ->
      Printf.sprintf "%s(%s)"
        s (String.concat ", " (List.map node_to_string l))

let rec subst_to_string (o : subst) =
  match o with
    | [] -> ""
    | (s, t)::r ->
      Printf.sprintf "%s -> %s\n%s"
        s (node_to_string t) (subst_to_string r)
;;

let rec unify (s : term) (t : term) : subst =
  let rec term_to_node (s : term) =
    let s_class = ref None in
    let node = begin match s with
      | TVar(s) -> NVar(s, (ref 1), (ref [s]), s_class)
      | TConst(n) -> NConst(n, (ref 1), (ref []), s_class)
      | TCons(s, l) -> NCons(s, List.map term_to_node l, (ref 1), (ref []), s_class)
    end in
      s_class := Some node;
      node in
  let s_node = term_to_node s in
  let t_node = term_to_node t in
    unif_closure s_node t_node;
    find_solution s_node []

and unif_closure (s : node) (t : node) =
  (* not sure what is meant by the same node *)
  match s, t with
    | NCons(n1, l1, _, _, _), NCons(n2, l2, _, _, _) ->
      if not (String.equal n1 n2)
      then failwith "Cannot unify cons of different names."
      else if not (List.length l1 = List.length l2)
      then failwith "Unequal length of arguments."
      else union s t; List.iter (fun (a1, a2) -> unif_closure a1 a2) (List.combine l1 l2)
    (* constants must be the same *)
    | NConst(n1, _, _, _), NConst(n2, _, _, _) ->
      if n1 != n2
      then failwith "Constants clash."
      else ()
    | NConst(_), NCons(_) -> failwith "Cannot unify constant with cons."
    | NCons(_), NConst(_) -> failwith "Cannot unify cons with constant."
    | _ -> union s t

and union (s : node) (t : node) =
  let s_size, s_vars, s_class = extract_mutable s in
  let t_size, t_vars, t_class = extract_mutable t in
  match s, t with
    | NVar(_), _ ->
      t_size := !t_size + !s_size;
      t_vars := !t_vars @ !s_vars;
      s_class := Some t;
      ()
    | _ ->
      s_size := !s_size + !t_size;
      s_vars := !s_vars @ !t_vars;
      t_class := Some s;
      ()

and find_solution (s : node) (o : subst) =
  let s_size, s_vars, s_class = extract_mutable s in
  let t =
    begin match !s_class with
      | None -> failwith "impossible state"
      | Some t -> t
    end in
  let t_size, t_vars, t_class = extract_mutable t in
  let o =
    begin match t with
      | NCons(_, args, _, _, _) ->
        let rec find_solution_args (l : node list) (o : subst) =
          begin match l with
            | [] -> o
            | a::r -> (find_solution_args r (find_solution a o))
          end in
          find_solution_args args o
      | _ -> o
    end in 
  let rec add_vars (vars : string list) (o : subst) =
    begin match vars with
      | [] -> o
      | a::r ->
        if begin match t with
          | NVar(s, _, _, _) -> s != a
          | _ -> true
        end then (a, t)::(add_vars r o)
        else add_vars r o
    end in
      add_vars !t_vars o

and extract_mutable (s : node) =
  match s with
    | NConst(_, size, vars, cls) -> size, vars, cls
    | NVar(_, size, vars, cls) -> size, vars, cls
    | NCons(_, _, size, vars, cls) -> size, vars, cls
;;

let first (a, r) = a
let second (a, r) = r
;;

let s = TVar("x")
let t = TCons("f", [TVar("y")])
;;

print_string (subst_to_string (unify t s))