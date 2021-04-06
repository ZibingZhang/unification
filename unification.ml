;; (* ========== Resources ========== *)
(* https://link.springer.com/chapter/10.1007/978-3-030-24986-1_48 *)
(* https://dl.acm.org/doi/pdf/10.1145/357162.357169?casa_token=SEFEG_LBSOwAAAAA:eRfG5zFc7pJi7chayqwzuc3FtjeyJKbE5xbCp4mop7giKyHfpT-loehd8kyoLwKH5CAh-6dJMwCQ7A *)

;; (* ========== Data Definitions ========== *)

(**
 * Terms exist for ease of manually constructing data.
 * When unification occurs, all terms are translated into nodes.
 *)

type term =
  | TConst of int
  | TVar of string
  | TCons of string * term list

type node =
  (* name * class * visited *)
  | NVar of string * cls option ref * bool ref
  (* name * args * class * visited *)
  | NCons of string * node list * cls option ref * bool ref
and cls =
  (* rep * nodes * size * vars *)
  | Class of node ref * node list ref * int ref * string list ref

type 'a envt = (string * 'a) list

type subst = node envt

;; (* ========== Helper Functions ========== *)

let get_cls_ref (s : node) : cls option ref =
  match s with
    | NVar(_, cls, _) -> cls
    | NCons(_, _, cls, _) -> cls

let get_cls (s : node) : cls =
  let maybe_cls = get_cls_ref s in
    match !maybe_cls with
      | None -> failwith "Impossible state."
      | Some(c) -> c

let set_class (s : node) (c : cls) : unit =
  let c_ref = get_cls_ref s in
    c_ref := Some c

let get_rep (s : node) : node =
  let Class(rep, _, _, _) = get_cls s in !rep

let has_visited (s : node) : bool =
  let v = match s with
    | NVar(_, _, v) -> v
    | NCons(_, _, _, v) -> v in 
  !v

let flag_visited (s : node) : unit =
  let v = match s with
    | NVar(_, _, v) -> v
    | NCons(_, _, _, v) -> v in 
  v := true

let unflag_visited (s : node) : unit =
  let v = match s with
    | NVar(_, _, v) -> v
    | NCons(_, _, _, v) -> v in
  v := false

;; (* ========== to_string Functions ========== *)

let rec node_to_string (s : node) : string =
  match s with
    | NVar(l, _, _) -> Printf.sprintf "%s" l
    | NCons(s, l, _, _) ->
      match l with
        | [] -> Printf.sprintf "%s" s
        | _ -> Printf.sprintf "%s(%s)" s (String.concat ", " (List.map node_to_string l))

let rec subst_to_string (o : subst) : string =
  match o with
    | [] -> ""
    | (s, t)::r ->
      Printf.sprintf "%s -> %s\n%s"
        s (node_to_string t) (subst_to_string r)

;; (* ========== Environment Functions ========== *)

let rec find (s : string) (env : 'a envt) : 'a option =
  match env with
    | [] -> None
    | (k, v)::r ->
      if String.equal s k
        then Some v
        else find s r

let contains (s : string) (env : 'a envt) : bool =
  match find s env with
    | None -> false
    | Some(_) -> true

;; (* ========== Term->Node Setup Functions ========== *)

let rec term_to_node (s : term) (env : node envt) : node * node envt =
  let rec map_over_args (l : term list) (env : node envt) (acc : node list): node list * node envt =
    begin match l with
      | [] -> List.rev acc, env
      | a::r ->
        let node, env = term_to_node a env in
          map_over_args r env (node::acc)
      end in
  let s_class = ref None in
  let node, vars, env = begin match s with
    | TVar(s) ->
        begin match find s env with
          | None ->
            let node = NVar(s, s_class, ref false) in
            let env = (s, node)::env in 
              node, (ref [s]), env
          | Some(node) ->
              node, (ref [s]), env
        end
    | TConst(n) ->
        NCons(string_of_int n, [], s_class, ref false), (ref []), env
    | TCons(s, l) -> 
      let args, env = map_over_args l env [] in
        NCons(s, args, s_class, ref false), (ref []), env
  end in
    s_class := Some (Class ((ref node), (ref [node]), (ref 1), vars));
    node, env

;; (* ========== Unification Functions ========== *)

let rec unify (s : term) (t : term) : subst =
  let s_node, env = term_to_node s [] in
  let t_node, _ = term_to_node t env in
    unif_closure s_node t_node;
    find_solution s_node

and unif_closure (s : node) (t : node) : unit =
  if s == t then () else
  let s_rep = get_rep s in
  let t_rep = get_rep t in
  begin match s_rep, t_rep with
    | NCons(n1, l1, _, _), NCons(n2, l2, _, _) ->
      if not (String.equal n1 n2)
        then failwith (Printf.sprintf "Cannot unify cons of different names, %s %s." n1 n2)
      else if not (List.length l1 = List.length l2)
        then failwith "Unequal length of arguments."
      else ()
    | _ -> ()
  end;
  match s, t with
    | NCons(n1, l1, _, _), NCons(n2, l2, _, _) ->
      if not (String.equal n1 n2)
        then failwith (Printf.sprintf "Cannot unify cons of different names, %s %s." n1 n2)
      else if not (List.length l1 = List.length l2)
        then failwith "Unequal length of arguments."
      else
        union s t; List.iter (fun (a1, a2) -> unif_closure a1 a2) (List.combine l1 l2)
    | _ -> union s t

and union (s : node) (t : node) : unit =
  let rec add_nodes (nodes : node list) (nodes_ref : node list ref) (c : cls) : unit =
    begin match nodes with
      | [] -> ()
      | a::r ->
        nodes_ref := a::(!nodes_ref);
        set_class a c;
        add_nodes r nodes_ref c
    end in 
  let combine_classes (s : cls) (t : cls) : unit =
    let Class(s_rep_ref, s_nodes_ref, s_size_ref, s_vars_ref) = s in
    let Class(t_rep_ref, t_nodes_ref, t_size_ref, t_vars_ref) = t in
    let t_size = !t_size_ref in
    let s_size = !s_size_ref in
      (* optimization based on size of classes *)
      if s_size < t_size then
        (t_size_ref := !t_size_ref + !s_size_ref;
        t_vars_ref := !t_vars_ref @ !s_vars_ref;
        add_nodes !s_nodes_ref t_nodes_ref t)
      else
        (s_size_ref := !t_size_ref + !s_size_ref;
        s_vars_ref := !t_vars_ref @ !s_vars_ref;
        add_nodes !t_nodes_ref s_nodes_ref s;
        s_rep_ref := !t_rep_ref)
      in
  (* combine s into t *)
  let combine (s : node) (t : node) : unit =
    let s_class = get_cls s in
    let t_class = get_cls t in
      combine_classes s_class t_class;
      set_class s (get_cls t) in
  match s with
    | NVar(_) -> combine s t
    | _ -> combine t s

and  find_solution (s : node) : subst =
  let rec add_vars (vars : string list) (s : node) (o : subst) : subst =
    begin match vars with
      | [] -> o
      | a::r ->
        if not (contains a o) && begin match s with
          (* prevents x -> x *)
          | NVar(s, _, _) -> s != a
          | _ -> true
        end
          then (a, s)::(add_vars r s o)
          else add_vars r s o
    end in
  let rec find_solution_args (l : node list) (o : subst) : subst =
    begin match l with
      | [] -> o
      | a::r -> (find_solution_args r (find_solution_help a o))
    end 
  and find_solution_help (s : node) (o : subst) : subst =
    if has_visited s then failwith "Cycle detected." else flag_visited s;
    let s_class = get_cls s in
    let Class(rep, _, _, vars) = s_class in
    let t = !rep in
    let o =
      begin match t with
        | NCons(_, args, _, _) -> find_solution_args args o
        | _ -> o
      end in
    let result = add_vars !vars t o in
      unflag_visited s;
      result in
  find_solution_help s []

;; (* ========== Term Examples ========== *)

(* x <=> f(x) *)
let s = TVar("x")
let t = TCons("f", [TVar("x")])

(* A(B(v), C(u, v)) <=> A(B(w), C(w, D(x, y))) *)
let p = TCons("A", [TCons("B", [TVar("v"); TCons("C", [TVar("u"); TVar("v")])])])
let q = TCons("A", [TCons("B", [TVar("w"); TCons("C", [TVar("w"); TCons("D", [TVar("x"); TVar("y")])])])])

(* f(x, x) <=> f(x, x) *)
let a = TCons("f", [TVar("x"); TVar("x")])
let b = TCons("f", [TVar("x"); TVar("x")])

(* x <=> f(g(f())) *)
let c = TVar("x")
let d = TCons("f", [TCons("g", [TCons("f", [])])])

(* f(x, 2) <=> f(1, x) *)
let e = TCons("f", [TVar("x"); TConst(2)])
let f = TCons("f", [TConst(1); TVar("x")])

(* f(x, x) <=> f(1, 2) *)
let g = TCons("f", [TVar("x"); TVar("x")])
let h = TCons("f", [TConst(1); TConst(2)])

(* TODO: Martelli and Montanari examples  *)

;; (* ========== Unification Examples ========== *)

print_string (subst_to_string (unify s t))
