(* https://link.springer.com/chapter/10.1007/978-3-030-24986-1_48 *)

(**
 * IDEA : use a flag to detect cycles during creating of the substitution. 
 *)

;; (* ========== Data Types ========== *)

(**
 * Terms exist for ease of manually constructing data.
 * When unification occurs, all terms get translated into nodes.
 * TVars of the same name are represented by the same node.
 *)
type term =
  | TConst of int
  | TVar of string
  | TCons of string * term list

type node =
  (* value * size * vars * class *)
  | NConst of int * int ref * string list ref * node option ref
  (* name * size * vars * class *)
  | NVar of string * int ref * string list ref * node option ref
  (* name * args * size * vars * class *)
  | NCons of string * node list * int ref * string list ref * node option ref

type subst = (string * node) list

type 'a envt = (string * 'a) list

;; (* ========== to_string Functions ========== *)

let rec node_to_string (s : node) =
  match s with
    | NConst(n, _, _, _) -> Printf.sprintf "%d" n
    | NVar(l, _, _, _) -> Printf.sprintf "%s" l
    | NCons(s, l, _, _, _) ->
      Printf.sprintf "%s(%s)"
        s (String.concat ", " (List.map node_to_string l))

let rec subst_to_string (o : subst) =
  match o with
    | [] -> "\n"
    | (s, t)::r ->
      Printf.sprintf "%s -> %s\n%s"
        s (node_to_string t) (subst_to_string r)

let rec node_envt_to_string (e : node envt) =
  match e with
    | [] -> "\n"
    | (k, v)::r ->
      Printf.sprintf "%s -> %s\n%s"
        k (node_to_string v) (node_envt_to_string r)

;; (* ========== Environment Functions ========== *)

let rec find (s : string) (env : 'a envt) =
  match env with
    | [] -> None
    | (k, v)::r ->
      if String.equal s k
      then Some v
      else find s r

;; (* ========== Term->Node Setup Functions ========== *)

let rec term_to_node (s : term) (env : node envt) =
  let s_class = ref None in
  let node, env = begin match s with
    | TVar(s) ->
        begin match find s env with
          | None ->
            let node = NVar(s, (ref 1), (ref [s]), s_class) in
            let env = (s, node)::env in 
              node, env
          | Some(node) ->
              node, env
        end
    | TConst(n) ->
        NConst(n, (ref 1), (ref []), s_class), env
    | TCons(s, l) -> 
      let args, env = over_args l env [] in
        NCons(s, args, (ref 1), (ref []), s_class), env
  end in
    s_class := Some node;
    node, env

and over_args (l : term list) (env : node envt) (acc : node list) =
  match l with
    | [] -> List.rev acc, env
    | a::r ->
      let node, env = term_to_node a env in
        over_args r env (node::acc)

;; (* ========== Unification Functions ========== *)

let rec unify (s : term) (t : term) : subst =
  let s_node, env = term_to_node s [] in
  let t_node, _ = term_to_node t env in
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
      s_class := Some t
    | _ ->
      s_size := !s_size + !t_size;
      s_vars := !s_vars @ !t_vars;
      t_class := Some s

and find_solution (s : node) (o : subst) =
  let s_size, s_vars, s_class = extract_mutable s in
  let t =
    begin match !s_class with
      | None -> failwith "Impossible state."
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

;; (* ========== Term Examples ========== *)

let s = TVar("x")
let t = TCons("f", [TVar("x")])

let p = TCons("A", [TCons("B", [TVar("v"); TCons("C", [TVar("u"); TVar("v")])])])
let q = TCons("A", [TCons("B", [TVar("w"); TCons("C", [TVar("w"); TCons("D", [TVar("x"); TVar("y")])])])])

;; (* ========== Unification Examples ========== *)

print_string (subst_to_string (unify t t))
