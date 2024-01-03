open Types
(*
   An implementation of the Generic Join algorithm, that will answer queries of the form
   Q(x_1, ..., x_k) :- R_1(X_1), ..., R_n(X_n)
*)

(*
   We should have a function converting type of queries to tries
*)

(*
   Relations module
   A relation is essentially a list of (k, v) pairs.
   The canonical representation of a relation is a trie, with the k's ordered according to some relation
   Relations controls how to create relations, and how to do search/substitutions.
*)

(* Convert query to conjuctive query form
   *)
module Compile : sig
  type t = Symbol.t * string list [@@deriving show]

  val compile : Symbol.t Query.t -> string list * t list
  val get_all_vars : string list * t list -> string list
end = struct
  let curv = ref 0

  let fresh () =
    curv := !curv + 1;
    "x" ^ string_of_int (!curv - 1)

  let reset () = curv := 0

  (* Var of string | Fun of Symbol.t * t list *)

  (* TODO: Don't optimize constants yet? Or at all? *)
  type t = Symbol.t * string list [@@deriving show]

  let rec aux : Symbol.t Query.t -> string * t list = function
    | V x -> (x, [])
    | Q (f, ps) ->
        let vs, atoms = List.map aux ps |> List.split in
        let v = fresh () in
        (v, (f, v :: vs) :: List.concat atoms)

  module StringSet = Set.Make (String)

  let rec get_vars : Symbol.t Query.t -> StringSet.t = function
    | V x -> StringSet.singleton x
    | Q (_, ps) ->
        List.fold_right StringSet.union (List.map get_vars ps) StringSet.empty

  let compile q =
    reset ();
    let root, atoms = aux q in
    let vars =
      StringSet.union (StringSet.singleton root) (get_vars q)
      |> StringSet.to_list
    in
    (vars, atoms)

  let get_all_vars (vs, ps) =
    let open StringSet in
    union (vs |> of_list)
      (List.fold_right union (List.map (fun (_, ls) -> ls |> of_list) ps) empty)
    |> to_list

  let%test "compiles" =
    let test_t = Alcotest.of_pp pp in
    let test_c = Alcotest.(pair (list string) (list test_t)) in
    (* let q = Query.of_sexp [%s f "?a" (g "?a")] in *)
    (* let q = Query.of_sexp [%s (f 1 (g "?a"))] in *)
    let q = Query.of_sexp Symbol.intern [%s f (g "?a") (h "?a")] in
    (* let q = Query.of_sexp Symbol.intern [%s "?a"] in *)
    Alcotest.(check test_c) "prints f(?a, g(?a))" ([], []) (compile q)
end

module Trie = struct
  type ('k, 'v) t = Node of 'k * ('v, ('k, 'v) t) Hashtbl.t | Nil

  (* insert assumes the entry lines up with structure of the trie. *)
  let rec insert (r : ('k * 'v) list) (root : ('k, 'v) t) : unit =
    match r with
    | [] -> ()
    | (k, v) :: rest -> (
        match root with
        | Nil -> failwith "impossible"
        | Node (k', branches) ->
            if k = k' then
              let root' =
                match Hashtbl.find_opt branches v with
                | None ->
                    let n =
                      match rest with
                      | [] -> Nil
                      | (k'', _) :: _ -> Node (k'', Hashtbl.create 1)
                    in
                    Hashtbl.add branches v n;
                    n
                | Some n -> n
              in
              insert rest root'
            else insert r root)

  let trywalk k v n =
    match n with
    | Nil -> None
    | Node (k', branches) ->
        if k = k' then Hashtbl.find_opt branches v else Some n

  let count_branches k = function
    | Nil -> None
    | Node (k', branches) ->
        if k = k' then Some (Hashtbl.length branches) else None
end

module Join = struct
  (* Represents a single query. Has
      - Function for converting a Compile.t to
     - Constructed by giving the relations, patterns
  *)
  type k = string
  type substitution = (k * eclass_id) list
  type trie = (k, eclass_id) Trie.t

  type t = {
    pat_ordering : k -> k -> int;
    patterns : k list;
    to_id : Term.t -> eclass_id;
    relations : (Compile.t * trie) list;
  }

  let make to_id pat_ordering patterns queries : t = {
    pat_ordering;
    patterns;
    to_id;
    relations = failwith "TODO"
  }

  (* Assumes fs and pat are the same length *)
  let add_to_trie (ordering : k -> k -> int) (fs : eclass_id list) pat trie =
    let exception Invalid in
    let table = Hashtbl.create (List.length fs) in
    try
      List.iter
        (fun (id, p) ->
          match Hashtbl.find_opt table p with
          | None -> Hashtbl.add table p id
          | Some id' -> if id = id' then () else raise Invalid)
        (List.combine fs pat);
      let r =
        Hashtbl.to_seq table |> List.of_seq
        |> List.sort (fun (k, _) (k', _) -> ordering k k')
      in
      Trie.insert r trie
    with Invalid -> ()

  (* Loop over all relations and insert if symbols match *)
  let add_to_relations self (f, fs) =
    List.iter
      (fun ((f', pat), trie) ->
        if f = f' then add_to_trie self.pat_ordering fs pat trie)
      self.relations

  (*
  let add_to_relations_sexp self e = add_to_relations self (Term.of_sexp self.to_id e)
  *)

  let argmin f =
    let lt a b =
      match (a, b) with
      | Some x, Some y -> x < y
      | Some _, None -> true
      | None, _ -> false
    in
    let rec go (min, arg) = function
      | [] -> arg
      | x :: xs ->
          let y = f x in
          if lt y min then go (y, x) xs else go (min, arg) xs
    in
    function [] -> None | x :: xs -> Some (go (f x, x) xs)

  let get_substitutions var relations =
    let min_node = argmin (Trie.count_branches var) relations in
    match min_node with
    | None | Some Nil ->
        failwith
          "Variable does not appear in any relation, (query not range \
           restricted)"
    | Some (Node (_, branches)) ->
        let ( let* ) x f = Option.bind x f in
        let new_relations v =
          let* relations' =
            List.fold_right
              (fun r cur ->
                let* cur' = cur in
                let* r' = Trie.trywalk var v r in
                Some (r' :: cur'))
              relations (Some [])
          in
          Some (v, relations')
        in
        let vs = Hashtbl.to_seq_keys branches |> List.of_seq in
        List.filter_map new_relations vs

  let generic_join self : substitution list =
    let rec go relations current_sub = function
      | [] -> [ current_sub ]
      | var :: vars' ->
          List.concat
            (List.map
               (fun (v, relations') ->
                 go relations' ((var, v) :: current_sub) vars')
               (get_substitutions var relations))
    in
    go (List.map snd self.relations) [] self.patterns
end

module type RELATION' = sig
  type k
  type v
  type t

  val ordering : k -> k -> int

  type xx = int array

  val create : (k, v) Hashtbl.t list -> t
  val add_to_relation : (k, v) Hashtbl.t list -> t -> t
  val get_substitutions : k -> t list -> (v * t list) list
end

module type RELATION = sig
  type k
  type v
  type t

  val ordering : k -> k -> int
  val create : (k, v) Hashtbl.t list -> t
  val add_to_relation : (k, v) Hashtbl.t list -> t -> t
  val get_substitutions : k -> t list -> (v * t list) list
end

module type REL = sig
  type k
  type v

  val ordering : k -> k -> int
end

(* TODO: should use a map instead of a hashtable?
   Typically the key will be ints, so not sure which is better. *)
module TrieRelation (Rel : REL) : RELATION = struct
  include Rel

  type t = Node of k * (v, t) Hashtbl.t | Nil

  (* Assuming all elements of ls have the same bindings. After sorting the list (of variables), recursively partition/insert them *)
  let create = function
    | [] -> Nil
    | l :: ls ->
        let ks =
          List.sort_uniq ordering (Hashtbl.to_seq_keys l |> List.of_seq)
        in
        let partition var entries =
          let table = Hashtbl.create 5 in
          List.iter
            (fun e ->
              let v = Hashtbl.find e var in
              match Hashtbl.find_opt table v with
              | None -> Hashtbl.add table v []
              | Some prev -> Hashtbl.replace table v (e :: prev))
            entries;
          table
        in
        let rec go entries = function
          | [] -> Nil
          | var :: vars ->
              let partitioned = partition var entries in
              let subtries =
                partitioned |> Hashtbl.to_seq
                |> Seq.map (fun (k, entries') -> (k, go entries' vars))
                |> Hashtbl.of_seq
              in
              Node (var, subtries)
        in
        go (l :: ls) ks

  let add_to_relation _ _ = failwith ""

  let trywalk x v n =
    match n with
    | Nil -> None
    | Node (x', branches) ->
        if x = x' then Hashtbl.find_opt branches v else Some n

  let count_branches x' n =
    match n with
    | Nil -> None
    | Node (x, branches) ->
        if x = x' then Some (Hashtbl.length branches) else None

  let argmin f =
    let lt a b =
      match (a, b) with
      | Some x, Some y -> x < y
      | Some _, None -> true
      | None, _ -> false
    in
    let rec go (min, arg) = function
      | [] -> arg
      | x :: xs ->
          let y = f x in
          if lt y min then go (y, x) xs else go (min, arg) xs
    in
    function [] -> None | x :: xs -> Some (go (f x, x) xs)

  let get_substitutions var relations =
    let min_node = argmin (count_branches var) relations in
    match min_node with
    | None | Some Nil ->
        failwith
          "Variable does not appear in any relation, (query not range \
           restricted)"
    | Some (Node (_, branches)) ->
        let ( let* ) x f = Option.bind x f in
        let new_relations v =
          let* relations' =
            List.fold_right
              (fun r cur ->
                let* cur' = cur in
                let* r' = trywalk var v r in
                Some (r' :: cur'))
              relations (Some [])
          in
          Some (v, relations')
        in
        let vs = Hashtbl.to_seq_keys branches |> List.of_seq in
        List.filter_map new_relations vs
end

(*
   Abstract types: depends on k and v
   Relations must be ordered the same way
   Operations on relations:
   - Add to trie
   - Get list of substitutions after substituting 
   - Given x, get list of possible v's, along with new relations after substituting [x -> v]

   Maybe internal to generic join?
*)

(* Our typical example will be k = String, v = Id.t (int) *)
(* This implementation is incorect, sort of (the type of keys in the trie are the patterns themselves)*)
module GenericJoin (Rel : RELATION) = struct
  type k = Rel.k
  type v = Rel.v
  type substitution = (k * v) list

  let generic_join (vars : k list) (relations : Rel.t list) : substitution list
      =
    let rec go relations current_sub = function
      | [] -> [ current_sub ]
      | var :: vars' ->
          List.concat
            (List.map
               (fun (v, relations') ->
                 go relations' ((var, v) :: current_sub) vars')
               (Rel.get_substitutions var relations))
    in
    go relations [] vars
end

module BasicRel : REL = struct
  type k = int
  type v = int

  let ordering = Int.compare
end

module BasicTrieRelation = TrieRelation (BasicRel)
module BasicGenericJoin = GenericJoin (BasicTrieRelation)

(*
module StringMap = Map.Make (String)

type trie = Node of string * trie StringMap.t
(*
   trie nodes stores variable of current level in relation,
   as well as a with edges to next level, substituting a value for the current variable
*)

(*
   We assume that all relation tries are ordered according to vars (can skip vars too)   
*)

let trywalk x v (Node (x', branches) as n) =
  if String.equal x x' then StringMap.find_opt v branches else Some n

let count_branches x' (Node (x, branches)) =
  if String.equal x x' then Some (StringMap.cardinal branches) else None

let argmin f =
  let lt a b =
    match (a, b) with
    | Some x, Some y -> x < y
    | Some _, None -> true
    | None, _ -> false
  in
  let rec go (min, arg) = function
    | [] -> arg
    | x :: xs ->
        let y = f x in
        if lt y min then go (y, x) xs else go (min, arg) xs
  in
  function [] -> None | x :: xs -> Some (go (f x, x) xs)

let rec genericJoin (vars : string list) (relations : trie list)
    (sub : string StringMap.t) : string StringMap.t list =
  match vars with
  | [] -> [ sub ]
  | x :: vars' -> (
      let min_node = argmin (count_branches x) relations in
      match min_node with
      (* This means x doesn't appear at all in any of the relations. Throw an exception? *)
      | None -> failwith "Query not range restricted"
      | Some (Node (_, branches)) ->
          let ( let* ) x f = Option.bind x f in
          (* Really wish I had mapM right now... *)
          let newRelations v =
            List.fold_right
              (* (fun r cur -> cur >>= (fun cur' -> trywalk x v r >>= fun r' -> Some(r' :: cur'))) *)
                (fun r cur ->
                let* cur' = cur in
                let* r' = trywalk x v r in
                Some (r' :: cur'))
              relations (Some [])
          in
          let addSubstitution v =
            let* relations' = newRelations v in
            Some (genericJoin vars' relations' (StringMap.add x v sub))
          in
          let vs =
            List.map (function a, _ -> a) (StringMap.bindings branches)
          in
          List.concat (List.filter_map addSubstitution vs))

(* TODO: test just this join code on a simple example...
   Should make it generic over any kind of trie...
   A trie has a generic type k (e.g., the type of pattern variables) that represents the current "level" in the trie,
   and a generic type v (e.g., the type of e-class ids) that represent the things that the patterns are substituted for
   Substitution is a map (k -> v), so k should have a map instance. v should be hashable (Hashtbl.t is polymorphic)
*)

(* TODO: Turn an egraph/query into a relation (represented by a trie) *)
*)
