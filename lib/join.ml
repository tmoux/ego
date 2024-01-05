open Types
open Language

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

module Compile = struct
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

  let rec get_vars : Symbol.t Query.t -> StringSet.t = function
    | V x -> StringSet.singleton x
    | Q (_, ps) ->
        List.fold_right StringSet.union (List.map get_vars ps) StringSet.empty

  let get_all_vars ps =
    let open StringSet in
    List.fold_right union (List.map (fun (_, ls) -> ls |> of_list) ps) empty
    |> to_list

  let compile q =
    reset ();
    let root, atoms = aux q in
    let vars = get_all_vars atoms in
    let pattern_vars = get_vars q in
    (vars, atoms, (root, pattern_vars))

  let of_sexp = Query.of_sexp Symbol.intern

  (*
  let%test "compiles" =
    let test_t = Alcotest.of_pp pp in
    let test_c = Alcotest.(pair (list string) (list test_t)) in
    (* let q = Query.of_sexp [%s f "?a" (g "?a")] in *)
    (* let q = Query.of_sexp [%s (f 1 (g "?a"))] in *)
    let q = Query.of_sexp Symbol.intern [%s f (g "?a") (h "?a")] in
    (* let q = Query.of_sexp Symbol.intern [%s "?a"] in *)
    Alcotest.(check test_c) "prints f(?a, g(?a))" ([], []) (compile q)
    *)
end

module Hashtbl = struct
  include Hashtbl

  let pp pp_key pp_value ppf values =
    Hashtbl.iter
      (fun key data ->
        Format.fprintf ppf "@[<1>%a: %a@]@." pp_key key pp_value data)
      values
end

module Trie = struct
  type ('k, 'v) t = Node of 'k * ('v, ('k, 'v) t) Hashtbl.t | Nil
  [@@deriving show]

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
            else assert false)
  (* else insert r root) *)

  let trywalk k v = function
    | Node (k', branches) when k = k' -> Hashtbl.find_opt branches v
    | n -> Some n

  let count_branches k = function
    | Nil -> None
    | Node (k', branches) ->
        if k = k' then Some (Hashtbl.length branches) else None

  let initial k = Node (k, Hashtbl.create 1)
end

module GenericJoin = struct
  (* Represents a single query. Has
      - Function for converting a Compile.t to
     - Constructed by giving the relations, patterns
  *)
  type k = string

  let pp_k = Fmt.string
  let pp_eclass_id = Fmt.int


  type substitution' = eclass_id * eclass_id StringMap.t
  type substitution = (k * eclass_id) list [@@deriving show]
  type trie = (k, eclass_id) Trie.t

  type t = {
    pat_ordering : k -> k -> int;
    patterns : k list;
    root_pattern : k * StringSet.t;
    to_id : Term.t -> eclass_id;
    relations : (Compile.t * trie) list;
  }

  let make to_id pat_ordering patterns root_pattern queries : t =
    {
      pat_ordering;
      patterns;
      root_pattern;
      to_id;
      relations =
        List.map
          (fun (f, ps) ->
            (* TODO: We can find min in O(|ps|) instead of sorting *)
            ( (f, ps),
              match List.sort pat_ordering ps with
              | [] -> Trie.Nil
              | p :: _ -> Trie.initial p ))
          queries;
    }

  (* Assumes fs and pat are the same length *)
  let add_to_trie (ordering : k -> k -> int) (fs : eclass_id list) pat trie =
    let exception Invalid in
    let table = Hashtbl.create (List.length fs) in
    try
      (* print_int (List.length fs);
         print_int (List.length pat); *)
      assert (List.length fs = List.length pat);
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
      Fmt.pr "%a\n" pp_substitution r;
      Trie.insert r trie
    with Invalid -> ()

  (* Loop over all relations and insert if symbols match *)
  let add_to_relations self (f, fs) =
    let root_id = self.to_id (f, fs) in
    List.iter
      (fun ((f', pat), trie) ->
        if Symbol.intern f = f' then
          add_to_trie self.pat_ordering (root_id :: fs) pat trie)
      self.relations

  let rec add_to_relations_sexp self e =
    (match e with
    | Sexplib.Sexp.List (_ :: rest) ->
        List.iter (add_to_relations_sexp self) rest
    | _ -> ());
    let f, fs = Term.of_sexp self.to_id e in
    (*
Fmt.(pr "%a\n" Sexplib.Sexp.pp_hum e);
Fmt.(pr "%a" (list int) fs);
print_string "  \n";
print_string f; *)
    add_to_relations self (f, fs)

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
    let rec go (relations : trie list) current_sub =
      Fmt.pr "CUR: %a\n" pp_substitution current_sub;
      Fmt.pr "Trie: %a\n" (Trie.pp pp_k pp_eclass_id) (List.nth relations 0);
      Fmt.pr "Trie: %a\n" (Trie.pp pp_k pp_eclass_id) (List.nth relations 1);
      function
      | [] -> [ current_sub ]
      | var :: vars' ->
          List.concat
            (List.map
               (fun (v, relations') ->
                 (*
                 Fmt.(pr "trying %a\n" int v);
                 let res = go relations' ((var, v) :: current_sub) vars' in
                 Fmt.(pr "back up from %a\n" int v);
                 res) *)
                 go relations' ((var, v) :: current_sub) vars')
               (get_substitutions var relations))
    in
    go (List.map snd self.relations) [] self.patterns

  let generic_join' self : substitution' list =
    let open StringMap in
    let root, patterns = self.root_pattern in
    (* Fmt.(pr "patterns: %a\n" (list string) (patterns |> StringSet.to_list));
    Fmt.(pr "root: %a\n" string root); *)
    let rec go (relations : trie list) root_sub current_sub = function
      | [] -> [ Option.get root_sub, current_sub ]
      | var :: vars' ->
          List.concat
            (List.map
               (fun (v, relations') ->
                 let current_sub' =
                   if not (StringSet.mem var patterns) then current_sub
                   else add var v current_sub
                 in
                 let root_sub' = if String.equal var root then Some(v) else root_sub in
                 go relations' root_sub' current_sub' vars')
               (get_substitutions var relations))
    in
    go (List.map snd self.relations) None empty self.patterns
end
