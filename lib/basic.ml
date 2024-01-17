open Containers [@@warning "-33"]
open Language
open Types
module StringMap = Map.Make (String)

let str p v = Format.to_string p v
let lappend_pair a (b, c) = (a, b, c)

module Symbol = Symbol

module Query = struct
  module Query = Query

  type 'a query = 'a Query.t = V of string | Q of 'a * 'a query list
  type t = Symbol.t query

  let of_sexp = Query.of_sexp Symbol.intern
  let to_sexp = Query.to_sexp (Format.to_string Symbol.pp)
  let pp = Query.pp Symbol.pp
  let show = Format.to_string pp
  let variables = Query.variables
end

module Term = Term

module Rule : sig
  type 'sym rule = Query.t * Query.t
  type t = Symbol.t rule [@@deriving show]

  val make : from:Query.t -> into:Query.t -> t option
end = struct
  type 'sym rule = Query.t * Query.t
  type t = Symbol.t rule

  let make ~from ~into =
    let pattern_vars = Query.variables from in
    let rewrite_vars = Query.variables into in
    if StringSet.subset rewrite_vars pattern_vars then Some (from, into)
    else None

  let pp fmt (lhs, rhs) =
    Format.pp_open_hbox fmt ();
    Query.pp fmt lhs;
    Format.pp_print_string fmt " -> ";
    Query.pp fmt rhs;
    Format.pp_close_box fmt ()

  let show = str pp

  let%test "rules are printed as expected" =
    Alcotest.(check string)
      "prints as expected" "(<< ?a 1) -> (* ?a 2)"
      (str pp
         ( Q (Symbol.intern "<<", [ V "a"; Q (Symbol.intern "1", []) ]),
           Q (Symbol.intern "*", [ V "a"; Q (Symbol.intern "2", []) ]) ))
end

(* * Egraphs *)
(* ** Types *)
type egraph = {
  mutable version : int;
  uf : Id.store;
      (* tracks equivalence classes of
         class ids *)
  class_members : (enode * Id.t) Vector.vector Id.Map.t;
      (* maps classes to the canonical nodes
         they contain, and any classes that are
         children of these nodes *)
  hash_cons : (enode, Id.t) Hashtbl.t;
      (* maps cannonical nodes to their
         equivalence classes *)
  worklist : Id.t Vector.vector;
      (* List of equivalence classes for which
         nodes are out of date - i.e
         cannoncial(node) != node *)
}

(* ** Graph *)
module EGraph = struct
  type t = egraph

  (* *** Pretty printing *)
  let pp ?(pp_id = EClassId.pp) fmt self =
    let open Format in
    pp_print_string fmt "(egraph";
    pp_open_hovbox fmt 1;
    pp_print_space fmt ();
    pp_print_string fmt "(eclasses ";
    pp_open_hvbox fmt 1;
    Id.Map.to_seq self.class_members
    |> Seq.to_list
    |> pp_print_list ~pp_sep:pp_print_space
         (fun fmt (cls, elts) ->
           pp_print_string fmt "(";
           pp_open_hvbox fmt 1;
           pp_id fmt cls;
           if not @@ Vector.is_empty elts then pp_print_space fmt ();
           Vector.pp ~pp_sep:pp_print_space
             (fun fmt (node, id) ->
               pp_print_string fmt "(";
               pp_open_hbox fmt ();
               pp_id fmt id;
               pp_print_space fmt ();
               ENode.pp ~pp_id fmt node;
               pp_close_box fmt ();
               pp_print_string fmt ")")
             fmt elts;
           pp_close_box fmt ();
           pp_print_string fmt ")")
         fmt;
    pp_close_box fmt ();
    pp_print_string fmt ")";
    pp_print_space fmt ();
    pp_print_string fmt "(enodes ";
    pp_open_hvbox fmt 1;
    Hashtbl.to_seq self.hash_cons
    |> Seq.to_list
    |> pp_print_list ~pp_sep:pp_print_space
         (fun fmt (node, cls) ->
           pp_print_string fmt "(";
           pp_open_hvbox fmt 1;
           pp_id fmt cls;
           pp_print_space fmt ();
           ENode.pp ~pp_id fmt node;
           pp_close_box fmt ();
           pp_print_string fmt ")")
         fmt;
    pp_close_box fmt ();
    pp_print_string fmt ")";
    pp_close_box fmt ();
    pp_print_string fmt ")"

  let ( .@[] ) self fn = fn self [@@inline always]

  (* *** Initialization *)
  let init () =
    {
      version = 0;
      uf = Id.create_store ();
      class_members = Id.Map.create 10;
      hash_cons = Hashtbl.create 10;
      worklist = Vector.create ();
    }

  (* *** Eclasses *)
  let new_class self =
    let id = Id.make self.uf () in
    id

  let get_class_members self id =
    match Id.Map.find_opt self.class_members id with
    | Some classes -> classes
    | None ->
        let cls = Vector.create () in
        Id.Map.add self.class_members id cls;
        cls

  (* Adds a node into the egraph, assuming that the cannonical version
     of the node is up to date in the hash cons or
  *)
  let add_enode self node =
    let node = ENode.canonicalise self.uf node in
    let id =
      match Hashtbl.find_opt self.hash_cons node with
      | None ->
          self.version <- self.version + 1;
          (* There are no nodes congruent to this node in the graph *)
          let id = self.@[new_class] in
          let cls = self.@[get_class_members] id in
          Vector.append_list cls
          @@ List.map (fun child -> (node, child)) (ENode.children node);
          Hashtbl.replace self.hash_cons node id;
          id
      | Some id -> id
    in
    Id.find self.uf id

  let rec subst self pat env =
    match pat with
    | Query.V id -> StringMap.find id env
    | Q (sym, args) ->
        let enode = (sym, List.map (fun arg -> self.@[subst] arg env) args) in
        self.@[add_enode] enode

  let add_node self ((sym, children) : Term.t) =
    add_enode self (Symbol.intern sym, children)

  let add_sexp self sexp = add_node self @@ Term.of_sexp (add_node self) sexp
  let find self vl = Id.find self.uf vl
  let append_to_worklist self vl = Vector.push self.worklist vl

  let merge self a b =
    let ( += ) va vb = Vector.append va vb in
    let a = Id.find self.uf a in
    let b = Id.find self.uf b in
    if Id.eq_id a b then ()
    else (
      self.version <- self.version + 1;
      assert (Id.eq_id a (Id.union self.uf a b));
      assert (Id.eq_id a (Id.find self.uf a));
      assert (Id.eq_id a (Id.find self.uf b));
      self.@[get_class_members] b += self.@[get_class_members] a;
      Vector.clear (self.@[get_class_members] a);
      self.@[append_to_worklist] b)

  let repair self ecls_id =
    let ( += ) va vb = Vector.append_iter va vb in
    let uses = self.@[get_class_members] ecls_id in
    let uses =
      let res = Vector.copy uses in
      Vector.clear uses;
      res
    in
    (* update canonical uses in hashcons *)
    Vector.to_iter uses (fun (p_node, p_eclass) ->
        Hashtbl.remove self.hash_cons p_node;
        let p_node = self.uf.@[ENode.canonicalise] p_node in
        Hashtbl.replace self.hash_cons p_node (self.@[find] p_eclass));
    let new_uses = Hashtbl.create 10 in
    Vector.to_iter uses (fun (p_node, p_eclass) ->
        let p_node = self.uf.@[ENode.canonicalise] p_node in
        (match Hashtbl.find_opt new_uses p_node with
        | None -> ()
        | Some nd -> self.@[merge] p_eclass nd);
        Hashtbl.replace new_uses p_node (self.@[find] p_eclass));
    self.@[get_class_members] (self.@[find] ecls_id) += Hashtbl.to_iter new_uses

  let rebuild self =
    while not @@ Vector.is_empty self.worklist do
      let worklist =
        Id.Set.of_iter (Vector.to_iter self.worklist |> Iter.map self.@[find])
      in
      Vector.clear self.worklist;
      Id.Set.to_iter worklist (fun ecls_id -> self.@[repair] ecls_id)
    done

  (* *** Exports *)
  (* **** Export eclasses *)
  let eclasses self =
    let r = Id.Map.create 10 in
    Hashtbl.iter
      (fun node eid ->
        let eid = Id.find self.uf eid in
        match Id.Map.find_opt r eid with
        | None ->
            let ls = Vector.of_list [ node ] in
            Id.Map.add r eid ls
        | Some ls -> Vector.push ls node)
      self.hash_cons;
    r

  (* **** Export as dot *)
  let to_dot self =
    let eclasses = eclasses self in
    let stmt_list =
      let rev_map =
        Hashtbl.to_seq self.hash_cons |> Seq.map Pair.swap |> Id.Map.of_seq
      in
      let to_label id =
        let rec to_str id =
          match Id.Map.find_opt rev_map id with
          | None -> Format.to_string EClassId.pp id
          | Some (sym, []) -> Format.to_string Symbol.pp sym
          | Some (sym, children) ->
              Printf.sprintf "(%s %s)"
                (Format.to_string Symbol.pp sym)
                (List.to_string ~sep:" " to_str children)
        in
        to_str id
      in
      let to_label_node (sym, children) =
        match children with
        | [] -> Format.to_string Symbol.pp sym
        | children ->
            Printf.sprintf "(%s %s)"
              (Format.to_string Symbol.pp sym)
              (List.to_string ~sep:" " to_label children)
      in
      let to_id id = Odot.Double_quoted_id (to_label id) in
      let to_node_id node = Odot.Double_quoted_id (to_label_node node) in
      let to_subgraph_id id =
        Odot.Simple_id (Printf.sprintf "cluster_%d" (Id.repr id))
      in
      let sub_graphs =
        (fun f -> Fun.flip Id.Map.iter eclasses (Fun.curry f))
        |> Iter.map (fun (eclass, enodes) ->
               let nodes =
                 Vector.to_iter enodes
                 |> Iter.map (fun (node : enode) ->
                        let node_id = to_node_id node in
                        let attrs =
                          Odot.
                            [
                              ( Simple_id "label",
                                Some
                                  (Double_quoted_id
                                     (Format.to_string Symbol.pp (fst node))) );
                            ]
                        in
                        Odot.Stmt_node ((node_id, None), attrs))
                 |> Iter.to_list
               in
               Odot.(
                 Stmt_subgraph
                   {
                     sub_id = Some (to_subgraph_id eclass);
                     sub_stmt_list =
                       Stmt_attr
                         (Attr_graph
                            [
                              ( Simple_id "label",
                                Some
                                  (Simple_id
                                     (Format.to_string EClassId.pp eclass)) );
                            ])
                       :: nodes;
                   }))
        |> Iter.to_list
      in
      let edges =
        (fun f -> Fun.flip Id.Map.iter eclasses (Fun.curry f))
        |> Iter.flat_map (fun (_eclass, enodes) ->
               Vector.to_iter enodes
               |> Iter.flat_map (fun node ->
                      let label = to_node_id node in
                      Iter.of_list (ENode.children node)
                      |> Iter.map (fun child ->
                             let child_label = to_id child in
                             Odot.(
                               Stmt_edge
                                 ( Edge_node_id (label, None),
                                   [ Edge_node_id (child_label, None) ],
                                   [] )))))
        |> Iter.to_list
      in
      List.append sub_graphs edges
    in
    Odot.{ strict = true; kind = Digraph; id = None; stmt_list }

  (* **** Print as dot *)
  let pp_dot fmt st =
    Format.pp_print_string fmt (Odot.string_of_graph (to_dot st))

  let extract cost eg =
    let eclasses = eg.@[eclasses] in
    let cost_map = Id.Map.create 10 in
    let node_total_cost node =
      let has_cost id = Id.Map.mem cost_map (eg.@[find] id) in
      if List.for_all has_cost (Term.children node) then
        let cost_f id = fst @@ Id.Map.find cost_map (eg.@[find] id) in
        Some (cost cost_f node)
      else None
    in
    let make_pass enodes =
      let cost, node =
        Vector.to_iter enodes
        |> Iter.map (fun n -> (node_total_cost n, n))
        |> Iter.min_exn ~lt:(fun (c1, _) (c2, _) ->
               (match (c1, c2) with
               | None, None -> 0
               | Some _, None -> -1
               | None, Some _ -> 1
               | Some c1, Some c2 -> Float.compare c1 c2)
               = -1)
      in
      Option.map (fun cost -> (cost, node)) cost
    in
    let find_costs () =
      let any_changes = ref true in
      while !any_changes do
        any_changes := false;
        Fun.flip Id.Map.iter eclasses (fun eclass enodes ->
            let pass = make_pass enodes in
            match (Id.Map.find_opt cost_map eclass, pass) with
            | None, Some nw ->
                Id.Map.replace cost_map eclass nw;
                any_changes := true
            | Some (cold, _), Some ((cnew, _) as nw)
              when Float.compare cnew cold = -1 ->
                Id.Map.replace cost_map eclass nw;
                any_changes := true
            | _ -> ())
      done
    in
    let rec extract eid =
      let eid = find eg eid in
      let enode = Id.Map.find cost_map eid |> snd in
      let head = Atom (Format.to_string Symbol.pp @@ fst enode) in
      match ENode.children enode with
      | [] -> head
      | children -> List (head :: List.map extract children)
    in
    find_costs ();
    fun result -> extract result

  (* ** Matching *)
  let ematch eg classes pattern =
    let rec enode_matches p enode env =
      match[@warning "-8"] (p, enode) with
      | Query.(Q (f, _), (f', _))
        when not @@ (Equal.map Symbol.repr Equal.int) f f' ->
          None
      | Q (_, args), (_, args') ->
          (fun f -> List.iter2 (Fun.curry f) args args')
          |> Iter.fold_while
               (fun env (qvar, trm) ->
                 match env with
                 | None -> (None, `Stop)
                 | Some env -> (
                     match match_in qvar trm env with
                     | Some _ as res -> (res, `Continue)
                     | None -> (None, `Stop)))
               (Some env)
    and match_in p eid env =
      let eid = find eg eid in
      match p with
      | V id -> (
          match StringMap.find_opt id env with
          | None -> Some (StringMap.add id eid env)
          | Some eid' when Id.eq_id eid eid' -> Some env
          | _ -> None)
      | p ->
          Vector.to_iter (Id.Map.find classes eid)
          |> Iter.find_map (fun enode -> enode_matches p enode env)
    in
    (fun f -> Id.Map.iter (Fun.curry f) classes)
    |> Iter.filter_map (fun (eid, _) ->
           match match_in pattern eid StringMap.empty with
           | Some env -> Some (eid, env)
           | _ -> None)

  (* ** Rewriting System *)
  let apply_rules eg rules =
    let eclasses = eclasses eg in
    let find_matches (from_rule, to_rule) =
      ematch eg eclasses from_rule |> Iter.map (lappend_pair to_rule)
    in
    let for_each_match = Iter.of_list rules |> Iter.flat_map find_matches in
    for_each_match (fun (to_rule, eid, env) ->
        let new_eid = subst eg to_rule env in
        merge eg eid new_eid);
    rebuild eg

  let run_until_saturation ?fuel eg rules =
    match fuel with
    | None ->
        let rec loop last_version =
          apply_rules eg rules;
          if not @@ Int.equal eg.version last_version then loop eg.version
          else ()
        in
        loop eg.version;
        true
    | Some fuel ->
        let rec loop fuel last_version =
          apply_rules eg rules;
          if not @@ Int.equal eg.version last_version then
            if fuel > 0 then loop (fuel - 1) eg.version else false
          else true
        in
        loop fuel eg.version
end

open Join

let testable_sub =
  let open Alcotest in
  let fmt_eclass_id = Fmt.using Id.repr Fmt.int in
  let test_eclass_id = testable fmt_eclass_id Id.eq_id in
  let test_map =
    of_pp
      (Fmt.using StringMap.to_list
         (Fmt.list ~sep:Fmt.comma
            (Fmt.parens
               (Fmt.pair ~sep:(Fmt.any " ->@ ") Fmt.string fmt_eclass_id))))
  in
  list @@ pair test_eclass_id test_map

let get_ematches query exprs =
  let graph = EGraph.init () in
  List.iter (fun e -> ignore @@ EGraph.add_sexp graph e) exprs;
  EGraph.ematch graph (EGraph.eclasses graph) query |> Iter.to_list

let get_join_matches query exprs =
  let graph = EGraph.init () in
  List.iter (fun e -> ignore @@ EGraph.add_sexp graph e) exprs;
  let pats, q, root_pattern = Compile.compile query in
  let matcher =
    GenericJoin.make (EGraph.add_node graph) String.compare pats root_pattern q
  in
  List.iter (fun e -> GenericJoin.add_to_relations_sexp matcher e) exprs;
  GenericJoin.generic_join matcher

let compare_matches query exprs =
  Alcotest.check testable_sub "equal subs"
    (List.sort Stdlib.compare (get_ematches query exprs))
    (List.sort Stdlib.compare (get_join_matches query exprs))

let%test "f ?a (g ?a)" =
  compare_matches
    (Query.of_sexp [%s f "?a" (g "?b")])
    [ [%s f 1 (g 1)]; [%s f 1 (g 2)]; [%s f 2 (g 2)] ]

let%test "f ?a (g ?b)" =
  compare_matches
    (Query.of_sexp [%s f "?a" (g "?b")])
    [ [%s f 1 (g 1)]; [%s f 1 (g 2)]; [%s f 2 (g 2)] ]

let%test "f (h ?a) (g ?a)" =
  compare_matches
    (Query.of_sexp [%s f "?a" (g "?b")])
    [
      [%s f (h 1) (g 1)];
      [%s f (h 2) (g 2)];
      [%s f (g 1) (g 2)];
      [%s f (g 1) (h 2)];
      [%s f (h 1) (g 2)];
    ]

let%test "f 3 (g ?a)" =
  compare_matches
    (Query.of_sexp [%s f 3 (g "?b")])
    [
      [%s f 3 (g 1)];
      [%s f 3 (g 2)];
      [%s f 2 (g 2)];
      [%s f 2 (h 2)];
      [%s f 3 (g 2)];
    ]

let%test "f 3 5" =
  compare_matches
    (Query.of_sexp [%s f 3 5])
    [ [%s f 3 5]; [%s f 3 3]; [%s f 2 (g 2)]; [%s f 2 (h 2)]; [%s f 3 (g 2)] ]

let%test "f ?a (f ?a (f ?a ?a))" =
  compare_matches
    (Query.of_sexp [%s f "?a" (f "?a" (f "?a" "?a"))])
    [
      [%s f 3 (f 3 (f 3 3))];
      [%s f 3 3];
      [%s f 2 (g 2)];
      [%s f 2 (h 2)];
      [%s f 3 (g 2)];
      [%s f 4 (f 4 (f 4 4))];
    ]

(* TODO: handle select-all query. Pass this test.
let%test "?a" =
  compare_matches
    (Query.of_sexp [%s "?a"])
    [
      [%s f (h 1) (g 1)];
      [%s f (h 2) (g 2)];
      [%s f (g 1) (g 2)];
      [%s f (g 1) (h 2)];
      [%s f (h 1) (g 2)];
    ]
*)

(*
  TODO:
  X Fix compile to return all pattern variables that appear
  X Fix add_to_relations_sexp to recursively add expressions
  X Make it return only the relevant patterns, not auxiliary ones (and return substitution) (generic_join')
  X Make testable for substitution type
  X Modify tests to compare with ematching function.
    X Modify tests checking so that we can give just a list of matches.
  X Helper function for creating tests
  - Add more matching tests that already do merging/rebuilding
  X Handle patterns that appear more than once in a relation.
  - Deal with select all query Q(x) :- x. Special case
  - Kind of annoying?

  Note: broke abstraction of private ints for debugging purposes

   *)
