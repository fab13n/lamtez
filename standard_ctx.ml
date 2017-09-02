open Ast
open Typecheck_ctx

let ctx = empty
  |> add_sum     "zero" [] []
  |> add_product "unit" [] []
  |> add_sum     "bool" [] ["False", tunit; "True", tunit]
  |> add_prim    "nat" []
  |> add_prim    "int" []
  |> add_prim    "time" []
  |> add_prim    "key" []
  |> add_prim    "string" []
  |> add_prim    "tez" []
  |> add_prim    "sig" []
  |> add_sum     "option" ["a"] ["None", tunit; "Some", TId(noloc, "a")]
  |> add_sum     "list" ["a"] ["Nil", tunit; "Cons", TTuple(noloc, [TId(noloc, "a"); TApp(noloc, "list", [TId(noloc, "a")])])]
  |> add_prim    "set" ["a"]
  |> add_prim    "map" ["k"; "v"]
  |> add_prim    "contract" ["param"; "result"]

  (* misc. *)

  |> add_evar "now"  ([], tprim0 "time")
  |> add_evar "unit" ([], tunit)
  |> add_evar "fail" ([], TFail)

  (* contract manipulation *)

  |> add_evar "contract-call" (* contract p r -> p -> tez -> r *)
    (["param"; "result"],
      tlambda [TApp(noloc, "contract", [TId(noloc, "param"); TId(noloc, "result")]);
               TId(noloc, "param"); tprim0 "tez"; TId(noloc, "result")])
  |> add_evar "contract-create"
    (* key -> key? -> bool -> bool -> tez -> (p*g -> r*g) -> g -> g -> contract p r *)
    (["param"; "storage"; "result"],
     tlambda [tprim0 "key"; toption (tprim0 "key");
              tprim0 "bool"; tprim0 "bool";
              tprim0 "tez";
              TLambda(noloc, TTuple(noloc, [TId(noloc, "param"); TId(noloc, "storage")]),
                      TTuple(noloc, [TId(noloc, "result"); TId(noloc, "storage")]));
              TId(noloc, "storage");
              TApp(noloc, "contract", [TId(noloc, "param"); TId(noloc, "result")])])
  |> add_evar "contract-create-account"
    (* key -> key? -> bool -> tez -> contract unit unit *)
      ([], tlambda [tprim0 "key"; toption (tprim0 "key");
                tprim0 "bool"; tprim0 "tez";
                TApp(noloc, "contract", [tunit; tunit])])
  |> add_evar "contract-get"
    ([], TLambda(noloc, tprim0 "key", TApp(noloc, "contract", [tunit; tunit])))
  |> add_evar "contract-manager"
    (["param"; "storage"],
     TLambda(noloc, TApp(noloc, "contract", [TId(noloc, "param"); TId(noloc, "storage")]), tprim0 "key"))

  (* This contract's self-awareness *)

  |> add_evar "self-amount" ([], tprim0 "tez")
  |> add_evar "self-contract"
    (["param"; "result"], TApp(noloc, "contract", [TId(noloc, "param"); TId(noloc, "result")]))
  |> add_evar "self-balance" ([], tprim0 "tez")
  |> add_evar "self-steps-to-quota" ([], tprim0 "nat")
  |> add_evar "self-source"
    (["param"; "result"], TApp(noloc, "contract", [TId(noloc, "param"); TId(noloc, "result")]))

  (* crypto *)

  |> add_evar "crypto-hash" (["a"], TLambda(noloc, TId(noloc, "a"), tprim0 "string"))
  |> add_evar "crypto-check" (* key -> signature -> string -> bool *)
    ([], tlambda [tprim0 "key"; tprim0 "sig"; tprim0 "string"; tprim0 "bool"])

  (* sets *)

  |> add_evar "set-empty" (["elt"], TApp(noloc, "set", [TId(noloc, "elt")]))
  |> add_evar "set-mem"  (["elt"], TLambda(noloc, TApp(noloc, "set", [TId(noloc, "elt")]), tprim0 "bool"))
  |> add_evar "set-update"
    (["elt"], tlambda [TId(noloc, "elt"); tprim0 "bool"; TApp(noloc, "set", [TId(noloc, "elt")])])
  |> add_evar "set-map"
    (["a"; "b"], tlambda [tlambda [TId(noloc, "a"); TId(noloc, "b")];
                          TApp(noloc, "set", [TId(noloc, "a")]);
                          TApp(noloc, "set", [TId(noloc, "b")])])
  |> add_evar "set-reduce"
    (["elt"; "acc"], tlambda [tlambda [TId(noloc, "elt"); TId(noloc, "acc"); TId(noloc, "acc")];
                              TApp(noloc,"set", [TId(noloc, "elt")]);
                              TId(noloc, "acc");
                              TId(noloc, "acc")])

  (* maps *)

  |> add_evar "map-empty" (["k"; "v"], TApp(noloc, "map", [TId(noloc, "k"); TId(noloc, "v")]))
  |> add_evar "map-mem"
    (["k"; "v"], tlambda [TId(noloc, "k");
                          TApp(noloc, "map", [TId(noloc, "k"); TId(noloc, "v")]);
                          tprim0 "bool"])
  |> add_evar "map-get"
    (["k"; "v"], tlambda [TId(noloc, "k");
                          TApp(noloc, "map", [TId(noloc, "k"); TId(noloc, "v")]);
                          toption(TId(noloc, "v"))])
  |> add_evar "map-update"
    (["k"; "v"], tlambda [TId(noloc, "k");
                          toption (TId(noloc, "v"));
                          TApp(noloc, "map", [TId(noloc, "k"); TId(noloc, "v")]);
                          TApp(noloc, "map", [TId(noloc, "k"); TId(noloc, "v")])])
  |> add_evar "map-map"
    (["k"; "v0"; "v1"], tlambda [tlambda [TId(noloc, "k"); TId(noloc, "v0"); TId(noloc, "v1")];
                                 TApp(noloc, "map", [TId(noloc, "k"); TId(noloc, "v0")]);
                                 TApp(noloc, "map", [TId(noloc, "k"); TId(noloc, "v1")])])
  |> add_evar "map-reduce"
    (["k"; "v"; "acc"], tlambda [tlambda [TId(noloc, "k"); TId(noloc, "v"); TId(noloc, "acc"); TId(noloc, "acc")];
                                 TApp(noloc, "map", [TId(noloc, "k"); TId(noloc, "v")]);
                                 TId(noloc, "acc");
                                 TId(noloc, "acc")])

  (* lists *)

  |> add_evar "list-map"
    (["a"; "b"], tlambda [tlambda [TId(noloc, "a"); TId(noloc, "b")];
                          TApp(noloc, "list", [TId(noloc, "a")]);
                          TApp(noloc, "list", [TId(noloc, "b")])])
  |> add_evar "list-reduce"
    (["a"; "acc"], tlambda [tlambda [TId(noloc, "a"); TId(noloc, "acc"); TId(noloc, "acc")];
                            TApp(noloc, "list", [TId(noloc, "a")]);
                            TId(noloc, "acc");
                            TId(noloc, "acc")])
    
