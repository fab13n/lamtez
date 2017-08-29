open Tree
open TypingContext

let ctx = TypingContext.(empty
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
  |> add_sum     "option" ["a"] ["None", tunit; "Some", TId "a"]
  |> add_sum     "list" ["a"] ["Nil", tunit; "Cons", TTuple[TId "a"; TApp("list", [TId "a"])]]
  |> add_prim    "set" ["a"]
  |> add_prim    "map" ["k"; "v"]
  |> add_prim    "contract" ["param"; "result"]

  (* misc. *)

  |> add_evar "now"  ([], tprim0 "time")
  |> add_evar "unit" ([], tunit)
  |> add_evar "fail" ([], TFail)

  (* contract manipulation *)

  |> add_evar "contract-call" (* param -> tez -> contract param result -> storage -> result*storage *) 
    (["param"; "result"; "storage"], 
      tlambda [TId "param"; 
               tprim0 "tez"; 
               TApp("contract", [TId "param"; TId "result"]);
               TId "storage";
               TTuple[TId "result"; TId "storage"]])

  |> add_evar "contract-create" 
    (* key -> key? -> bool -> bool -> tez -> (p*g -> r*g) -> g -> g -> contract p r *)
    (["param"; "storage"; "result"],
     tlambda [tprim0 "key"; toption (tprim0 "key");
              tprim0 "bool"; tprim0 "bool";
              tprim0 "tez";
              TLambda(TTuple[TId "param"; TId "storage"],
                      TTuple[TId "result"; TId "storage"]);
              TId "storage";
              TApp("contract", [TId "param"; TId "result"])])
  |> add_evar "contract-create-account"
    (* key -> key? -> bool -> tez -> contract unit unit *)
      ([], tlambda [tprim0 "key"; toption (tprim0 "key");
                tprim0 "bool"; tprim0 "tez";
                TApp("contract", [tunit; tunit])])
  |> add_evar "contract-get"
    ([], TLambda(tprim0 "key", TApp("contract", [tunit; tunit])))
  |> add_evar "contract-manager"
    (["param"; "storage"],
     TLambda(TApp("contract", [TId "param"; TId "storage"]), tprim0 "key"))

  (* This contract's self-awareness *)

  |> add_evar "self-amount" ([], tprim0 "tez")
  |> add_evar "self-contract"
    (["param"; "result"], TApp("contract", [TId "param"; TId "result"]))
  |> add_evar "self-balance" ([], tprim0 "tez")
  |> add_evar "self-steps-to-quota" ([], tprim0 "nat")
  |> add_evar "self-source"
    (["param"; "result"], TApp("contract", [TId "param"; TId "result"]))

  (* crypto *)

  |> add_evar "crypto-hash" (["a"], TLambda(TId "a", tprim0 "string"))
  |> add_evar "crypto-check" (* key -> signature -> signed_string -> bool *)
    ([], tlambda [tprim0 "key"; tprim0 "sig"; tprim0 "string"; tprim0 "bool"])
  
  (* sets *)

  |> add_evar "set-empty" (["elt"], TApp("set", [TId "elt"]))
  |> add_evar "set-mem"  (["elt"], TLambda(TApp("set", [TId "elt"]), tprim0 "bool"))
  |> add_evar "set-update"
    (["elt"], tlambda [TId "elt"; tprim0 "bool"; TApp("set", [TId "elt"])])
  |> add_evar "set-map"
    (["a"; "b"], tlambda [tlambda [TId "a"; TId "b"];
                          TApp("set", [TId "a"]);
                          TApp("set", [TId "b"])])
  |> add_evar "set-reduce"
    (["elt"; "acc"], tlambda [tlambda [TId "elt"; TId "acc"; TId "acc"];
                              TApp("set", [TId "elt"]);
                              TId "acc";
                              TId "acc"])

  (* maps *)
  
  |> add_evar "map-empty" (["k"; "v"], TApp("map", [TId "k"; TId "v"]))
  |> add_evar "map-mem" 
    (["k"; "v"], tlambda [TId "k"; 
                          TApp("map", [TId "k"; TId "v"]);
                          tprim0 "bool"])
  |> add_evar "map-get" 
    (["k"; "v"], tlambda [TId "k"; 
                          TApp("map", [TId "k"; TId "v"]);
                          toption(TId "v")])
  |> add_evar "map-update" 
    (["k"; "v"], tlambda [TId "k"; 
                          toption (TId "v");
                          TApp("map", [TId "k"; TId "v"]); 
                          TApp("map", [TId "k"; TId "v"])])
  |> add_evar "map-map" 
    (["k"; "v0"; "v1"], tlambda [tlambda [TId "k"; TId "v0"; TId "v1"];
                                 TApp("map", [TId "k"; TId "v0"]);
                                 TApp("map", [TId "k"; TId "v1"])])
  |> add_evar "map-reduce" 
    (["k"; "v"; "acc"], tlambda [tlambda [TId "k"; TId "v"; TId "acc"; TId "acc"];
                                 TApp("map", [TId "k"; TId "v"]);
                                 TId "acc";
                                 TId "acc"])
  
  (* lists *)
  
  |> add_evar "list-map"
    (["a"; "b"], tlambda [tlambda [TId "a"; TId "b"];
                          TApp("list", [TId "a"]);
                          TApp("list", [TId "b"])])
  |> add_evar "list-reduce"
    (["a"; "acc"], tlambda [tlambda [TId "a"; TId "acc"; TId "acc"];
                            TApp("list", [TId "a"]);
                            TId "acc";
                            TId "acc"])
  
  )
