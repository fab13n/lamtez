open Ast
open Typecheck_ctx

let ctx = empty
  |> add_alias   "unit" ([], tunit)
  |> add_sum     "zero" [] []
  |> add_sum     "bool" [] ["False", tunit; "True", tunit]
  |> add_prim    "nat" []
  |> add_prim    "int" []
  |> add_prim    "time" []
  |> add_prim    "key" []
  |> add_prim    "string" []
  |> add_prim    "tez" []
  |> add_prim    "sig" []
  |> add_sum     "or"  ["a"; "b"] ["Left", tid "a"; "Right", tid "b"]
  |> add_sum     "option" ["a"] ["None", tunit; "Some", tid "a"]
  |> add_sum     "list" ["a"] ["Nil", tunit; "Cons", ttuple[tid "a"; tapp "list" [tid "a"]]]
  |> add_prim    "set" ["a"]
  |> add_prim    "map" ["k"; "v"]
  |> add_prim    "contract" ["param"; "result"]
  |> add_alias   "account" ([], tapp "contract" [tunit; tunit])
  |> add_prim   "closure" ["env"; "param"; "result"]
  
  (* misc. *)

  |> add_evar "fail" ([], TFail)

  (* contract manipulation *)

  |> add_evar "contract-call" (* contract p r -> p -> tez -> r *)
    (["param"; "result"],
      tlambda [tapp "contract" [tid "param"; tid "result"];
               tid "param"; tprim "tez"; tid "result"])
  |> add_evar "contract-create"
    (* key -> key? -> bool -> bool -> tez -> (p*g -> r*g) -> g -> g -> contract p r *)
    (["param"; "storage"; "result"],
     tlambda [tprim "key"; toption (tprim "key");
              tprim "bool"; tprim "bool";
              tprim "tez";
              tlambda [(ttuple [tid "param"; tid "storage"]);
                       (ttuple ([tid "result"; tid "storage"]))];
              tid "storage";
              tapp "contract" [tid "param"; tid "result"]])
  |> add_evar "contract-create-account"
    (* key -> key? -> bool -> tez -> contract unit unit *)
      ([], tlambda [tprim "key"; toption (tprim "key");
                    tprim "bool"; tprim "tez";
                    tapp "contract" [tunit; tunit]])
  |> add_evar "contract-get"
    ([], tlambda [tprim "key"; tapp "contract" [tunit; tunit]])
  |> add_evar "contract-manager"
    (["param"; "storage"],
     tlambda [tapp "contract" [tid "param"; tid "storage"]; tprim "key"])

  (* This contract's self-awareness *)

  |> add_evar "self-now"  ([], tprim "time")
  |> add_evar "self-amount" ([], tprim "tez")
  |> add_evar "self-contract"
    (["param"; "result"], tapp "contract" [tid "param"; tid "result"])
  |> add_evar "self-balance" ([], tprim "tez")
  |> add_evar "self-steps-to-quota" ([], tprim "nat")
  |> add_evar "self-source"
    (["param"; "result"], tapp "contract" [tid "param"; tid "result"])

  (* crypto *)

  |> add_evar "crypto-hash" (["a"], tlambda [tid "a"; tprim "string"])
  |> add_evar "crypto-check" (* key -> signature -> string -> bool *)
    ([], tlambda [tprim "key"; tprim "sig"; tprim "string"; tprim "bool"])

  (* sets *)

  |> add_evar "set-empty" (["elt"], tapp "set" [tid "elt"])
  |> add_evar "set-mem"  (["elt"], tlambda [tapp "set" [tid "elt"]; tid "elt"; tprim "bool"])
  |> add_evar "set-update"
    (["elt"], tlambda [tid "elt"; tprim "bool"; tapp "set" [tid "elt"]])
  |> add_evar "set-map"
    (["a"; "b"], tlambda [tlambda [tid "a"; tid "b"];
                          tapp "set" [tid "a"];
                          tapp "set" [tid "b"]])
  |> add_evar "set-reduce"
    (["elt"; "acc"], tlambda [tlambda [tid "elt"; tid "acc"; tid "acc"];
                              tapp "set" [tid "elt"];
                              tid "acc";
                              tid "acc"])

  (* maps *)

  |> add_evar "map-empty" (["k"; "v"], tapp "map" [tid "k"; tid "v"])
  |> add_evar "map-mem"
    (["k"; "v"], tlambda [tid "k";
                          tapp "map" [tid "k"; tid "v"];
                          tprim "bool"])
  |> add_evar "map-get"
    (["k"; "v"], tlambda [tid "k";
                          tapp "map" [tid "k"; tid "v"];
                          toption(tid "v")])
  |> add_evar "map-update"
    (["k"; "v"], tlambda [tid "k";
                          toption (tid "v");
                          tapp "map" [tid "k"; tid "v"];
                          tapp "map" [tid "k"; tid "v"]])
  |> add_evar "map-map"
    (["k"; "v0"; "v1"], tlambda [tlambda [tid "k"; tid "v0"; tid "v1"];
                                 tapp "map" [tid "k"; tid "v0"];
                                 tapp "map" [tid "k"; tid "v1"]])
  |> add_evar "map-reduce"
    (["k"; "v"; "acc"], tlambda [tlambda [tid "k"; tid "v"; tid "acc"; tid "acc"];
                                 tapp "map" [tid "k"; tid "v"];
                                 tid "acc";
                                 tid "acc"])

  (* lists *)

  |> add_evar "list-map"
    (["a"; "b"], tlambda [tlambda [tid "a"; tid "b"];
                          tapp "list" [tid "a"];
                          tapp "list" [tid "b"]])
  |> add_evar "list-reduce"
    (["a"; "acc"], tlambda [tlambda [tid "a"; tid "acc"; tid "acc"];
                            tapp "list" [tid "a"];
                            tid "acc";
                            tid "acc"])


let operators = ["EQ"; "NEQ"; "LE"; "LT"; "GE"; "GT"; "CONCAT"; "OR"; "AND"; 
"XOR"; "ADD"; "SUB"; "MUL"; "EDIV"; "LSR"; "LSL"; "NOT"; "NEG"; "ABS"] 

let globals = get_evars ctx @ operators
