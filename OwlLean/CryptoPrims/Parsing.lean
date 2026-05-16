import OwlLean.OwlLang.Owl
import OwlLean.TypeChecker.OwlComplete
import Std.Data.TreeMap
open Owl



#tc parse_example [] [v1, v2] [] [] := ⊢ {
  λ x =>
    let v : RData ⊥ [ "xyzw" ] = "xyzw" in
    let w = ⟨"splitL"⟩ ( "xyzw", 2) in
    let u = ⟨"splitR"⟩ ( "xyzw", 2) in
    get_val w = w in
    get_val u = u in
    assert ( w = "xy" );
    assert ( u = "zw" );
    v
} : Public -> Public
