import OwlLean.TypeChecker.OwlComplete
import OwlLean.OwlLang.Owl


#ty Map [] [] [t] :=
  Ref (Public -> t + unit)

#tc NewMap [] [] [t <: Any] [] := ⊢ {
  alloc (λ (null : Public) : (t + unit) => ı2 ())
} : $ Map [] [] [t]

#tc GetMap [] [] [t <: Any] [] := ⊢ {
  λ (m : $ Map [] [] [t]) : Public -> t + unit =>
  λ (k : Public) : t + unit =>
    (! m) k
} : $ Map [] [] [t] -> Public -> t + unit

#tc SetMap [] [] [t <: Any] [] := ⊢ {
  λ (m : $ Map [] [] [t]) : Public -> t -> unit  =>
  λ (k : Public) : t -> unit =>
  λ (v : t) : unit =>
    let old = (! m) in
    m := (λ (k2 : Public) : (t + unit) => if ⟦eq⟧(k2, k) then ı1 v else (old k))
} : $ Map [] [] [t] -> Public -> t -> unit

/--
`mk_map t` creates a new map from keys of type Public to t
-/
macro "mk_map" t:owl_type : owl_tm =>
  `(owl_tm | $ NewMap [] [] [$t:owl_type] [] )

/--
`get_map t mp k` gets the value of the map mp at key k
-/
macro "get_map" t:owl_type : owl_tm =>
  `(owl_tm | $ GetMap [] [] [$t:owl_type] [] )

/--
`set_map t mp k v` sets the value of the map mp at key k to v
-/
macro "set_map" t:owl_type : owl_tm =>
  `(owl_tm | $ SetMap [] [] [$t:owl_type] [] )
