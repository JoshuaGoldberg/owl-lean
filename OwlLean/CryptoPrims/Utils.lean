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
    m := (λ (k2 : Public) : (t + unit) => if ⟨"eq"⟩(k2, k) then ı1 v else (old k))
} : $ Map [] [] [t] -> Public -> t -> unit
