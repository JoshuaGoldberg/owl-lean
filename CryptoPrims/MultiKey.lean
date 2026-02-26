import OwlLean.TypeChecker.OwlComplete




def ENC := OwlTy_with [lK, lM] [] [m] {
  ∃ a <: Data lK.
    (a *
      (corr (lK) ?
        (Public * Public) -> Public
        :
        (a * m) -> Public)
      *
      (corr (lK) ?
        (Public * Public) -> Public
        :
        (a * Public) -> Maybe m)

        )
}
