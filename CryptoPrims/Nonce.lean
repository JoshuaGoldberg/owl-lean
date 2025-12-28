import OwlLean.TypeChecker.OwlComplete

def OwlBool :=
  OwlTy [] [] {
      ∀ t <: Any.
        (t * t) -> t
  }

def OwlTrue :=
  Owl [] [] [] {
    Λ α.
      λ x => π1 x
  }

def OwlFalse :=
  Owl [] [] [] {
    Λ α.
      λ x => π2 x
  }

theorem OwlTrue.wf :
  (· ; ·; ·; ·; ($ OwlTrue [] [] []) ⊢ ($ OwlBool [] [])) := by
    tc_man (
      try simp
    )



def NONCE :=
  OwlTy [l] [] {
    ∃ α <: Data l.
      (α * (corr (l) ? (Public * Public -> Public) :
                       (α * Public ->
      Unit))
  }
