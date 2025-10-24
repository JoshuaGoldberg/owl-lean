import OwlLean.OwlLang.Owl
import Lean
import Std.Data.HashMap
import OwlLean.TypeChecker.OwlParser
import OwlLean.TypeChecker.OwlTyping

-- check that labels works
#eval label_parse(x ⊓ y)

-- Just define some concrete elements:
axiom bot : Owl.Lcarrier
axiom top : Owl.Lcarrier
axiom low : Owl.Lcarrier
axiom high : Owl.Lcarrier

-- Then test:
#check label_parse(⟨ Owl.L.bot ⟩)
#check label_parse(⟨ low ⟩)

#reduce OwlTy [] [] { Public }

-- check that cond_sym works
#eval cond_sym_parse(⊑)
#eval cond_sym_parse(!⊑)

-- check that constraints works
#eval constraint_parse(y ⊑ x)

-- check that binary works
#eval binary_parse("1101")

-- check that types works
#eval type_parse(Unit -> Unit)
#eval type_parse(∀ t <: Any . (t -> t))

-- test operator
def coin_flip : Owl.op :=
  fun (x1 x2 : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- check that terms works
#eval term_parse(case * in x1 => pack (Unit, x1) | x2 => (Λ t . * [[ t ]]))
#reduce term_parse(* [[[ z ⊔ ⟨Owl.L.bot⟩ ]]])
#eval term_parse(⟨ coin_flip ⟩ ( ["110"] , ["110"]))

-- check that terms works (format 2)
#eval Owl_Parse {
  unpack p as (a, x) in
    case π1 x in
      x => ⟨ ı1 x , π2 i ⟩
    | y => ⟨ ı2 y , π2 x ⟩
}

#eval Owl_Parse {
  ( fix loop ( state )
    case (! state) in
      cont => loop [ alloc cont ]
    | done => *
  ) [ alloc ⟨ ı1 * , * ⟩ ]
}

-- non functional
def sub_op : Owl.op :=
  fun (x1 x2 : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def mul_op : Owl.op :=
  fun (x1 x2 : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

#eval Owl_Parse {
  fix factorial ( n )
    if n then
      ⟨ mul_op ⟩ ( n , factorial [ ⟨ sub_op ⟩ ( n , 1 ) ] )
    else
      1
}

-- check that Owl elaborates and translates
#eval Owl [x, y, z] [] [x, y]{
  *
}

#eval Owl [] [] [] {
  fix factorial ( n )
    if n then
      ⟨ mul_op ⟩ ( n , factorial [ ⟨ sub_op ⟩ ( n , 1 ) ] )
    else
      1
}

#eval Owl [] [] [] {
  ( fix loop ( state )
    case (! state) in
      cont => loop [ alloc cont ]
    | done => *
  ) [ alloc ⟨ ı1 * , * ⟩ ]
}

#eval Owl [] [] [] {
  unpack (pack (Unit, *)) as (a, x) in
    case π1 x in
      x => ⟨ ı1 x , π2 x ⟩
    | y => ⟨ ı2 y , π2 x ⟩
}

#eval Owl [] [] [] {
  let x = 5 in
    x [x]
}

def test_embed (e : Owl.tm 0 0 0) : Owl.tm 0 0 0 :=
  Owl [] [] [] {
    ⟨$ e , $ e⟩
  }

def test_lam : Owl.tm 0 0 0 :=
  Owl [] [] [] {
    Λ x . * [[x]]
  }

#eval Owl [] [] [] {
  ($ (test_embed test_lam)) [error]
}

-- LAYERED ENCRYPTION EXAMPLE

-- non functional
def genKey : Owl.op :=
  fun (_ m_ty : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def enc : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

-- non functional
def rand : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

theorem gen_key_ht (l1 : Owl.L.labels):
  (· ; · ; · ; · ; (⟨genKey⟩ (["000"], ["000"])) ⊢ (Data ⟨l1⟩)) :=
    by
     apply infer_sound
     dsimp [infer, SLabel.elab, check_subtype]
     simp at *







theorem gen_key_pack_ht (l1 l2 : Owl.L.labels) (pf : Owl.L.leq l1 l2 = true):
  (· ; · ; · ; · ; (pack ((Data ⟨l1⟩), ⟨genKey⟩ (["000"], ["000"]))) ⊢ (∃ alphaK <: (Data ⟨l2⟩) . alphaK)) :=
    by
    tc (
      try attempt_solve
    )

theorem gen_key_pack_pair_ht (l1 l2 : Owl.L.labels) (pf : Owl.L.leq l1 l2 = true):
  (· ; · ; · ; · ; (pack ((Data ⟨l1⟩), ⟨⟨genKey⟩ (["000"], ["000"]), *⟩ )) ⊢ (∃ alphaK <: (Data ⟨l2⟩) . (alphaK * Unit))) :=
    by
    tc_man (
      try simp
      attempt_solve
    )

theorem gen_key_pack_pair_if_ht (l1 l2 : Owl.L.labels) (pf : Owl.L.leq l1 l2 = true):
  (· ; · ; · ; · ;
    (pack ((Data ⟨l1⟩), ⟨⟨genKey⟩ (["000"], ["000"]),
                        if ["10001"] then * else *⟩)) ⊢
    (∃ alphaK <: (Data ⟨l2⟩) . (alphaK * Unit))) :=
    by
    tc_man (
      try simp
      auto_solve
    )

noncomputable def ENC :=
  OwlTy [betaK, betaM, betaC] [] {
    ∃ alphaK <: (Data betaK) . (alphaK * ((corr ( betaK ) ? (Public * Public) -> Public : (alphaK * Data betaM) -> Public)
                                          *
                                          (corr ( betaK ) ? (Public * Public) -> Public : ((Data betaK) * (Data betaM)) -> Public)))
  }

 theorem enc_ty :
  ((betaK, betaM ⊑ betaK) ; · ; · ; · ;
    pack (Public, ⟨⟨genKey⟩ (["000"], ["000"]), (corr_case betaK in if corr ( betaK ) then ((λx . ⟨enc⟩ (π1 x, π2 x)) : (Public * Public) -> Public)
                                                        else ((λx . ⟨rand⟩ (zero (π2 x), ["0"])) : (Public * Data betaM) -> Public))⟩)
      ⊢
      (∃ alphaK <: (Data betaK) . (alphaK * corr (betaK) ? (Public * Public) -> Public : (alphaK * Data betaM) -> Public))) :=
    by
    tc_man (
      try simp
      auto_solve
    )

theorem test_annot :
   (· ; -- Phi
    · ;
    · ; -- Delta
    · ; -- Gamma
   ((λ y. y) [*]) ⊢ -- Tm
   (Unit)) -- Ty
    :=
  by
  tc (try grind)

def P (l1 l2 adv : Owl.label 0) :=
  Owl [] [] [] {
    unpack $ (Enc l1 adv) as (alpha1, p1) in
    unpack $ (Enc l2 adv) as (alpha1, p2) in
    let n = sync ((π2 p1) [⟨π1 p1, π1 p2⟩]) in
            sync ((π2 p2) [⟨π1 p2, ["010101"]⟩])
  }

-- TC tests

#reduce infer empty_phi (empty_psi 0) empty_delta empty_gamma (.unpack (.annot packed_unit (.ex .Any .Unit)) .skip) (.some .Unit)

-- number of variables must match!
def towl_ty :=
  OwlTy [x] [x] {
    Unit -> Unit
  }

def towl_tm :=
  Owl [x] [x] [y] {
    fix f (z) z
  }

noncomputable def lemma_phi_new :=
  Ψ:= (x, y ⊒ x, z ⊒ y, a ⊒ z)

-- OLD WAY (cool, but not *as* cool)
theorem lambda_identity_unit_2  :
          has_type  (Ψ:= (x, y ⊑ x))
                    []
                    (dcons .Unit empty_delta)
                    (Owl.cons .Any empty_gamma)
                    (Owl [x, y] [x] [y] { fix f (z) z })
                    (OwlTy [x, y] [x] { Unit -> Unit }) :=
  by
  tc (try grind)

-- NEW WAY (easier to write, cleaner in various ways, but doesn't quite support embedding)
theorem lambda_identity_unit_3 :
   ((x, y ⊑ x); -- Phi
   · ;
   (x <: Unit, y <: Data y); -- Delta
   (x => Any, y => Data ⟨Owl.L.bot⟩); -- Gamma
   (fix f (z) z) ⊢ -- Tm
   (Unit -> Unit)) -- Ty
    :=
  by
  tc (try grind)

-- cool test for embdedding
theorem phi_tc_sc (l1 : Owl.L.labels) :
  ((pcons (.leq, .var_label 0) (pcons (.geq, .latl Owl.L.bot) empty_phi)) |= (.condition .leq (.latl Owl.L.bot) (.latl l1))) := by
    try solve_phi_validation_anon

-- labels example
theorem phi_tc_test (l1 : Owl.L.labels):
  ((x, z ⊑ x); -- Phi
  · ;
  (x <: Unit, y <: Data x); -- Delta
  (x => Any, y => Data ⟨Owl.L.bot⟩); -- Gamma
  ⟨ * ,(fix f (z) y)⟩ ⊢  -- Tm
  (Unit * (Unit -> (Data ⟨l1⟩)))) -- Ty
  :=
  by
  tc (
    try attempt_solve
  )

-- cool test for embdedding
theorem test_latt_new :
  ((x, y ⊒ x, z ⊒ y, a ⊒ z) ⊨ (y ⊒ x)) := by
    solve_phi_validation_anon

theorem test_latt_new2 :
  (· ⊨ (y ⊒ x)) := by
    attempt_solve


def MapOf (t : Owl.ty 0 0) := OwlTy [] [] { Public -> (Unit + $ t) }

def empty :=
  Owl [] [] []{
    fix f (x) (ı1 *)
  }

theorem ht_empty :
  forall (t : Owl.ty 0 0),
  ( · ; -- Phi
    · ; -- Delta
    · ; -- Gamma
    · ;
   ($ empty) ⊢  -- Tm
   ($ (MapOf t))) -- Ty
   :=
  by
  intro t
  tc (
    solve_all_constraints
  )

-- non functional
def eq : Owl.op :=
  fun (_ _ : Owl.binary) =>
    Owl.Dist.ret (Owl.binary.bend)

def insert_tm := --TEMP
  Owl [] [] [] {
    λmap . λx . λv . λy . if (⟨eq⟩(["111"], ["111"])) then (ı1 *) else (ı1 *)
  }

def insert_ty (t : Owl.ty 0 0) :=
  OwlTy [] [] {
    (Public -> (Unit + ($ t))) -> Public -> ($ t) -> Public -> (Unit + ($ t))
  }

theorem ht_zero :
  ( · ; -- Phi
    · ; -- Delta
    · ; -- Gamma
    · ;
   (zero (["111"] : (Data ⟨Owl.L.bot⟩))) ⊢  -- Tm
   (Public)) -- Ty
   :=
  by
  tc (
    solve_all_constraints
  )

theorem prove_corr :
  phi_psi_entail_corr empty_phi [] (Owl.corruption.corr (Owl.label.latl Owl.L.bot)) := by
  unfold phi_psi_entail_corr
  intro pm C vpm Csp
  check_corr vpm C Csp

-- VERY NICE!
theorem prove_corr_harder :
  phi_psi_entail_corr (pcons (.geq, (.var_label ⟨0, by omega⟩)) (pcons (.geq, (.latl Owl.L.bot)) empty_phi))
                      ((.corr (.latl Owl.L.bot)) :: (.corr (.var_label ⟨1, by omega⟩)) :: []) (Owl.corruption.corr (.var_label ⟨1, by omega⟩)) := by
  intro pm C vpm Csp
  check_corr vpm C Csp

-- VERY NICE!
theorem prove_corr_harder2 :
  phi_psi_entail_corr (pcons (.geq, (.var_label ⟨0, by omega⟩)) (pcons (.geq, (.latl Owl.L.bot)) empty_phi))
                      ((.corr (.latl Owl.L.bot)) :: (.corr (.var_label ⟨1, by omega⟩)) :: []) (Owl.corruption.corr (.latl Owl.L.bot)) := by
  unfold phi_psi_entail_corr
  intro pm C vpm Csp
  check_corr vpm C Csp

theorem ht_eq :
  ( · ; -- Phi
    · ; -- Delta
    · ; -- Gamma
    · ;
   (⟨eq⟩(["111"], ["111"])) ⊢  -- Tm
   (Public)) -- Ty
   :=
  by
  tc_man (
    try simp
    intro pm C vpm Csp
    check_corr vpm C Csp
  )

-- testing a contradiction case now
theorem ht_if_eq :
  ( (x ⊑ ⟨Owl.L.bot⟩, y) ; -- Phi
    (¬corr(y), corr(y)) ; -- Psi
    · ; -- Delta
    · ; -- Gamma
   (if (⟨eq⟩(["111"], ["111"]) : (Data x)) then ["111"] else ["111"]) ⊢  -- Tm
   (Public)) -- Ty
   :=
  by tc (try grind)

theorem ht_insert :
  forall (t : Owl.ty 0 0),
  ( · ; -- Phi
    · ; -- Delta
    (a <: Any) ; -- Gamma
    · ;
   (λmap . λx . λv . λy . if (⟨eq⟩(y, x)) then (ı2 v) else (map [y])) ⊢  -- Tm
   (Public -> (Unit + a)) -> Public -> a -> Public -> (Unit + a)) -- Ty
   :=
  by
  intro t
  tc (try grind)

theorem ht_insert_part :
  ( · ; -- Phi
    · ; -- Delta
    (a <: Any) ; -- Gamma
    · ;
   (λmap . map [*]) ⊢  -- Tm
   (Unit -> (Unit + a)) -> (Unit + a)) -- Ty
   :=
  by
  tc (
    solve_all_constraints
  )

-- example of a how tc_man lets you know when typing fails
theorem ht_unit :
  ( · ; -- Phi
    · ; -- Delta
    · ; -- Gamma
    · ;
   * ⊢  -- Tm
   (Data ⟨Owl.L.bot⟩)) -- Ty
   :=
  by
  tc_man (
    try simp
    sorry
  )

theorem ht_if_corr :
  ( x ; -- Phi
    (¬corr(x)) ; -- Delta
    · ; -- Gamma
    · ;
   (if corr (x) then * else *) ⊢  -- Tm
   Unit) -- Ty
   :=
  by
  tc_man (
    auto_solve
  )
