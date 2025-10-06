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
#check label_parse(⟨ bot ⟩)
#check label_parse(⟨ low ⟩)

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
#eval term_parse(* [[[ z ⊔ y ]]])
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
#eval Owl {
  *
}

#eval Owl {
  fix factorial ( n )
    if n then
      ⟨ mul_op ⟩ ( n , factorial [ ⟨ sub_op ⟩ ( n , 1 ) ] )
    else
      1
}

#eval Owl {
  ( fix loop ( state )
    case (! state) in
      cont => loop [ alloc cont ]
    | done => *
  ) [ alloc ⟨ ı1 * , * ⟩ ]
}

#eval Owl {
  unpack (pack (Unit, *)) as (a, x) in
    case π1 x in
      x => ⟨ ı1 x , π2 x ⟩
    | y => ⟨ ı2 y , π2 x ⟩
}

#eval Owl {
  let x = 5 in
    x [x]
}

def test_embed (e : Owl.tm 0 0 0) : Owl.tm 0 0 0 :=
  Owl {
    ⟨$ e , $ e⟩
  }

def test_lam : Owl.tm 0 0 0 :=
  Owl {
    Λ x . * [[x]]
  }

#eval Owl {
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

def ENC (betaK betaM betaC : Owl.label 0) :=
  OwlTy {
    ∃ alphaK <: (Data ($ betaK)) . alphaK * (if ($ betaK ⊑ $ betaC)
                                             then (Data ($ betaC) * Data ($ betaC) -> Data ($ betaC))
                                             else (alphaK * Data ($ betaM) -> Data ($ betaC)))
  }

def Enc (betaK betaC : Owl.label 0) :=
  Owl {
    let k = ⟨genKey⟩ (*, *) in
    let enc = if ($ betaK ⊑ $ betaC) then λx . ⟨enc⟩ (π1 x, π2 x) else λx . ⟨rand⟩(zero π2 x, *) in
    pack (Unit, ⟨k, enc⟩) -- Unit is temp
  }

def P (l1 l2 l3 adv : Owl.label 0) :=
  Owl {
    unpack $ (Enc l1 adv) as (alpha1, p1) in
    unpack $ (Enc l2 adv) as (alpha1, p2) in
    let n = sync ((π2 p1) [⟨π1 p1, π1 p2⟩]) in
            sync ((π2 p2) [⟨π1 p2, ["010101"]⟩])
  }

-- TC tests

#reduce infer empty_sigma empty_phi empty_delta empty_gamma (.unpack (.annot packed_unit (.ex .Any .Unit)) .skip) (.some .Unit)

def owl_ty :=
  OwlTy {
    Unit -> Unit
  }

theorem lambda_identity_unit_2  :
          has_type empty_sigma Wempty_phi empty_delta empty_gamma (.fixlam (.var_tm ⟨1, by omega⟩)) (owl_ty) := by
  tc (try grind)
