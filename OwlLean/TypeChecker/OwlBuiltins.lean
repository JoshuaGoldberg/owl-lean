import Std.Data.TreeMap

notation "OwlVal" => List Char

@[simp]
abbrev Nat.toOwlVal : Nat -> List Char :=
  fun x =>
    Nat.toDigits 10 x

@[simp]
abbrev Nat.ofOwlVal : List Char -> Nat :=
  fun x =>
    Nat.ofDigitChars 10 x 0

attribute [simp] Nat.ofDigitChars
attribute [simp] Nat.toDigits

@[grind ., simp]
theorem Nat.ofOwlVal_toOwlVal (x : Nat) : Nat.ofOwlVal (Nat.toOwlVal x) = x := by
  unfold Nat.toOwlVal Nat.ofOwlVal
  rw [Nat.ofDigitChars_toDigits]
  simp
  simp




@[simp]
def builtinFunc : List (String × (OwlVal -> OwlVal -> OwlVal)) :=
  [
    ("concat", fun x y => x ++ y),
    ("splitL", fun (x : OwlVal) (y : OwlVal) =>
          x.take (Nat.ofOwlVal y)
    ),
    ("splitR", fun (x : OwlVal) (y : OwlVal) =>
          (x.drop (Nat.ofOwlVal y))
    )
  ]

opaque owl_f_interp' : String -> OwlVal -> OwlVal -> OwlVal

@[simp]
def owl_f_interp (s : String) (x y : OwlVal) : OwlVal :=
  match List.lookup s builtinFunc with
  | some f => f x y
  | none => owl_f_interp' s x y


attribute [simp] List.lookup
