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
def OwlVal.binop (f : OwlVal -> OwlVal -> OwlVal) : List OwlVal -> OwlVal :=
  fun xs =>
    match xs with
    | x :: y :: [] => f x y
    | _ => []

@[simp]
def builtinFunc : List (String × (List OwlVal -> OwlVal)) :=
  [
    ("concat", OwlVal.binop fun x y => x ++ y),
    ("splitL", OwlVal.binop fun (x : OwlVal) (y : OwlVal) =>
          x.take (Nat.ofOwlVal y)
    ),
    ("splitR", OwlVal.binop fun (x : OwlVal) (y : OwlVal) =>
          (x.drop (Nat.ofOwlVal y))
    ),
    ("eq", OwlVal.binop fun (x : OwlVal) (y : OwlVal) => if x = y then "1".toList else "0".toList),
  ]

opaque owl_f_interp' : String -> List OwlVal -> OwlVal

@[simp]
def owl_f_interp (s : String) (xs : List OwlVal) : OwlVal :=
  match List.lookup s builtinFunc with
  | some f => f xs
  | none => owl_f_interp' s xs


attribute [simp] List.lookup
