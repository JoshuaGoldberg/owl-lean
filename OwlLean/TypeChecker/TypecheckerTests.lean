import OwlLean.TypeChecker.OwlTypecheck
import OwlLean.OwlLang.Owl
import OwlLean.TypeChecker.OwlParser

/-!
Typechecker regression tests using `#tc` (empty Φ, Ψ, Δ, Θ, Γ). Each `#tc` elaborates a
closed term and checks it against the given type via `TcSimple.infer`.

We cover System F (`Λ` / type instantiation `[τ]`), subtyping (sums, products, unions, `Public`),
refinement carriers (`RData`, `∃ α.`, `Λr` / `[{re}]`), and information-flow–flavoured checks
(`Public`, `Data ⊥`, `sync`).

Known gaps (no active `#tc` here; the typechecker or empty sequent does not support them yet):

- `union_elim` with a `Public` annotation on the scrutinee does not yield a union; an `ı`-sum
  annotation is required.
- Label polymorphism (`Λβ`) needs a non-empty Φ (`#tc_with`) to discharge `LblEntails`.
- `if corr(…)` / `corr (…) ? …` needs corruption/Ψ context the plain `#tc` elaborator does not set.
- General intersection reasoning on annotations is not available for the forms we tried.
-/

-- Information flow / `Public`: constant bitstrings carry `RData` and subtype to `Public`.
#tc tc_bitstring_sub_public := ⊢ { "32" } : Public


-- Base type `unit`.
#tc tc_unit := ⊢ { () } : unit

-- `sync` requires a `Public` scrutinee and yields `Public`.
#tc tc_sync := ⊢ { sync "ok" } : Public

-- Boolean-style `if` on `Public`, branches must agree up to subtyping.
#tc tc_if_unit := ⊢ { if "0" then () else () } : unit

-- Let-binding inherits refinements / hypotheses from the bound expression where supported.
#tc tc_let_public := ⊢ { let y = "a" in y } : Public

-- Refined data type: explicit `RData` with a constant refinement expression.
#tc tc_rdata_explicit := ⊢ { "hello" } : RData ⊥ [ "hello" ]

-- Subtyping on products: pair of bitstrings checked against `Public * Public`.
#tc tc_pair_public_prod := ⊢ { ⟨ "a", "b" ⟩ } : Public * Public

-- Subtyping on sums: inject left with an annotation giving the full sum type.
#tc tc_inl_sum := ⊢ { (ı1 "x" : Public + unit) } : Public + unit

-- Case split on a sum; both branches return `Public`.
#tc tc_case_sum :=
  ⊢ { case (ı1 "x" : Public + unit) with | inl _ => "L" | inr _ => "R" } : Public

-- Subtyping on unions: `union_elim` needs a real sum annotated into `t₁ ∪ t₂`.
#tc tc_union_elim :=
  ⊢ { union_elim z = ("a" : (Public ∪ Public)) in z } : Public

-- System F: type-polymorphic identity.
#tc tc_poly_id := ⊢ { (Λ X . ((λ (x : X) : X => x) : (X -> X))) } : ∀ X <: Any . X -> X

-- `Λ` must be ascribed before `[τ]` application: with `exp = none`, `tlam` does not get a `∀`.
#tc tc_tapp_poly_id :=
  ⊢ { ((((Λ X . ((λ (x : X) : X => x) : (X -> X))) : (∀ X <: Any . X -> X))[Public]) "hi") } :
    Public

-- Refinement quantification: pack an existential witness.
#tc tc_pack_exists := ⊢ { pack (Public, ("w" : Public)) } : ∃ α <: Public . α

-- Existential unpack: witness type `Public`, body uses the packed value.
#tc tc_unpack_exists :=
  ⊢ { unpack (pack (Public, ("m" : Public)) : ∃ α <: Public. α  ) as (α, x) in x } : Public

/-
#tc tc_rapp_poly_rdata_failed :=
  ⊢ { ((((Λr r . (("bits" : RData ⊥ [r]))) : (∀ r . RData ⊥ [r]))[{ "k" }])) } : RData ⊥ [ "k" ]
-- Fails: checker asks for a side condition `const "bits" == rexp.var 0` when relating the
--   concrete bitstring refinement to the abstract `r` after substitution; the literal `"bits"`
--   cannot be shown equal to the formal refinement parameter instantiated at `"k"`.
-/

#tc tc_rapp_admit :=
  ⊢ { ((((Λr r . ((admit : RData ⊥ [r]))) : (∀ r . RData ⊥ [r]))[{ "k" }])) } : RData ⊥ [ "k" ]

-- Simple function type (annotated λ).
#tc tc_fun_id_public :=
  ⊢ { ((λ (x : Public) : Public => x) : (Public -> Public)) } : Public -> Public

-- Application of the annotated identity function.
#tc tc_app_id :=
  ⊢ { (((λ (x : Public) : Public => x) : (Public -> Public)) "z") } : Public

-- `Data ⊥` accepts public-style bitstrings via `RData <: Data`.
#tc tc_string_data := ⊢ { "secret" } : Data ⊥


-- Reference: allocate and read back.
#tc tc_ref_alloc_read := ⊢ { let r = alloc ("v" : Public) in !r } : Public

-- Reference: assign then read.
#tc tc_ref_assign :=
  ⊢ { let r = alloc ("0" : Public) in (r := "1") ; !r } : Public

-- `Maybe τ` desugars to `τ + unit`; the left injection must carry `τ`, not `unit`.
#tc tc_maybe_inl := ⊢ { (ı1 "ok" : Public + unit) } : Maybe Public

-- Top-like supertype: bitstrings are also `Any`.
#tc tc_string_any := ⊢ { "y" } : Any

-- Refined type syntax: supertype `Public` with a trivially true equation on the value.
#tc tc_refined_public := ⊢ { let x = "1" in rpack ("1", x) } : ∃r. RData ⊥ [r]
