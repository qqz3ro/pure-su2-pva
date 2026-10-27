module

public import KhanSL2.BGG.TermPBWFree

@[expose] public section

/-! Reconstructing full-current module morphisms from the two PBW factors. -/

noncomputable section

namespace KhanSL2.BGG

/-- Positive-enveloping and constant equivariance together imply full enveloping equivariance. -/
theorem term_map_smul_of_positive_constant {p q : ℕ}
    (f : Term p →ₗ[ℂ] Term q)
    (hpos : ∀ (u : PositiveEnveloping) (v : Term p), f (u • v) = u • f v)
    (hconst : ∀ (x : G) (v : Term p),
      f (constGenerator x • v) = constGenerator x • f v)
    (a : Enveloping) (v : Term p) : f (a • v) = a • f v := by
  induction a using UE.induction ℂ Current generalizing v with
  | scalar r => simp only [algebraMap_smul, map_smul]
  | generator x =>
    let u : positive := ⟨x - constant (evalZero x), sub_constant_mem_positive x⟩
    have hx : UniversalEnvelopingAlgebra.ι ℂ x =
        positiveFactor (UniversalEnvelopingAlgebra.ι ℂ u) + constGenerator (evalZero x) := by
      rw [positiveFactor_iota]
      change UniversalEnvelopingAlgebra.ι ℂ x =
        UniversalEnvelopingAlgebra.ι ℂ (x - constant (evalZero x)) +
          UniversalEnvelopingAlgebra.ι ℂ (constant (evalZero x))
      rw [← map_add, sub_add_cancel]
    rw [hx, add_smul, map_add, add_smul, hconst]
    exact congrArg (· + constGenerator (evalZero x) • f v)
      (hpos (UniversalEnvelopingAlgebra.ι ℂ u) v)
  | add a b ha hb => rw [add_smul, map_add, ha, hb, add_smul]
  | mul a b ha hb => rw [mul_smul, ha, hb, mul_smul]

/-- A map with the two concrete PBW equivariances is an actual current-module morphism. -/
def termMapOfPositiveConstant {p q : ℕ}
    (f : Term p →ₗ[ℂ] Term q)
    (hpos : ∀ (u : PositiveEnveloping) (v : Term p), f (u • v) = u • f v)
    (hconst : ∀ (x : G) (v : Term p),
      f (constGenerator x • v) = constGenerator x • f v) :
    Term p →ₗ[Enveloping] Term q where
  toFun := f
  map_add' := f.map_add
  map_smul' := term_map_smul_of_positive_constant f hpos hconst

@[simp] theorem termMapOfPositiveConstant_apply {p q : ℕ}
    (f : Term p →ₗ[ℂ] Term q) (hpos) (hconst) (v : Term p) :
    termMapOfPositiveConstant f hpos hconst v = f v := rfl

end KhanSL2.BGG
