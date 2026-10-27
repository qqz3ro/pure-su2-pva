module

public import KhanSL2.BGG.CurrentPBW
public import KhanSL2.BGG.InducedFactorization
public import KhanSL2.BGG.TermGrading
public import TauCeti.Algebra.Lie.UniversalEnveloping.Module

@[expose] public section

/-! Relative PBW for the actual induced BGG terms. -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG

/-- The actual relative PBW equivalence for every standard coefficient module. -/
def positiveTensorEquivTerm (p : ℕ) :
    PositiveEnveloping ⊗[ℂ] Coefficient p ≃ₗ[ℂ] Term p := by
  letI := TauCeti.UniversalEnvelopingAlgebra.asModule ℂ G (Coefficient p)
  letI := TauCeti.UniversalEnvelopingAlgebra.isScalarTower_asModule ℂ G (Coefficient p)
  exact Induced.Split.equiv constGenerator (coefficientAction p) positiveFactor constantFactor
    currentPBW currentPBW_tmul constantFactor_iota
    (TauCeti.UniversalEnvelopingAlgebra.asModule_ι_smul ℂ G (Coefficient p))

/-- The equivalence is the specified action map, not an arbitrary vector-space equivalence. -/
@[simp] theorem positiveTensorEquivTerm_tmul (p : ℕ) (u : PositiveEnveloping) (v : Coefficient p) :
    positiveTensorEquivTerm p (u ⊗ₜ[ℂ] v) = positiveFactor u • termGenerator p v := by
  let := TauCeti.UniversalEnvelopingAlgebra.asModule ℂ G (Coefficient p)
  let := TauCeti.UniversalEnvelopingAlgebra.isScalarTower_asModule ℂ G (Coefficient p)
  exact Induced.Split.equiv_tmul constGenerator (coefficientAction p) positiveFactor constantFactor
    currentPBW currentPBW_tmul constantFactor_iota
    (TauCeti.UniversalEnvelopingAlgebra.asModule_ι_smul ℂ G (Coefficient p)) u v

@[simp] theorem positiveTensorEquivTerm_one_tmul (p : ℕ) (v : Coefficient p) :
    positiveTensorEquivTerm p ((1 : PositiveEnveloping) ⊗ₜ[ℂ] v) = termGenerator p v := by
  rw [positiveTensorEquivTerm_tmul, map_one, one_smul]

/-- PBW intertwines the actual positive-current enveloping-algebra action. -/
theorem positiveTensorEquivTerm_smul (p : ℕ) (u : PositiveEnveloping)
    (t : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    positiveTensorEquivTerm p (u • t) = positiveFactor u • positiveTensorEquivTerm p t := by
  induction t using TensorProduct.inductionOn with
  | tmul b v =>
    rw [TensorProduct.smul_tmul', positiveTensorEquivTerm_tmul, positiveTensorEquivTerm_tmul]
    change positiveFactor (u * b) • termGenerator p v = _
    rw [map_mul, mul_smul]
  | add t s ht hs => simp only [smul_add, map_add, ht, hs]

end KhanSL2.BGG
