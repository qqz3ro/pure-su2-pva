module

public import KhanSL2.Macdonald.RootFreeBidegree
public import KhanSL2.Macdonald.StrongBridgeHomologyPairing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The explicit bidegree generator embeddings agree with the previously
specified free-coordinate equivalence. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open SymmetricFamily

@[simp] theorem strongFreeUncoloredEquiv_symm_single_val (b : FreeMonomialIndex) :
    (strongFreeUncoloredEquiv.symm (Finsupp.single b 1)).val =
      StrongMacdonald.mono (rootEvenExponent b.1) (b.2.map rootOddModeEmbedding) := by
  change (strongFreeCoordinateEquiv.symm
    (Finsupp.domLCongr (R := ℂ) strongFreeIndexEquiv.symm (Finsupp.single b 1))).val = _
  rw [Finsupp.domLCongr_single,strongFreeCoordinateEquiv_symm_single_val]
  rw [strongFreeIndexEquiv_symm_val]

/-- The bidegree source basis maps to its actual free monomial. -/
theorem rootFreeBidegreeRaw_basis (q r : ℕ)
    (t : Set.powersetCard ℕ q) (e : DegreeExponent ℕ r) :
    rootFreeBidegreeRaw q r
      (((Polynomial.basisMonomials ℂ).exteriorPower q t) ⊗ₜ[ℂ] (rootEvenPowerBasis r e)) =
        StrongMacdonald.mono (rootEvenExponent e.val) (t.val.map rootOddModeEmbedding) := by
  rw [rootFreeBidegreeRaw_tmul]
  have he : (rootEvenPowerBasis r e).val = MvPolynomial.monomial e.val 1 := by
    change ((rootEvenExponentEquiv r).symm (Finsupp.single e 1)).val = _
    exact rootEvenExponentEquiv_symm_single r e 1
  rw [he,rootEvenEmbedding_monomial]
  change StrongMacdonald.mono (rootEvenExponent e.val) ∅ *
    StrongMacdonald.ofExt (rootOddPowerEmbedding q
      ((Polynomial.basisMonomials ℂ).exteriorPower q t)) = _
  rw [rootOddPowerEmbedding_basis,StrongMacdonald.mono,StrongMacdonald.ofExt_apply,
    AddMonoidAlgebra.single_mul_single,add_zero]
  change AddMonoidAlgebra.single _ ((1 : FiniteExterior.Exterior BGG.PositiveCE.Mode) * _) = _
  rw [one_mul]
  rfl

theorem rootFreeBidegreeMap_source_single (q r : ℕ) (b : FreeBidegreeIndex q r) :
    rootFreeBidegreeMap q r (freeBidegreeSourceEquiv q r (Finsupp.single b 1)) =
      strongFreeUncoloredEquiv.symm (Finsupp.single b.val 1) := by
  apply Subtype.ext
  change rootFreeBidegreeRaw q r (freeBidegreeSourceEquiv q r (Finsupp.single b 1)) = _
  simp only [freeBidegreeSourceEquiv,LinearEquiv.trans_apply,Finsupp.domLCongr_single,
    Module.Basis.repr_symm_single,one_smul]
  rw [Module.Basis.tensorProduct_apply',rootFreeBidegreeRaw_basis,
    strongFreeUncoloredEquiv_symm_single_val]
  rfl

/-- Extend fixed-bidegree coordinates by zero to all free monomials. -/
def freeBidegreeCoordinateInclusion (q r : ℕ) :
    (FreeBidegreeIndex q r →₀ ℂ) →ₗ[ℂ] (FreeMonomialIndex →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (fun b => b.val)

/-- The actual product embedding has the exact specified finite coordinates. -/
theorem rootFreeBidegreeMap_coordinates (q r : ℕ) (x : FreeBidegreeIndex q r →₀ ℂ) :
    strongFreeUncoloredEquiv (rootFreeBidegreeMap q r (freeBidegreeSourceEquiv q r x)) =
      freeBidegreeCoordinateInclusion q r x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single b c =>
    have h : Finsupp.single b c = c • Finsupp.single b (1 : ℂ) := by simp
    rw [h]
    simp only [map_smul,rootFreeBidegreeMap_source_single,LinearEquiv.apply_symm_apply]
    simp [freeBidegreeCoordinateInclusion]

end KhanSL2.Macdonald
