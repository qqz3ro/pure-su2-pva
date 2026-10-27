module

public import KhanSL2.Macdonald.ChainModel
public import KhanSL2.Macdonald.CurrentActionWeight
public import KhanSL2.Macdonald.RestrictedTranspose
public import KhanSL2.BGG.PositiveCEGrading

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The genuine symmetric-coefficient CE boundary preserves the finite weight
and symmetric-degree blocks used for restricted duality. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Macdonald

@[simp] theorem basis_repr_tmul (p : Poly) (ω : Exterior) (d : Exponent) (t : Finset Mode) :
    basis.repr (p ⊗ₜ[ℂ] ω) (d,t) = ω t * p.coeff d := by
  change ((MvPolynomial.basisMonomials Mode ℂ).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (Finset Mode) ℂ Exterior)).repr
      (p ⊗ₜ[ℂ] ω) (d,t) = _
  rw [Module.Basis.tensorProduct_repr_tmul_apply]
  rfl

theorem tmul_mem_weightDegreePiece {w e s : ℕ} {p : Poly} {ω : Exterior}
    (hpw : ∀ d ∈ p.support, polynomialWeight d = w)
    (hps : ∀ d ∈ p.support, polynomialDegree d = s)
    (hω : ∀ t ∈ ω.support, exteriorWeight t = e) :
    p ⊗ₜ[ℂ] ω ∈ weightDegreePiece (w+e) s := by
  intro b hb
  obtain ⟨d,t⟩ := b
  have hn := Finsupp.mem_support_iff.mp hb
  change basis.repr (p ⊗ₜ[ℂ] ω) (d,t) ≠ 0 at hn
  rw [basis_repr_tmul] at hn
  have hd : d ∈ p.support := MvPolynomial.mem_support_iff.mpr (by
    intro hz; apply hn; rw [hz, mul_zero])
  have ht : t ∈ ω.support := Finsupp.mem_support_iff.mpr (by
    intro hz; apply hn; rw [hz, zero_mul])
  exact ⟨by simp only [weight, hpw d hd, hω t ht], hps d hd⟩

theorem polynomial_homogeneous_iff (s : ℕ) (p : Poly) :
    p.IsHomogeneous s ↔ ∀ d ∈ p.support, polynomialDegree d = s := by
  simp only [MvPolynomial.IsHomogeneous, MvPolynomial.IsWeightedHomogeneous,
    MvPolynomial.mem_support_iff, Finsupp.weight_apply, Pi.one_apply, nsmul_eq_mul, mul_one,
    polynomialDegree]
  constructor
  · intro h d hd
    exact h hd
  · intro h d hd
    exact h d hd

theorem boundary_monomial_weight (t e : Finset Mode)
    (he : e ∈ (BGG.PositiveCE.boundary (FiniteExterior.monomial t)).support) :
    exteriorWeight e = exteriorWeight t := by
  by_cases ht : t.card = 0
  · have hz : t = ∅ := Finset.card_eq_zero.mp ht
    subst t
    have hone : FiniteExterior.monomial (∅ : Finset Mode) = (1 : Exterior) := rfl
    simp only [hone, BGG.PositiveCE.boundary_one, Finsupp.support_zero,
      Finset.notMem_empty] at he
  · have hm : FiniteExterior.monomial t ∈
        BGG.PositiveCE.piece ((t.card-1)+1) (exteriorWeight t) := by
      apply Finsupp.single_mem_supported ℂ 1
      exact ⟨by omega, rfl⟩
    exact (BGG.PositiveCE.boundary_mem_piece hm he).2

theorem chainBoundary_basis_mem (b : BasisIndex) :
    chainBoundary (basis b) ∈ weightDegreePiece (weight b) (symmetricDegree b) := by
  classical
  obtain ⟨d,t⟩ := b
  rw [basis_apply]
  have hsupp : FiniteExterior.supportModes (FiniteExterior.monomial t) ⊆ t := by
    apply (BGG.FreeCE.supportModes_subset_iff t _).mpr
    exact FiniteExterior.monomial_mem_generatorsIn _ _ (by intro i hi; exact hi)
  rw [chainBoundary_tmul t _ _ hsupp]
  have hpw : ∀ e ∈ (MvPolynomial.monomial d (1 : ℂ)).support,
      polynomialWeight e = polynomialWeight d := by
    intro e he
    have h := MvPolynomial.support_monomial_subset he
    simpa only [Finset.mem_singleton] using congrArg polynomialWeight (Finset.mem_singleton.mp h)
  have hps : ∀ e ∈ (MvPolynomial.monomial d (1 : ℂ)).support,
      polynomialDegree e = polynomialDegree d := by
    intro e he
    exact congrArg polynomialDegree (Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he))
  apply Submodule.sub_mem
  · exact tmul_mem_weightDegreePiece hpw hps (boundary_monomial_weight t)
  · apply Submodule.sum_mem
    intro m hm
    have hactw := currentAction_mode_mem_weight (m.index+1) m.color
      ((mem_polynomialWeightPiece _ _).mpr hpw)
    have hacts := symmetricDerivation_preserves_degree
      (LieAlgebra.ad ℂ BGG.Current (BGG.mode (m.index+1) (MatrixSL2.color m.color)))
      ((polynomial_homogeneous_iff _ _).mpr hps)
    have he : exteriorWeight (t.erase m) + (m.index+1) = exteriorWeight t :=
      Finset.sum_erase_add _ _ hm
    rw [BGG.PositiveCE.contract, FiniteExterior.contraction_monomial, if_pos hm,
      TensorProduct.tmul_smul]
    apply Submodule.smul_mem
    have hmon : ∀ e ∈ (FiniteExterior.monomial (t.erase m) : Exterior).support,
        exteriorWeight e = exteriorWeight (t.erase m) := by
      intro e he'
      have h := Finsupp.support_single_subset he'
      exact congrArg exteriorWeight (Finset.mem_singleton.mp h)
    have h := tmul_mem_weightDegreePiece
      ((mem_polynomialWeightPiece _ _).mp hactw)
      ((polynomial_homogeneous_iff _ _).mp hacts) hmon
    have hsum : polynomialWeight d + (m.index+1) + exteriorWeight (t.erase m) =
        weight (d,t) := by
      change polynomialWeight d + (m.index+1) + exteriorWeight (t.erase m) =
        polynomialWeight d + exteriorWeight t
      omega
    simpa only [BGG.FreeCE.lieGenerator, BGG.positiveMode_coe, hsum, symmetricDegree] using h

/-- The finite block condition required by the genuine restricted transpose. -/
theorem chainBoundary_preservesWeightDegree : PreservesWeightDegree chainBoundary := by
  intro w s u hu
  rw [eq_sum_basis u, map_sum]
  apply Submodule.sum_mem
  intro b hb
  rw [map_smul]
  apply Submodule.smul_mem
  obtain ⟨hw,hs⟩ := (mem_weightDegreePiece_iff u w s).mp hu b hb
  simpa only [hw,hs] using chainBoundary_basis_mem b

/-- Restricted CE coboundary, defined from the actual coefficient chain complex. -/
def differential : Module.End ℂ W := restrictedTranspose chainBoundary

theorem differential_pairing (u v : W) : pairing (differential u) v = pairing u (chainBoundary v) :=
  pairing_restrictedTranspose chainBoundary chainBoundary_preservesWeightDegree u v

/-- This square-zero proof has no Macdonald or cohomological hypothesis. -/
theorem differential_square_zero (u : W) : differential (differential u) = 0 :=
  restrictedTranspose_square_zero chainBoundary chainBoundary_preservesWeightDegree
    chainBoundary_comp_self u

end KhanSL2.Macdonald
