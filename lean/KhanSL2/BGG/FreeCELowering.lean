module

public import KhanSL2.BGG.FreeCEDegree
public import KhanSL2.BGG.PolynomialKoszulFiltration

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The full CE correction strictly lowers the actual PBW-plus-exterior length filtration. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.FreeCE

open PolynomialKoszul

private theorem contract_monomial_degree (m : Mode) (t : Finset Mode) (ht : 0 < t.card) :
    PositiveCE.degreeOp (PositiveCE.contract m (FiniteExterior.monomial t)) =
      ((t.card - 1 : ℕ) : ℂ) • PositiveCE.contract m (FiniteExterior.monomial t) := by
  have h := exteriorDegree_contract m (FiniteExterior.monomial t)
  rw [exteriorDegree_monomial, map_smul,
    show t.card = (t.card - 1) + 1 from (Nat.sub_add_cancel (Nat.succ_le_of_lt ht)).symm] at h
  simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul] at h
  exact add_right_cancel h

private theorem boundary_monomial_degree (t : Finset Mode) (ht : 0 < t.card) :
    PositiveCE.degreeOp (PositiveCE.boundary (FiniteExterior.monomial t)) =
      ((t.card - 1 : ℕ) : ℂ) • PositiveCE.boundary (FiniteExterior.monomial t) := by
  rw [PositiveCE.degreeOp_boundary, exteriorDegree_monomial, map_smul,
    show t.card = (t.card - 1) + 1 from (Nat.sub_add_cancel (Nat.succ_le_of_lt ht)).symm]
  simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_sub_cancel_right, Nat.add_sub_cancel]

/-- Each genuine tensor-basis vector has a CE-minus-Koszul error of strictly lower total length. -/
theorem polynomialPerturbation_basis (b : PolynomialKoszul.BasisIndex) :
    (polynomialDifferential - PolynomialKoszul.d) (PolynomialKoszul.basis b) ∈
      filtration (totalLength b) := by
  obtain ⟨s,t⟩ := b
  rw [polynomialDifferential_sub_koszul_basis]
  by_cases ht : t.card = 0
  · rw [Finset.card_eq_zero.mp ht]
    simp only [Finset.sum_empty, show FiniteExterior.monomial (∅ : Finset Mode) = (1 : Cochain) from rfl,
      PositiveCE.boundary_one, TensorProduct.tmul_zero, add_zero]
    exact (filtration _).zero_mem
  · have htpos : 0 < t.card := Nat.pos_of_ne_zero ht
    apply (filtration _).add_mem
    · apply (filtration _).sum_mem
      intro m _
      apply tmul_mem_filtration_of_exterior_degree
        (q := s.sum (fun _ k => k)) (r := t.card - 1)
        (polynomialEquiv_right_error s m) (contract_monomial_degree m t htpos)
      exact Nat.add_lt_add_left (Nat.sub_lt htpos (by decide : 0 < 1)) _
    · have hp : MvPolynomial.monomial s (1 : ℂ) ∈
          MvPolynomial.restrictTotalDegree Mode ℂ (s.sum fun _ n => n) := by
        rw [MvPolynomial.mem_restrictTotalDegree, MvPolynomial.totalDegree_monomial s one_ne_zero]
      apply tmul_mem_filtration_of_exterior_degree hp (boundary_monomial_degree t htpos)
      dsimp only [totalLength]
      simp only [Finsupp.sum]
      omega

/-- The concrete perturbation strictly lowers the exhaustive strict-length filtration. -/
theorem polynomialPerturbation_lowers (n : ℕ) (u : PolynomialKoszul.Chain)
    (hu : u ∈ filtration (n + 1)) :
    (polynomialDifferential - PolynomialKoszul.d) u ∈ filtration n := by
  rw [PolynomialKoszul.eq_sum_basis u]
  simp only [map_sum, map_smul]
  apply (filtration n).sum_mem
  intro b hb
  apply (filtration n).smul_mem
  have hlength : totalLength b < n + 1 := hu hb
  exact filtration_mono (Nat.le_of_lt_succ hlength) (polynomialPerturbation_basis b)

end KhanSL2.BGG.FreeCE
