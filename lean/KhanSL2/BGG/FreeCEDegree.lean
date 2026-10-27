module

public import KhanSL2.BGG.FreeCEPBWAugmentation
public import KhanSL2.BGG.PolynomialKoszulGrading
public import KhanSL2.BGG.PositiveCEGrading

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual free CE differential lowers exterior degree in PBW polynomial coordinates. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.FreeCE

open PolynomialKoszul

/-- The specified free CE operator lowers exterior degree by exactly one. -/
theorem exteriorDegree_polynomialDifferential (u : PolynomialKoszul.Chain) :
    exteriorDegree (polynomialDifferential u) + polynomialDifferential u =
      polynomialDifferential (exteriorDegree u) := by
  have heq : exteriorDegree.comp polynomialDifferential + polynomialDifferential =
      polynomialDifferential.comp exteriorDegree := by
    apply PolynomialKoszul.basis.ext
    rintro ⟨s,t⟩
    simp only [LinearMap.add_apply, LinearMap.comp_apply, exteriorDegree_basis, map_smul]
    rw [PolynomialKoszul.basis_apply, polynomialDifferential_tmul_monomial]
    let P := MvPolynomial.monomial s (1 : ℂ)
    let B := P ⊗ₜ[ℂ] PositiveCE.boundary (FiniteExterior.monomial t)
    let A (m : Mode) := polynomialEquiv (polynomialEquiv.symm P * ueGenerator m) ⊗ₜ[ℂ]
      PositiveCE.contract m (FiniteExterior.monomial t)
    have hA (m : Mode) : exteriorDegree (A m) + A m = (t.card : ℂ) • A m := by
      dsimp only [A]
      rw [exteriorDegree_tmul, ← TensorProduct.tmul_add, exteriorDegree_contract,
        exteriorDegree_monomial, map_smul, TensorProduct.tmul_smul]
    have hB : exteriorDegree B + B = (t.card : ℂ) • B := by
      dsimp only [B]
      rw [exteriorDegree_tmul, ← TensorProduct.tmul_add, PositiveCE.degreeOp_boundary,
        sub_add_cancel, exteriorDegree_monomial, map_smul, TensorProduct.tmul_smul]
    have hsum : exteriorDegree (∑ m ∈ t, A m) + (∑ m ∈ t, A m) =
        (t.card : ℂ) • ∑ m ∈ t, A m := by
      rw [map_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
      exact Finset.sum_congr rfl fun m _ => hA m
    change exteriorDegree ((∑ m ∈ t, A m) + B) + ((∑ m ∈ t, A m) + B) =
      (t.card : ℂ) • ((∑ m ∈ t, A m) + B)
    calc
      _ = (exteriorDegree (∑ m ∈ t, A m) + (∑ m ∈ t, A m)) +
          (exteriorDegree B + B) := by rw [map_add]; abel
      _ = _ := by rw [hsum, hB, smul_add]
  exact LinearMap.congr_fun heq u

theorem polynomialDifferential_mem_degreePiece {p : ℕ} {u : PolynomialKoszul.Chain}
    (hu : u ∈ degreePiece (p + 1)) : polynomialDifferential u ∈ degreePiece p := by
  rw [mem_degreePiece_iff] at hu ⊢
  have h := exteriorDegree_polynomialDifferential u
  rw [hu, map_smul] at h
  simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul] at h
  exact add_right_cancel h

/-- There is no free CE differential out of exterior degree zero. -/
theorem polynomialDifferential_eq_zero_of_degree_zero {u : PolynomialKoszul.Chain}
    (hu : u ∈ degreePiece 0) : polynomialDifferential u = 0 := by
  change ∀ b ∈ (PolynomialKoszul.basis.repr u).support, b.2.card = 0 at hu
  rw [PolynomialKoszul.eq_sum_basis u]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  rintro ⟨s,t⟩ hb
  have ht : t = ∅ := Finset.card_eq_zero.mp (hu (s,t) hb)
  rw [PolynomialKoszul.basis_apply, ht, polynomialDifferential_tmul_monomial]
  simp only [Finset.sum_empty, show (FiniteExterior.monomial (∅ : Finset Mode)) = (1 : Cochain) from rfl,
    PositiveCE.boundary_one, TensorProduct.tmul_zero, add_zero, smul_zero]

end KhanSL2.BGG.FreeCE
