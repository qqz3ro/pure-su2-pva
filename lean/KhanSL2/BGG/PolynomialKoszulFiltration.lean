module

public import KhanSL2.BGG.PolynomialKoszulGrading
public import KhanSL2.BGG.PolynomialKoszulTensor

@[expose] public section

/-! The exhaustive total-length filtration and tensor bounds for PBW leading-term correction. -/
noncomputable section
open scoped BigOperators TensorProduct
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PolynomialKoszul

/-- Strict total-length filtration; the zero stage is the zero space. -/
def filtration (n : ℕ) : Submodule ℂ Chain :=
  (Finsupp.supported ℂ ℂ {b : BasisIndex | totalLength b < n}).comap basis.repr.toLinearMap

theorem mem_filtration_iff (u : Chain) (n : ℕ) :
    u∈filtration n ↔ ∀ b∈(basis.repr u).support, totalLength b<n := Iff.rfl

@[simp] theorem basis_mem_filtration_iff (b : BasisIndex) (n : ℕ) :
    basis b∈filtration n ↔ totalLength b<n := by
  classical
  rw [mem_filtration_iff, basis.repr_self]
  simp

theorem filtration_mono : Monotone filtration := by
  intro n m hnm u hu b hb
  exact lt_of_lt_of_le (hu hb) hnm

@[simp] theorem filtration_zero : filtration 0 = ⊥ := by
  apply le_antisymm
  · intro u hu
    rw [mem_filtration_iff] at hu
    change u=0
    apply basis.repr.injective
    apply Finsupp.ext
    intro b
    by_cases hb : basis.repr u b=0
    · simpa using hb
    · exact (Nat.not_lt_zero _ (hu b (Finsupp.mem_support_iff.mpr hb))).elim
  · exact bot_le

/-- Every actual finite chain lies at a finite filtration stage. -/
theorem filtration_exhaustive (u : Chain) : ∃ n, u∈filtration n := by
  classical
  refine ⟨(basis.repr u).support.sup totalLength + 1, ?_⟩
  rw [mem_filtration_iff]
  intro b hb
  exact Nat.lt_succ_of_le (Finset.le_sup (f := totalLength) hb)

theorem lengthPiece_le_filtration {k n : ℕ} (hkn : k<n) : lengthPiece k ≤ filtration n := by
  intro u hu b hb
  change totalLength b < n
  rw [hu hb]
  exact hkn

theorem homotopy_mem_filtration {n : ℕ} {u : Chain} (hu : u∈filtration n) :
    homotopy u∈filtration n := by
  rw [eq_sum_basis u]
  simp only [map_sum, map_smul]
  apply (filtration n).sum_mem
  intro b hb
  apply (filtration n).smul_mem
  apply lengthPiece_le_filtration (hu hb)
  apply homotopy_mem_lengthPiece
  rw [mem_lengthPiece_iff, lengthOp_basis]

theorem d_mem_filtration {n : ℕ} {u : Chain} (hu : u∈filtration n) : d u∈filtration n := by
  rw [eq_sum_basis u]
  simp only [map_sum, map_smul]
  apply (filtration n).sum_mem
  intro b hb
  apply (filtration n).smul_mem
  apply lengthPiece_le_filtration (hu hb)
  apply d_mem_lengthPiece
  rw [mem_lengthPiece_iff, lengthOp_basis]

/-- The actual tensor-basis coefficient formula. -/
theorem basis_repr_tmul (p : Poly) (u : Exterior) (s : Exponent) (t : Finset Mode) :
    basis.repr (p ⊗ₜ[ℂ] u) (s,t) = u t * p.coeff s := by
  rw [basis, Module.Basis.tensorProduct_repr_tmul_apply]
  rfl

/-- A polynomial-degree bound plus an exterior support bound controls total length. -/
theorem tmul_mem_filtration_of_support {p : Poly} {u : Exterior} {q r n : ℕ}
    (hp : ∀ s∈p.support, s.sum (fun _ k => k) ≤ q)
    (hu : ∀ t∈u.support, t.card ≤ r) (hqr : q+r<n) : p ⊗ₜ[ℂ] u∈filtration n := by
  intro b hb
  obtain ⟨s,t⟩ := b
  have hcoeff : basis.repr (p ⊗ₜ[ℂ] u) (s,t) ≠ 0 := Finsupp.mem_support_iff.mp hb
  rw [basis_repr_tmul] at hcoeff
  have ht : t∈u.support := Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp hcoeff).1
  have hs : s∈p.support := MvPolynomial.mem_support_iff.mpr (mul_ne_zero_iff.mp hcoeff).2
  have hps := hp s hs
  have hut := hu t ht
  change s.sum (fun _ k => k) + t.card < n
  omega

theorem tmul_mem_filtration_of_restrictTotalDegree {p : Poly} {u : Exterior} {q r n : ℕ}
    (hp : p∈MvPolynomial.restrictTotalDegree Mode ℂ q)
    (hu : ∀ t∈u.support, t.card≤r) (hqr : q+r<n) : p ⊗ₜ[ℂ] u∈filtration n := by
  apply tmul_mem_filtration_of_support _ hu hqr
  exact hp

/-- The homogeneous exterior-degree specialization used for the transported CE error. -/
theorem tmul_mem_filtration_of_exterior_degree {p : Poly} {u : Exterior} {q r n : ℕ}
    (hp : p∈MvPolynomial.restrictTotalDegree Mode ℂ q)
    (hu : PositiveCE.degreeOp u = (r : ℂ) • u) (hqr : q+r<n) :
    p ⊗ₜ[ℂ] u∈filtration n := by
  apply tmul_mem_filtration_of_restrictTotalDegree hp _ hqr
  have h := (euler_degree_eq_smul_iff r u).mp hu
  intro t ht
  exact (h t ht).le

theorem tmul_mem_filtration_degree_bound {p : Poly} {u : Exterior} {q r : ℕ}
    (hp : p∈MvPolynomial.restrictTotalDegree Mode ℂ q)
    (hu : PositiveCE.degreeOp u = (r : ℂ) • u) : p ⊗ₜ[ℂ] u∈filtration (q+r+1) :=
  tmul_mem_filtration_of_exterior_degree hp hu (Nat.lt_succ_self _)

/-- The usual polynomial augmentation, evaluation of all variables at zero. -/
def polynomialAugmentation : Poly →ₐ[ℂ] ℂ := MvPolynomial.aeval (fun _ => 0)

@[simp] theorem polynomialAugmentation_apply (p : Poly) : polynomialAugmentation p = p.coeff 0 := by
  rw [polynomialAugmentation, MvPolynomial.aeval_zero']
  rfl

@[simp] theorem polynomialAugmentation_X (i : Mode) : polynomialAugmentation (MvPolynomial.X i) = 0 := by
  simp [polynomialAugmentation]

/-- The Koszul augmentation is exactly polynomial augmentation times exterior scalar coefficient. -/
theorem augmentation_tmul (p : Poly) (u : Exterior) :
    augmentation (p ⊗ₜ[ℂ] u) = polynomialAugmentation p * u ∅ := by
  rw [augmentation_apply]
  change basis.repr (p ⊗ₜ[ℂ] u) (0,∅) = _
  rw [basis_repr_tmul, polynomialAugmentation_apply, mul_comm]

theorem augmentation_tmul_monomial (p : Poly) (t : Finset Mode) :
    augmentation (p ⊗ₜ[ℂ] monomial t) =
      if t=∅ then polynomialAugmentation p else 0 := by
  classical
  rw [augmentation_tmul]
  simp [monomial, Finsupp.single_apply]

@[simp] theorem augmentation_tmul_one (p : Poly) :
    augmentation (p ⊗ₜ[ℂ] (1 : Exterior)) = polynomialAugmentation p := by
  change augmentation (p ⊗ₜ[ℂ] monomial ∅) = _
  rw [augmentation_tmul_monomial, if_pos rfl]

end KhanSL2.BGG.PolynomialKoszul
