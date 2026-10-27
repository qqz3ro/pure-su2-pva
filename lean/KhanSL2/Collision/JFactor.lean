module

public import KhanSL2.Collision.ChartSplit

@[expose] public section

/-!
# Factorization of `J` on charts (depth paper, eq. `Jfactor`)

On a chart `(A, f₁, f₂)` of `R_B` with `B = B₁ + B₂`,
`A ⊗_{R_B} J_{B,p} ≅ ⊕_{q ≤ p} (A ⊗_{R_{B₁}} J_{B₁,q}) ⊗_A (A ⊗_{R_{B₂}} J_{B₂,p-q})`
as `A`-modules (`jFactor`).

Proof: `J_{r,s} ≅ ℂ[a, w]` (coefficients of `(A, W)`, `srcEquivJ`), so the left side is the
ring `T = A ⊗_{R_B} CMod B p s` of `ChartSplit`. That ring is the product of its components
`T ⧸ (1 - eps q)` (`toComponents_bijective`), and each component is the factorized ring
`(A ⊗ CMod B₁ q s₁) ⊗_A (A ⊗ CMod B₂ (p-q) s₂)` (`Setup.quotEquiv`). Summands that do not
satisfy the degree condition vanish on both sides.
-/

noncomputable section

open Polynomial TensorProduct
open scoped DirectSum

namespace KhanSL2.Collision

open Conditional Depth CoordSplit
open scoped KhanSL2.Conditional

/-! ## `J ≅ CMod` -/

/-- `J_{r,s} ≅ ℂ[a, w]` as `R_B`-modules, `B = r + 3s`. -/
def jEquiv (B r s : ℕ) (h : B = r + 3 * s) : ↥(Depth.J B r s) ≃ₗ[RB B] CMod B r s := by
  subst h
  exact (srcEquivJ r s).symm

/-- In the nonzero case, `J_{B,p} ≅ CMod B p ((B-p)/3)`. -/
def jbEquiv (B p : ℕ) (h : p ≤ B ∧ 3 ∣ B - p) : J B p ≃ₗ[RB B] CMod B p ((B - p) / 3) :=
  (LinearEquiv.ofEq _ _ (show Depth.JB B p = Depth.J B p ((B - p) / 3) from if_pos h)).trans
    (jEquiv B p ((B - p) / 3) (by omega))

theorem J_subsingleton (B p : ℕ) (h : ¬ (p ≤ B ∧ 3 ∣ B - p)) : Subsingleton (J B p) := by
  have h0 : Depth.JB B p = ⊥ := if_neg h
  change Subsingleton ↥(Depth.JB B p)
  rw [h0]
  infer_instance

theorem tensor_subsingleton_right {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton N] : Subsingleton (M ⊗[R] N) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ z : M ⊗[R] N, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [h0 x, h0 y]

theorem tensor_subsingleton_left {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton M] : Subsingleton (M ⊗[R] N) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ z : M ⊗[R] N, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim m 0, zero_tmul]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [h0 x, h0 y]

/-! ## The coefficient map of a monic polynomial -/

theorem univPoly_map_coeffHom {A : Type*} [CommRing A] [Algebra ℂ A] {n : ℕ} {f : A[X]}
    (hf : f.Monic) (hn : f.natDegree = n) :
    (univPoly n).map (coeffHom n f : RB n →+* A) = f := by
  cases subsingleton_or_nontrivial A
  · exact Subsingleton.elim _ _
  refine eq_of_monic_of_coeff_lt ((univPoly_monic n).map _) hf (n := n)
    (by rw [(univPoly_monic n).natDegree_map, univPoly, natDegree_monicOf]) hn ?_
  intro k hk
  have hk' : k = n - 1 - ((⟨n - 1 - k, by omega⟩ : Fin n) : ℕ) := by simp only; omega
  rw [coeff_map, hk', univPoly_coeff, map_mul]
  simp only [RingHom.coe_coe, coeffHom, MvPolynomial.aeval_C, MvPolynomial.aeval_X, elemCoord,
    map_pow, map_neg, map_one]
  rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]


theorem summand_subsingleton {B₁ B₂ : ℕ} {A : Type*} [CommRing A] [Algebra (RB B₁) A]
    [Algebra (RB B₂) A] (q r : ℕ) (h : ¬ (q ≤ B₁ ∧ 3 ∣ B₁ - q) ∨ ¬ (r ≤ B₂ ∧ 3 ∣ B₂ - r)) :
    Subsingleton ((A ⊗[RB B₁] J B₁ q) ⊗[A] (A ⊗[RB B₂] J B₂ r)) := by
  rcases h with h | h
  · have := J_subsingleton B₁ q h
    have : Subsingleton (A ⊗[RB B₁] J B₁ q) := tensor_subsingleton_right
    exact tensor_subsingleton_left
  · have := J_subsingleton B₂ r h
    have : Subsingleton (A ⊗[RB B₂] J B₂ r) := tensor_subsingleton_right
    exact tensor_subsingleton_right

/-! ## The factorization -/

/-- **Factorization of `J` on charts** (depth paper, eq. `Jfactor`). -/
theorem jFactor (B : ℕ) : JFactor B := by
  intro B₁ B₂ _ _ hBB A _ _ _ c p
  let := c.algebra₁
  let := c.algebra₂
  show Nonempty ((A ⊗[RB B] J B p) ≃ₗ[A] FactorSide c (J B₁) (J B₂) p)
  by_cases hv : p ≤ B ∧ 3 ∣ B - p
  swap
  · have := J_subsingleton B p hv
    have : Subsingleton (A ⊗[RB B] J B p) := tensor_subsingleton_right
    have : ∀ q : Fin (p + 1),
        Subsingleton ((A ⊗[RB B₁] J B₁ q) ⊗[A] (A ⊗[RB B₂] J B₂ (p - q))) := by
      intro q
      have hq := q.isLt
      exact summand_subsingleton _ _ (by omega)
    have : Subsingleton (FactorSide c (J B₁) (J B₂) p) :=
      (DirectSum.linearEquivFunOnFintype A (Fin (p + 1)) _).injective.subsingleton
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  set s := (B - p) / 3 with hs_def
  have hB : B = p + 3 * s := by omega
  let := chartComplexAlgebra (B := B) (A := A)
  obtain ⟨α, β, hαβ⟩ := c.coprime
  let D : Setup B B₁ B₂ A :=
    { f₁ := c.f₁, f₂ := c.f₂, α := α, β := β, monic₁ := c.monic₁, monic₂ := c.monic₂,
      deg₁ := c.degree₁, deg₂ := c.degree₂, factor := c.factor,
      univ₁ := univPoly_map_coeffHom c.monic₁ c.degree₁,
      univ₂ := univPoly_map_coeffHom c.monic₂ c.degree₂, bezout := hαβ }
  let e₀ : (A ⊗[RB B] J B p) ≃ₗ[A] A ⊗[RB B] CMod B p s :=
    LinearEquiv.baseChange (RB B) A _ _ (jbEquiv B p hv)
  let ε : Fin (p + 1) → A ⊗[RB B] CMod B p s := fun q => D.eps p s q
  have hmul : ∀ i j, ε i * ε j = if i = j then ε i else 0 := by
    intro i j
    simp only [ε]
    rw [D.eps_mul hB]
    simp only [Fin.val_inj]
  have hsum : ∑ i, ε i = 1 := by
    simp only [ε]
    rw [Fin.sum_univ_eq_sum_range (fun q => D.eps p s q)]
    exact D.sum_eps hB
  let e₁ := (AlgEquiv.ofBijective (toComponents (A := A) ε)
    (toComponents_bijective ε hmul hsum)).toLinearEquiv
  have e₂ : ∀ q : Fin (p + 1), Nonempty (((A ⊗[RB B] CMod B p s) ⧸ Ideal.span {1 - ε q}) ≃ₗ[A]
      ((A ⊗[RB B₁] J B₁ q) ⊗[A] (A ⊗[RB B₂] J B₂ (p - q)))) := by
    intro q
    have hqp : (q : ℕ) ≤ p := Nat.lt_succ_iff.mp q.isLt
    by_cases hq : Setup.Valid B₁ s q
    · have hq' := hq
      obtain ⟨h1, h2, h3⟩ := hq'
      have hB₁' : B₁ = q + 3 * ((B₁ - q) / 3) := by omega
      have hB₂' : B₂ = (p - q) + 3 * ((B₂ - (p - q)) / 3) := by omega
      have hp' : p = q + (p - q) := by omega
      have hs' : s = (B₁ - q) / 3 + (B₂ - (p - q)) / 3 := by omega
      have hI : Ideal.span {1 - ε q} = D.Ib p s q ((B₁ - q) / 3) := by
        simp only [ε, Setup.eps, if_pos hq]
      have hJ₁ : (q : ℕ) ≤ B₁ ∧ 3 ∣ B₁ - q := ⟨h1, h2⟩
      have hJ₂ : p - q ≤ B₂ ∧ 3 ∣ B₂ - (p - q) := by omega
      exact ⟨(Ideal.quotientEquivAlgOfEq A hI).toLinearEquiv ≪≫ₗ
        (D.quotEquiv hB hB₁' hB₂' hp' hs').toLinearEquiv ≪≫ₗ
        TensorProduct.congr (LinearEquiv.baseChange (RB B₁) A _ _ (jbEquiv B₁ q hJ₁).symm)
          (LinearEquiv.baseChange (RB B₂) A _ _ (jbEquiv B₂ (p - q) hJ₂).symm)⟩
    · have hε : ε q = 0 := by simp only [ε, Setup.eps, if_neg hq]
      have : Subsingleton ((A ⊗[RB B] CMod B p s) ⧸ Ideal.span {1 - ε q}) := by
        rw [hε, sub_zero, Ideal.span_singleton_one]
        exact Ideal.Quotient.subsingleton_iff.mpr rfl
      have := summand_subsingleton (A := A) (B₁ := B₁) (B₂ := B₂) q (p - q)
        (by unfold Setup.Valid at hq; omega)
      exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  exact ⟨e₀ ≪≫ₗ e₁ ≪≫ₗ LinearEquiv.piCongrRight (fun q => Classical.choice (e₂ q)) ≪≫ₗ
    (DirectSum.linearEquivFunOnFintype A (Fin (p + 1)) _).symm⟩

end KhanSL2.Collision
