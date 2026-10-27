module

public import KhanSL2.Injectivity.VandermondeFactors
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant
public import KhanSL2.Modules.PowerSumCoordinates

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace KhanSL2.BGGBridge.TopAlternants

open Finset MvPolynomial
open KhanSL2.Injectivity

/-- The increasing Vandermonde in the coefficient slots. -/
def vandermonde (B : ℕ) : MvPolynomial (Fin B) ℂ :=
  TauCeti.alternant (Fin B) ℂ (fun i => i.val)

theorem vandermonde_eq_prod (B : ℕ) :
    vandermonde B = ∏ a : OrderedPair B,
      (X a.val.2 - X a.val.1 : MvPolynomial (Fin B) ℂ) := by
  rw [vandermonde, TauCeti.alternant_fin_val_eq_vandermonde]
  exact (orderedPair_prod (fun a : Fin B × Fin B =>
    (X a.2 - X a.1 : MvPolynomial (Fin B) ℂ))).symm

theorem vandermonde_ne_zero (B : ℕ) : vandermonde B ≠ 0 :=
  TauCeti.alternant_ne_zero_of_injective Fin.val_injective

theorem rename_vandermonde (B : ℕ) (e : Equiv.Perm (Fin B)) :
    rename e (vandermonde B) = e.sign • vandermonde B :=
  TauCeti.rename_alternant e _

/-- Every alternating polynomial is divisible by the Vandermonde. -/
theorem vandermonde_dvd {B : ℕ} (p : MvPolynomial (Fin B) ℂ)
    (hp : ∀ e : Equiv.Perm (Fin B), rename e p = e.sign • p) :
    vandermonde B ∣ p := by
  rw [vandermonde_eq_prod]
  apply Fintype.prod_dvd_of_isRelPrime
  · intro a b hab
    apply diagonal_isRelPrime a.property.ne' b.property.ne'
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact hab (Subtype.ext (Prod.ext h₂.symm h₁.symm))
    · have ha := a.property
      have hb := b.property
      rw [h₁, h₂] at hb
      exact (lt_asymm ha hb).elim
  · intro a
    apply (diagonal_eq_zero_iff_dvd a.property.ne' p).mp
    apply diagonal_eq_zero_of_antisymmetric
    simpa [Equiv.Perm.sign_swap a.property.ne', Units.smul_def] using
      hp (Equiv.swap a.val.2 a.val.1)

/-- The quotient of two polynomials with the same sign character is symmetric. -/
theorem alternating_eq_vandermonde_mul {B : ℕ} (p : MvPolynomial (Fin B) ℂ)
    (hp : ∀ e : Equiv.Perm (Fin B), rename e p = e.sign • p) :
    ∃ q : KhanSL2.Modules.R B, p = vandermonde B * (q : MvPolynomial (Fin B) ℂ) := by
  obtain ⟨q, hq⟩ := vandermonde_dvd p hp
  refine ⟨⟨q, ?_⟩, hq⟩
  intro e
  have h := hp e
  rw [hq, map_mul, rename_vandermonde] at h
  have hs : (e.sign • vandermonde B) * rename e q =
      (e.sign • vandermonde B) * q := by
    simpa only [smul_mul_assoc] using h
  exact mul_left_cancel₀
    (by simpa only [Units.smul_def, zsmul_eq_mul] using
      mul_ne_zero (show ((e.sign : ℤ) : MvPolynomial (Fin B) ℂ) ≠ 0 from
        Int.cast_ne_zero.mpr (Units.ne_zero e.sign)) (vandermonde_ne_zero B)) hs

variable {B : ℕ} {Q : Type*} [AddCommGroup Q] [Module ℂ Q]

/-- Alternation becomes multiplication by `B!` under an alternating linear map. -/
theorem map_alternant (L : MvPolynomial (Fin B) ℂ →ₗ[ℂ] Q)
    (hL : ∀ (e : Equiv.Perm (Fin B)) p, L (rename e p) = e.sign • L p)
    (a : Fin B → ℕ) :
    L (TauCeti.alternant (Fin B) ℂ a) =
      B.factorial • L (∏ i : Fin B, (X i : MvPolynomial (Fin B) ℂ) ^ a i) := by
  rw [TauCeti.alternant_eq_sum, map_sum]
  have hterm (e : Equiv.Perm (Fin B)) :
      L (e.sign • ∏ i : Fin B, (X (e i) : MvPolynomial (Fin B) ℂ) ^ a i) =
        L (∏ i : Fin B, (X i : MvPolynomial (Fin B) ℂ) ^ a i) := by
    have hr : (∏ i : Fin B, (X (e i) : MvPolynomial (Fin B) ℂ) ^ a i) =
        rename e (∏ i : Fin B, (X i : MvPolynomial (Fin B) ℂ) ^ a i) := by simp
    rw [hr]
    simp only [Units.smul_def, map_zsmul, hL]
    rw [← Units.smul_def, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
  simp only [hterm, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin]

section Cyclicity

variable {A : Type*} [CommRing A] [Algebra ℂ A]
  [Module A Q] [IsScalarTower ℂ A Q]

omit [IsScalarTower ℂ A Q] in
/-- Alternating polynomial maps are generated, over symmetric coefficients, by
one consecutive-exponent word. No injectivity of the polynomial map is needed. -/
theorem product_eq_smul (L : MvPolynomial (Fin B) ℂ →ₗ[ℂ] Q)
    (hL : ∀ (e : Equiv.Perm (Fin B)) p, L (rename e p) = e.sign • L p)
    (action : KhanSL2.Modules.R B →ₐ[ℂ] A)
    (hmul : ∀ (q : KhanSL2.Modules.R B) p,
      L ((q : MvPolynomial (Fin B) ℂ) * p) = action q • L p)
    (a : Fin B → ℕ) :
    ∃ r : A, L (∏ i : Fin B, (X i : MvPolynomial (Fin B) ℂ) ^ a i) =
      r • L (∏ i : Fin B, (X i : MvPolynomial (Fin B) ℂ) ^ i.val) := by
  obtain ⟨q, hq⟩ := alternating_eq_vandermonde_mul
    (TauCeti.alternant (Fin B) ℂ a) (fun e => TauCeti.rename_alternant e a)
  refine ⟨action q, ?_⟩
  have h := map_alternant L hL a
  rw [hq, mul_comm, hmul, vandermonde, map_alternant L hL] at h
  apply smul_right_injective Q (show (B.factorial : ℂ) ≠ 0 from
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero B))
  simpa only [Nat.cast_smul_eq_nsmul, smul_comm (action q) B.factorial] using h.symm

/-- Every value of an alternating polynomial map lies in its consecutive-word
cyclic module. The scalar action is the specified action on symmetric polynomials. -/
theorem exists_smul_of_symmetric (L : MvPolynomial (Fin B) ℂ →ₗ[ℂ] Q)
    (hL : ∀ (e : Equiv.Perm (Fin B)) p, L (rename e p) = e.sign • L p)
    (action : KhanSL2.Modules.R B →ₐ[ℂ] A)
    (hmul : ∀ (q : KhanSL2.Modules.R B) p,
      L ((q : MvPolynomial (Fin B) ℂ) * p) = action q • L p)
    (p : MvPolynomial (Fin B) ℂ) :
    ∃ r : A, L p =
      r • L (∏ i : Fin B, (X i : MvPolynomial (Fin B) ℂ) ^ i.val) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    obtain ⟨r, hr⟩ := product_eq_smul L hL action hmul d
    refine ⟨algebraMap ℂ A c * r, ?_⟩
    rw [monomial_eq, Finsupp.prod_fintype _ _ (by intro; simp),
      ← MvPolynomial.smul_eq_C_mul, map_smul, hr, mul_smul, algebraMap_smul]
  | add p q hp hq =>
    obtain ⟨r, hr⟩ := hp
    obtain ⟨s, hs⟩ := hq
    exact ⟨r + s, by rw [map_add, hr, hs, add_smul]⟩

/-- To identify the symmetric coefficient action, only the first `B` power sums
need to be checked. This is a consequence of the proved Newton coordinates. -/
theorem symmetric_intertwines_of_powerSums
    (e : MvPolynomial (Fin B) ℂ ≃ₐ[ℂ] A)
    (L : MvPolynomial (Fin B) ℂ →ₗ[ℂ] Q)
    (hpower : ∀ (i : Fin B) p,
      L (psum (Fin B) ℂ (i.val + 1) * p) = e (X i) • L p)
    (q : KhanSL2.Modules.R B) (p : MvPolynomial (Fin B) ℂ) :
    L ((q : MvPolynomial (Fin B) ℂ) * p) =
      e ((KhanSL2.Modules.powerSumAlgEquiv B).symm q) • L p := by
  have hpoly : ∀ (r : MvPolynomial (Fin B) ℂ) p,
      L (((KhanSL2.Modules.powerSumAlgEquiv B) r : MvPolynomial (Fin B) ℂ) * p) =
        e r • L p := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C c =>
      intro p
      have hc₁ := (KhanSL2.Modules.powerSumAlgEquiv B).commutes c
      have hc₂ := e.commutes c
      change KhanSL2.Modules.powerSumAlgEquiv B (C c) = _ at hc₁
      change e (C c) = _ at hc₂
      rw [hc₁, hc₂]
      change L (C c * p) = algebraMap ℂ A c • L p
      rw [← MvPolynomial.smul_eq_C_mul, map_smul, algebraMap_smul]
    | add r s hr hs =>
      intro p
      simp only [map_add, Subalgebra.coe_add, add_mul, hr, hs, add_smul]
    | mul_X r i hr =>
      intro p
      simp only [map_mul, Subalgebra.coe_mul, KhanSL2.Modules.powerSumAlgEquiv_X,
        mul_assoc, mul_smul]
      rw [hr]
      change e r • L (psum (Fin B) ℂ (i.val + 1) * p) = _
      rw [hpower]
  simpa only [AlgEquiv.apply_symm_apply] using
    hpoly ((KhanSL2.Modules.powerSumAlgEquiv B).symm q) p

/-- Cyclicity with the actual power-sum operators, expressed in any prescribed
polynomial coordinates on the scalar ring. -/
theorem exists_smul_of_powerSums
    (e : MvPolynomial (Fin B) ℂ ≃ₐ[ℂ] A)
    (L : MvPolynomial (Fin B) ℂ →ₗ[ℂ] Q)
    (hL : ∀ (f : Equiv.Perm (Fin B)) p, L (rename f p) = f.sign • L p)
    (hpower : ∀ (i : Fin B) p,
      L (psum (Fin B) ℂ (i.val + 1) * p) = e (X i) • L p)
    (p : MvPolynomial (Fin B) ℂ) :
    ∃ r : A, L p =
      r • L (∏ i : Fin B, (X i : MvPolynomial (Fin B) ℂ) ^ i.val) := by
  exact exists_smul_of_symmetric L hL
    (e.toAlgHom.comp (KhanSL2.Modules.powerSumAlgEquiv B).symm.toAlgHom)
    (fun q p => symmetric_intertwines_of_powerSums e L hpower q p) p

end Cyclicity

end KhanSL2.BGGBridge.TopAlternants
