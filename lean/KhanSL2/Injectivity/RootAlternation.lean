module

public import KhanSL2.Injectivity.RootPolynomialEncoding
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace KhanSL2.Injectivity.Cartan

open Finset MvPolynomial

variable {R : Type*} [CommRing R] [Algebra ℂ R]

def rootPointEvaluation {s : ℕ} (w : Fin s → R) (e f : Equiv.Perm (Fin s)) :
    MvPolynomial (Fin s ⊕ Fin s) ℂ →ₐ[ℂ] R :=
  aeval (Sum.elim (fun i => w (e i)) (fun i => w (f i)))

def rootAlternation {s : ℕ} (w : Fin s → R) :
    MvPolynomial (Fin s ⊕ Fin s) ℂ →ₗ[ℂ] R :=
  ∑ e : Equiv.Perm (Fin s), ∑ f : Equiv.Perm (Fin s),
    (Equiv.Perm.sign e : ℂ) • ((Equiv.Perm.sign f : ℂ) •
      (rootPointEvaluation w e f).toLinearMap)

theorem rootAlternation_apply {s : ℕ} (w : Fin s → R)
    (p : MvPolynomial (Fin s ⊕ Fin s) ℂ) :
    rootAlternation w p = ∑ e : Equiv.Perm (Fin s), ∑ f : Equiv.Perm (Fin s),
      (Equiv.Perm.sign e : R) * (Equiv.Perm.sign f : R) * rootPointEvaluation w e f p := by
  simp [rootAlternation, Algebra.smul_def, mul_assoc]

theorem rootPointEvaluation_monomial {s : ℕ} (w : Fin s → R)
    (e f : Equiv.Perm (Fin s)) (d : (Fin s ⊕ Fin s) →₀ ℕ) (c : ℂ) :
    rootPointEvaluation w e f (monomial d c) =
      algebraMap ℂ R c * ((∏ i, w (e i) ^ d (.inl i)) *
        ∏ i, w (f i) ^ d (.inr i)) := by
  rw [rootPointEvaluation, aeval_monomial, Finsupp.prod_fintype _ _ (by intro; simp),
    Fintype.prod_sum_type]
  rfl

theorem rootAlternation_monomial {s : ℕ} (w : Fin s → R)
    (d : (Fin s ⊕ Fin s) →₀ ℕ) (c : ℂ) :
    rootAlternation w (monomial d c) = c •
      (Matrix.det (fun i j : Fin s => w j ^ d (.inl i)) *
        Matrix.det (fun i j : Fin s => w j ^ d (.inr i))) := by
  rw [rootAlternation_apply, ← Matrix.det_transpose (fun i j : Fin s => w j ^ d (.inl i)),
    ← Matrix.det_transpose (fun i j : Fin s => w j ^ d (.inr i))]
  simp only [rootPointEvaluation_monomial, Matrix.det_apply', Matrix.transpose_apply,
    Algebra.smul_def, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _he
  apply sum_congr rfl
  intro f _hf
  ring

/-- A polynomial constant on all paired permutations can be pulled through the
double antisymmetrization. This is the finite form of diagonal specialization. -/
theorem rootAlternation_mul_constant {s : ℕ} (w : Fin s → R)
    (p q : MvPolynomial (Fin s ⊕ Fin s) ℂ) (t : R)
    (hp : ∀ e f, rootPointEvaluation w e f p = t) :
    rootAlternation w (p * q) = t * rootAlternation w q := by
  simp only [rootAlternation_apply, map_mul, hp, mul_sum]
  apply sum_congr rfl
  intro e _he
  apply sum_congr rfl
  intro f _hf
  ring

/-- Alternating inputs specialize to the diagonal with the exact factorial
squared normalization. This includes the empty alphabet. -/
theorem rootAlternation_of_alternating {s : ℕ} (w : Fin s → R)
    (p : MvPolynomial (Fin s ⊕ Fin s) ℂ) (t : R)
    (hp : ∀ e f, rootPointEvaluation w e f p =
      (Equiv.Perm.sign e : R) * (Equiv.Perm.sign f : R) * t) :
    rootAlternation w p = ((s.factorial : R) ^ 2) * t := by
  rw [rootAlternation_apply]
  have hsign (e : Equiv.Perm (Fin s)) :
      (Equiv.Perm.sign e : R) * (Equiv.Perm.sign e : R) = 1 := by
    simp only [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hterm : ∀ e f : Equiv.Perm (Fin s),
      (Equiv.Perm.sign e : R) * (Equiv.Perm.sign f : R) * rootPointEvaluation w e f p = t := by
    intro e f
    rw [hp]
    calc
      _ = ((Equiv.Perm.sign e : R) * (Equiv.Perm.sign e : R)) *
          ((Equiv.Perm.sign f : R) * (Equiv.Perm.sign f : R)) * t := by ring
      _ = t := by rw [hsign, hsign, one_mul, one_mul]
  simp only [hterm, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin]
  simp only [nsmul_eq_mul, pow_two, mul_assoc]

def rootVandermonde (s : ℕ) : MvPolynomial (Fin s) ℂ :=
  Matrix.det (Matrix.vandermonde (fun i : Fin s => (X i : MvPolynomial (Fin s) ℂ)))

def alternatingRootInput (s : ℕ) (p : MvPolynomial (Fin s) ℂ) :
    MvPolynomial (Fin s ⊕ Fin s) ℂ :=
  rename Sum.inl (rootVandermonde s * p) * rename Sum.inr (rootVandermonde s)

theorem aeval_rootVandermonde {s : ℕ} (w : Fin s → R) :
    aeval w (rootVandermonde s) = Matrix.det (Matrix.vandermonde w) := by
  rw [rootVandermonde, AlgHom.map_det]
  congr 1
  ext i j
  simp [Matrix.vandermonde_apply]

theorem aeval_rootVandermonde_perm {s : ℕ} (w : Fin s → R) (e : Equiv.Perm (Fin s)) :
    aeval (fun i => w (e i)) (rootVandermonde s) =
      (Equiv.Perm.sign e : R) * Matrix.det (Matrix.vandermonde w) := by
  rw [aeval_rootVandermonde]
  exact Matrix.det_permute e (Matrix.vandermonde w)

theorem aeval_symmetric_perm {s : ℕ} (w : Fin s → R) (e : Equiv.Perm (Fin s))
    (p : MvPolynomial (Fin s) ℂ) (hp : p.IsSymmetric) :
    aeval (fun i => w (e i)) p = aeval w p := by
  change aeval (w ∘ e) p = _
  rw [← aeval_rename, hp e]

theorem rootPointEvaluation_alternatingRootInput {s : ℕ} (w : Fin s → R)
    (e f : Equiv.Perm (Fin s)) (p : MvPolynomial (Fin s) ℂ) (hp : p.IsSymmetric) :
    rootPointEvaluation w e f (alternatingRootInput s p) =
      (Equiv.Perm.sign e : R) * (Equiv.Perm.sign f : R) *
        ((Matrix.det (Matrix.vandermonde w)) ^ 2 * aeval w p) := by
  simp only [alternatingRootInput, map_mul, rootPointEvaluation, aeval_rename,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, aeval_rootVandermonde_perm,
    aeval_symmetric_perm w e p hp]
  ring

theorem rootAlternation_alternatingRootInput {s : ℕ} (w : Fin s → R)
    (p : MvPolynomial (Fin s) ℂ) (hp : p.IsSymmetric) :
    rootAlternation w (alternatingRootInput s p) =
      ((s.factorial : R) ^ 2) *
        ((Matrix.det (Matrix.vandermonde w)) ^ 2 * aeval w p) :=
  rootAlternation_of_alternating w _ _ fun e f =>
    rootPointEvaluation_alternatingRootInput w e f p hp

section Newton

variable [Algebra ℚ R]

omit [Algebra ℂ R] in
theorem rootElementary_perm {s : ℕ} (w : Fin s → R) (e : Equiv.Perm (Fin s)) (k : ℕ) :
    rootElementary (fun i => w (e i)) k = rootElementary w k := by
  unfold rootElementary
  change aeval (w ∘ e) (signedElementary (Fin s) ℚ k) = _
  rw [← aeval_rename]
  simp [signedElementary, rename_esymm]

omit [Algebra ℂ R] in
theorem rootPowerSum_perm {s : ℕ} (w : Fin s → R) (e : Equiv.Perm (Fin s)) (k : ℕ) :
    rootPowerSum (fun i => w (e i)) k = rootPowerSum w k := by
  simp only [rootPowerSum_eq_sum]
  exact Equiv.sum_comp e (fun i => w i ^ k)

omit [Algebra ℂ R] in
theorem rootCycle_perm {s : ℕ} (u v : Fin s → R) (e f : Equiv.Perm (Fin s)) (k : ℕ) :
    rootCycle (fun i => u (e i)) (fun i => v (f i)) k = rootCycle u v k := by
  have he : rootElementary (fun i => u (e i)) = rootElementary u :=
    funext (rootElementary_perm u e)
  have hf : rootPowerSum (fun i => v (f i)) = rootPowerSum v :=
    funext (rootPowerSum_perm v f)
  simp only [rootCycle, he, hf]

theorem rootPointEvaluation_rootCycle {s : ℕ} (w : Fin s → R)
    (e f : Equiv.Perm (Fin s)) (k j : ℕ) :
    rootPointEvaluation w e f
      (rootCycle (fun i : Fin s => (X (.inl i) : MvPolynomial (Fin s ⊕ Fin s) ℂ))
        (fun i : Fin s => X (.inr i)) k j) = rootCycle w w k j := by
  have h := congrArg (fun c : ℕ →₀ R => c j)
    (rootCycle_map (rootPointEvaluation w e f).toRingHom
      (fun i : Fin s => (X (.inl i) : MvPolynomial (Fin s ⊕ Fin s) ℂ))
      (fun i : Fin s => X (.inr i)) k)
  simpa only [mapCartanCoefficients_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    rootPointEvaluation, aeval_X, Sum.elim_inl, Sum.elim_inr, rootCycle_perm] using h

end Newton

end KhanSL2.Injectivity.Cartan
