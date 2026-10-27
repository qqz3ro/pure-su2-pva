module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! The polynomial part of coprime weighted-root splitting. All statements hold
in arbitrary commutative rings, including rings with nilpotents. -/

noncomputable section
open scoped BigOperators
open Polynomial
namespace KhanSL2.Factorization.WeightedRoots

variable {A : Type*} [CommRing A]
variable {ι : Type*}

/-- A weighted product over a specified collection of labelled roots. -/
def rootProduct (x : ι → A) (m : ι → ℕ) (S : Finset ι) : A[X] :=
  ∏ i ∈ S, (X - C (x i)) ^ m i

theorem rootProduct_monic (x : ι → A) (m : ι → ℕ) (S : Finset ι) :
    (rootProduct x m S).Monic :=
  monic_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (x i)).pow (m i))

theorem rootProduct_natDegree [Nontrivial A] (x : ι → A) (m : ι → ℕ) (S : Finset ι) :
    (rootProduct x m S).natDegree = ∑ i ∈ S, m i := by
  unfold rootProduct
  rw [natDegree_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (x i)).pow (m i))]
  simp only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

theorem rootProduct_union [DecidableEq ι] (x : ι → A) (m : ι → ℕ) {S T : Finset ι}
    (h : Disjoint S T) : rootProduct x m (S ∪ T) = rootProduct x m S * rootProduct x m T :=
  Finset.prod_union h

theorem rootProduct_eval_eq_zero (x : ι → A) (m : ι → ℕ) (S : Finset ι)
    {i : ι} (hi : i ∈ S) (hm : 0 < m i) : (rootProduct x m S).eval (x i) = 0 := by
  unfold rootProduct
  rw [eval_prod]
  apply Finset.prod_eq_zero hi
  simp [hm.ne']

/-- An invertible value makes the corresponding linear factor coprime to f. -/
theorem isCoprime_X_sub_C_of_isUnit_eval (f : A[X]) (a : A) (h : IsUnit (f.eval a)) :
    IsCoprime f (X - C a) := by
  obtain ⟨u,hu⟩ := h
  obtain ⟨q,hq⟩ := (X_sub_C_dvd_sub_C_eval (p := f) (a := a))
  refine ⟨C (↑u⁻¹ : A), -(C (↑u⁻¹ : A) * q), ?_⟩
  have hc : C (↑u⁻¹ : A) * C (f.eval a) = 1 := by
    rw [← hu, ← C_mul, Units.inv_mul, C_1]
  calc
    C (↑u⁻¹ : A) * f + -(C (↑u⁻¹ : A) * q) * (X - C a) =
        C (↑u⁻¹ : A) * C (f.eval a) := by linear_combination C (↑u⁻¹ : A) * hq
    _ = 1 := hc

theorem isCoprime_rootProduct_of_isUnit_eval (f : A[X]) (x : ι → A) (m : ι → ℕ)
    (S : Finset ι) (h : ∀ i ∈ S, IsUnit (f.eval (x i))) :
    IsCoprime f (rootProduct x m S) := by
  apply IsCoprime.prod_right
  intro i hi
  exact (isCoprime_X_sub_C_of_isUnit_eval f (x i) (h i hi)).pow_right

/-- Two complementary root collections must give the prescribed monic factors.
The hypotheses concern root values, not reduced points or integral domains. -/
theorem factors_eq_of_assignment {f₁ f₂ : A[X]} (hf₁ : f₁.Monic) (hf₂ : f₂.Monic)
    (x : ι → A) (m : ι → ℕ) (S T : Finset ι)
    (hprod : rootProduct x m S * rootProduct x m T = f₁ * f₂)
    (hS : ∀ i ∈ S, IsUnit (f₂.eval (x i)))
    (hT : ∀ i ∈ T, IsUnit (f₁.eval (x i))) :
    rootProduct x m S = f₁ ∧ rootProduct x m T = f₂ := by
  nontriviality A
  have hd₁ : f₁ ∣ rootProduct x m S :=
    (isCoprime_rootProduct_of_isUnit_eval f₁ x m T hT).dvd_of_dvd_mul_right
      (hprod.symm ▸ dvd_mul_right f₁ f₂)
  have hd₂ : f₂ ∣ rootProduct x m T :=
    (isCoprime_rootProduct_of_isUnit_eval f₂ x m S hS).dvd_of_dvd_mul_left
      (hprod.symm ▸ dvd_mul_left f₂ f₁)
  have hl₁ := hf₁.natDegree_le_of_dvd (rootProduct_monic x m S).ne_zero hd₁
  have hl₂ := hf₂.natDegree_le_of_dvd (rootProduct_monic x m T).ne_zero hd₂
  have hn := congrArg Polynomial.natDegree hprod
  rw [(rootProduct_monic x m S).natDegree_mul (rootProduct_monic x m T),
    hf₁.natDegree_mul hf₂] at hn
  exact ⟨eq_of_monic_of_dvd_of_natDegree_le hf₁ (rootProduct_monic x m S) hd₁ (by omega),
    eq_of_monic_of_dvd_of_natDegree_le hf₂ (rootProduct_monic x m T) hd₂ (by omega)⟩

/-- Bézout coefficients supply the root-assignment idempotent. -/
def selector (β f₂ : A[X]) (a : A) : A := β.eval a * f₂.eval a

theorem selector_isIdempotent {α β f₁ f₂ : A[X]} (hbez : α*f₁ + β*f₂ = 1)
    {a : A} (hroot : (f₁*f₂).eval a = 0) : IsIdempotentElem (selector β f₂ a) := by
  have hb := congrArg (fun p : A[X] => p.eval a) hbez
  simp only [eval_add, eval_mul, eval_one] at hb
  rw [eval_mul] at hroot
  change (β.eval a * f₂.eval a) * (β.eval a * f₂.eval a) = β.eval a * f₂.eval a
  linear_combination (β.eval a * f₂.eval a) * hb - (α.eval a * β.eval a) * hroot

theorem eval_left_eq_zero_of_selector_one {α β f₁ f₂ : A[X]}
    (_hbez : α*f₁ + β*f₂ = 1) {a : A} (hroot : (f₁*f₂).eval a = 0)
    (hsel : selector β f₂ a = 1) : f₁.eval a = 0 := by
  rw [eval_mul] at hroot
  calc
    f₁.eval a = f₁.eval a * selector β f₂ a := by rw [hsel,mul_one]
    _ = β.eval a * (f₁.eval a * f₂.eval a) := by unfold selector; ring
    _ = 0 := by rw [hroot,mul_zero]

theorem isUnit_eval_right_of_selector_one {β f₂ : A[X]} {a : A}
    (hsel : selector β f₂ a = 1) : IsUnit (f₂.eval a) :=
  IsUnit.of_mul_eq_one (β.eval a) (by simpa only [selector,mul_comm] using hsel)

theorem isUnit_eval_left_of_selector_zero {α β f₁ f₂ : A[X]}
    (hbez : α*f₁ + β*f₂ = 1) {a : A} (hsel : selector β f₂ a = 0) :
    IsUnit (f₁.eval a) := by
  have hb := congrArg (fun p : A[X] => p.eval a) hbez
  simp only [eval_add, eval_mul, eval_one] at hb
  change β.eval a * f₂.eval a = 0 at hsel
  rw [hsel,add_zero] at hb
  exact IsUnit.of_mul_eq_one (α.eval a) (by simpa only [mul_comm] using hb)

theorem rootProduct_map {B : Type*} [CommRing B] (φ : A →+* B)
    (x : ι → A) (m : ι → ℕ) (S : Finset ι) :
    (rootProduct x m S).map φ = rootProduct (fun i => φ (x i)) m S := by
  simp only [rootProduct,Polynomial.map_prod,Polynomial.map_pow,Polynomial.map_sub,
    Polynomial.map_X,Polynomial.map_C]

theorem selector_map {B : Type*} [CommRing B] (φ : A →+* B)
    (β f₂ : A[X]) (a : A) :
    selector (β.map φ) (f₂.map φ) (φ a) = φ (selector β f₂ a) := by
  simp [selector]

end KhanSL2.Factorization.WeightedRoots



