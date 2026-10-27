module

public import KhanSL2.StrongMacdonald.HomDer
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# Exponentials of locally nilpotent even derivations

* `LocNil D`: every element is killed by some power of `D`.
* `IsDer.pow_mul`: the general Leibniz rule `D^n (x y) = Σ_k C(n,k) D^k x · D^(n-k) y` for an
  even derivation.
* `locNil_of_gen`: for an even derivation, local nilpotency can be checked on generators.
* `expDer D`: the exponential `Σ_n D^n / n!` of a locally nilpotent even derivation, an algebra
  endomorphism of `W`; `expDer_apply_of` computes it with any nilpotency cutoff and
  `expDer_of_eq_zero` shows it fixes the kernel of `D`.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

/-- `D` is locally nilpotent. -/
def LocNil (D : Module.End ℂ W) : Prop := ∀ x, ∃ n, (D ^ n) x = 0

/-- Once a power of `D` kills `x`, all higher powers do. -/
theorem pow_apply_eq_zero_of_le {D : Module.End ℂ W} {x : W} {n m : ℕ} (hx : (D ^ n) x = 0)
    (h : n ≤ m) : (D ^ m) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, pow_add, Module.End.mul_apply, hx, map_zero]

theorem LocNil.smul {D : Module.End ℂ W} (hN : LocNil D) (t : ℂ) : LocNil (t • D) := by
  intro x
  obtain ⟨n, hn⟩ := hN x
  exact ⟨n, by rw [smul_pow, LinearMap.smul_apply, hn, smul_zero]⟩

/-- `t • D` is again a derivation (a restatement of `IsDer.smul` with `t` last). -/
theorem IsDer.smul' {p : ℕ} {D : Module.End ℂ W} (hD : IsDer p D) (t : ℂ) :
    IsDer p (t • D) :=
  IsDer.smul t hD

/-! ## The Leibniz rule -/

theorem IsDer.pow_mul_nsmul {D : Module.End ℂ W} (hD : IsDer 0 D) (n : ℕ) (x y : W) :
    (D ^ n) (x * y) =
      ∑ k ∈ Finset.range (n + 1), n.choose k • ((D ^ k) x * (D ^ (n - k)) y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_choose_succ_nsmul (fun i j => (D ^ i) x * (D ^ j) y) n, pow_succ',
      Module.End.mul_apply, ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : n + 1 - k = n - k + 1 := by omega
    rw [map_nsmul, ← nsmul_add, hD, Function.iterate_zero_apply, h1, pow_succ', pow_succ',
      Module.End.mul_apply, Module.End.mul_apply, add_comm]

/-- General Leibniz rule for an even derivation. -/
theorem IsDer.pow_mul {D : Module.End ℂ W} (hD : IsDer 0 D) (n : ℕ) (x y : W) :
    (D ^ n) (x * y) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) • ((D ^ k) x * (D ^ (n - k)) y) := by
  rw [hD.pow_mul_nsmul]
  simp only [Nat.cast_smul_eq_nsmul]

/-- If `D^a x = 0` and `D^b y = 0` then `D^(a+b) (x y) = 0`. -/
theorem IsDer.pow_mul_eq_zero {D : Module.End ℂ W} (hD : IsDer 0 D) {x y : W} {a b : ℕ}
    (hx : (D ^ a) x = 0) (hy : (D ^ b) y = 0) : (D ^ (a + b)) (x * y) = 0 := by
  rw [hD.pow_mul_nsmul]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases le_or_gt a k with hk | hk
  · rw [pow_apply_eq_zero_of_le hx hk, zero_mul, smul_zero]
  · rw [pow_apply_eq_zero_of_le hy (by omega), mul_zero, smul_zero]

/-- Local nilpotency can be checked on generators. -/
theorem locNil_of_gen {D : Module.End ℂ W} (hD : IsDer 0 D)
    (h : ∀ g : Gen, ∃ n, (D ^ n) g.elt = 0) : LocNil D := by
  intro x
  refine induction_gen (P := fun x => ∃ n, (D ^ n) x = 0) ?_ ?_ ?_ ?_ ?_ ?_ x
  · exact ⟨0, map_zero _⟩
  · exact ⟨1, by rw [pow_one, hD.map_one]⟩
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨max a b, by rw [map_add, pow_apply_eq_zero_of_le ha (le_max_left a b),
      pow_apply_eq_zero_of_le hb (le_max_right a b), add_zero]⟩
  · rintro r x ⟨a, ha⟩
    exact ⟨a, by rw [map_smul, ha, smul_zero]⟩
  · rintro g x ⟨b, hb⟩
    obtain ⟨a, ha⟩ := h (.s g)
    exact ⟨a + b, hD.pow_mul_eq_zero ha hb⟩
  · rintro m x ⟨b, hb⟩
    obtain ⟨a, ha⟩ := h (.p m)
    exact ⟨a + b, hD.pow_mul_eq_zero ha hb⟩

/-! ## Truncated exponentials -/

/-- The truncated exponential series `Σ_{n < N} D^n / n!`. -/
def expTrunc (D : Module.End ℂ W) (N : ℕ) : Module.End ℂ W :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹) • D ^ n

theorem expTrunc_apply (D : Module.End ℂ W) (N : ℕ) (x : W) :
    expTrunc D N x = ∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹) • (D ^ n) x := by
  simp [expTrunc, LinearMap.sum_apply]

/-- Enlarging the cutoff beyond a nilpotency index does not change the truncation. -/
theorem expTrunc_eq_of_le {D : Module.End ℂ W} {x : W} {N M : ℕ} (hx : (D ^ N) x = 0)
    (h : N ≤ M) : expTrunc D M x = expTrunc D N x := by
  rw [expTrunc_apply, expTrunc_apply]
  refine (Finset.sum_subset (Finset.range_subset_range.mpr h) fun n _ hn => ?_).symm
  rw [Finset.mem_range, not_lt] at hn
  rw [pow_apply_eq_zero_of_le hx hn, smul_zero]

/-- Any two nilpotency cutoffs give the same truncation. -/
theorem expTrunc_eq_expTrunc {D : Module.End ℂ W} {x : W} {N M : ℕ} (hN : (D ^ N) x = 0)
    (hM : (D ^ M) x = 0) : expTrunc D N x = expTrunc D M x := by
  rw [← expTrunc_eq_of_le hN (le_max_left N M), ← expTrunc_eq_of_le hM (le_max_right N M)]

/-! ## The exponential -/

/-- The exponential of a locally nilpotent operator, as a linear map. -/
def expLin (D : Module.End ℂ W) (hN : LocNil D) : Module.End ℂ W where
  toFun x := expTrunc D (Classical.choose (hN x)) x
  map_add' x y := by
    have hx := Classical.choose_spec (hN x)
    have hy := Classical.choose_spec (hN y)
    have hxy := Classical.choose_spec (hN (x + y))
    set a := Classical.choose (hN x)
    set b := Classical.choose (hN y)
    have hx' : (D ^ (a + b)) x = 0 := pow_apply_eq_zero_of_le hx (Nat.le_add_right a b)
    have hy' : (D ^ (a + b)) y = 0 := pow_apply_eq_zero_of_le hy (Nat.le_add_left b a)
    have hs : (D ^ (a + b)) (x + y) = 0 := by rw [map_add, hx', hy', add_zero]
    rw [expTrunc_eq_expTrunc hxy hs, map_add, expTrunc_eq_expTrunc hx' hx,
      expTrunc_eq_expTrunc hy' hy]
  map_smul' r x := by
    have hx := Classical.choose_spec (hN x)
    have hrx := Classical.choose_spec (hN (r • x))
    have hs : (D ^ Classical.choose (hN x)) (r • x) = 0 := by rw [map_smul, hx, smul_zero]
    rw [RingHom.id_apply, expTrunc_eq_expTrunc hrx hs, map_smul]

theorem expLin_apply_of {D : Module.End ℂ W} (hN : LocNil D) {x : W} {N : ℕ}
    (hx : (D ^ N) x = 0) : expLin D hN x = expTrunc D N x :=
  expTrunc_eq_expTrunc (Classical.choose_spec (hN x)) hx

/-- Coefficient identity `C(n,k) / n! = 1 / (k! (n-k)!)`. -/
theorem inv_factorial_mul_choose {n k : ℕ} (hk : k ≤ n) :
    ((n.factorial : ℂ))⁻¹ * (n.choose k : ℂ) =
      ((k.factorial : ℂ))⁻¹ * (((n - k).factorial : ℂ))⁻¹ := by
  have h : (n.choose k : ℂ) * k.factorial * (n - k).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have h1 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h2 : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (n.choose k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  rw [← h]
  field_simp

theorem expLin_mul {D : Module.End ℂ W} (hD : IsDer 0 D) (hN : LocNil D) (x y : W) :
    expLin D hN (x * y) = expLin D hN x * expLin D hN y := by
  obtain ⟨a, ha⟩ := hN x
  obtain ⟨b, hb⟩ := hN y
  set M := a + b
  have hxM : (D ^ M) x = 0 := pow_apply_eq_zero_of_le ha (Nat.le_add_right a b)
  rw [expLin_apply_of hN (hD.pow_mul_eq_zero ha hb), expLin_apply_of hN hxM, expTrunc_apply,
    expTrunc_apply, Finset.sum_mul]
  -- expand the Leibniz rule and reindex the Cauchy product
  have hL : ∀ n ∈ Finset.range M, ((n.factorial : ℂ)⁻¹) • (D ^ n) (x * y) =
      ∑ k ∈ Finset.range (n + 1),
        (((k.factorial : ℂ)⁻¹) • (D ^ k) x) *
          (((n - k).factorial : ℂ)⁻¹ • (D ^ (n - k)) y) := by
    intro n _
    rw [hD.pow_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [smul_smul, inv_factorial_mul_choose hk', smul_mul_smul_comm]
  rw [Finset.sum_congr rfl hL,
    Finset.sum_range_diag_flip M fun k l =>
      (((k.factorial : ℂ)⁻¹) • (D ^ k) x) * ((l.factorial : ℂ)⁻¹ • (D ^ l) y)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.mul_sum, ← expTrunc_apply]
  rcases le_or_gt a k with hak | hak
  · rw [pow_apply_eq_zero_of_le ha hak, smul_zero, zero_mul, zero_mul]
  · have hy' : (D ^ (M - k)) y = 0 := pow_apply_eq_zero_of_le hb (by omega)
    rw [expLin_apply_of hN hy']

/-- The exponential of a locally nilpotent even derivation, an algebra endomorphism. -/
def expDer (D : Module.End ℂ W) (hD : IsDer 0 D) (hN : LocNil D) : W →ₐ[ℂ] W :=
  AlgHom.ofLinearMap (expLin D hN)
    (by
      rw [expLin_apply_of hN (show (D ^ 1) (1 : W) = 0 by rw [pow_one, hD.map_one])]
      simp [expTrunc_apply])
    (expLin_mul hD hN)

theorem expDer_apply (D : Module.End ℂ W) (hD : IsDer 0 D) (hN : LocNil D) (x : W) :
    expDer D hD hN x = expLin D hN x := rfl

theorem expDer_apply_of {D : Module.End ℂ W} (hD : IsDer 0 D) (hN : LocNil D) {x : W} {N : ℕ}
    (hx : (D ^ N) x = 0) :
    expDer D hD hN x = ∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹) • (D ^ n) x := by
  rw [expDer_apply, expLin_apply_of hN hx, expTrunc_apply]

theorem expDer_of_eq_zero {D : Module.End ℂ W} (hD : IsDer 0 D) (hN : LocNil D) {x : W}
    (hx : D x = 0) : expDer D hD hN x = x := by
  rw [expDer_apply_of hD hN (N := 1) (by rwa [pow_one])]
  simp

/-- The exponential of `t • D`, computed with a nilpotency cutoff of `D`. -/
theorem expDer_smul_of {D : Module.End ℂ W} (hD : IsDer 0 D) (hN : LocNil D) (t : ℂ) {x : W}
    {N : ℕ} (hx : (D ^ N) x = 0) :
    expDer (t • D) (hD.smul' t) (hN.smul t) x =
      ∑ n ∈ Finset.range N, (((n.factorial : ℂ)⁻¹) * t ^ n) • (D ^ n) x := by
  have hx' : ((t • D) ^ N) x = 0 := by rw [smul_pow, LinearMap.smul_apply, hx, smul_zero]
  rw [expDer_apply_of _ _ hx']
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_pow, LinearMap.smul_apply, smul_smul]

end KhanSL2.StrongMacdonald
