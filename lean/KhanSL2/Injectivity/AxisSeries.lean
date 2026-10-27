module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Data.Finsupp.Antidiagonal

/-! A series in one selected variable, allowing noncommutative coefficients. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace KhanSL2.Injectivity

variable {σ R : Type*} [DecidableEq σ] [Ring R]

def axisSeries (v : σ) (f : ℕ → R) : MvPowerSeries σ R :=
  fun d => if d = Finsupp.single v (d v) then f (d v) else 0

theorem axisSeries_apply (v : σ) (f : ℕ → R) (d) :
    axisSeries v f d = if d = Finsupp.single v (d v) then f (d v) else 0 := rfl

@[simp] theorem axisSeries_single (v : σ) (f : ℕ → R) (n : ℕ) :
    axisSeries v f (Finsupp.single v n) = f n := by simp [axisSeries]

theorem axisSeries_ne_zero_support {v : σ} {f : ℕ → R} {d : σ →₀ ℕ}
    (h : axisSeries v f d ≠ 0) : d = Finsupp.single v (d v) := by
  by_contra he
  exact h (if_neg he)

theorem axisSeries_monomial (v : σ) (n : ℕ) (a : R) :
    axisSeries v (fun j => if j = n then a else 0) =
      MvPowerSeries.monomial (R := R) (Finsupp.single v n) a := by
  apply MvPowerSeries.ext
  intro d
  rw [MvPowerSeries.coeff_monomial]
  change (if d = Finsupp.single v (d v) then (if d v = n then a else 0) else 0) = _
  by_cases hd : d = Finsupp.single v (d v)
  · rw [if_pos hd]
    by_cases hv : d v = n
    · rw [if_pos hv, if_pos (hd.trans (congrArg (Finsupp.single v) hv))]
    · rw [if_neg hv, if_neg (fun h => hv (by simpa using DFunLike.congr_fun h v))]
  · rw [if_neg hd, if_neg (fun h => hd (by subst d; simp))]

theorem axisSeries_mul (v : σ) (f g : ℕ → R) :
    axisSeries v f * axisSeries v g =
      axisSeries v (fun n => ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2) := by
  ext d
  by_cases hd : d = Finsupp.single v (d v)
  · conv_lhs => rw [hd]
    rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
    simp only [Finset.sum_map]
    change (∑ ij ∈ Finset.antidiagonal (d v),
      axisSeries v f (Finsupp.single v ij.1) * axisSeries v g (Finsupp.single v ij.2)) = _
    simp only [axisSeries_single]
    exact (if_pos hd).symm
  · rw [show MvPowerSeries.coeff (R := R) d (axisSeries v _) = 0 from if_neg hd,
      MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    change axisSeries v f ij.1 * axisSeries v g ij.2 = 0
    by_cases hi : axisSeries v f ij.1 = 0
    · rw [hi, zero_mul]
    by_cases hj : axisSeries v g ij.2 = 0
    · rw [hj, mul_zero]
    exfalso
    apply hd
    have he := Finset.mem_antidiagonal.mp hij
    have hvi := axisSeries_ne_zero_support hi
    have hvj := axisSeries_ne_zero_support hj
    calc
      d = ij.1 + ij.2 := he.symm
      _ = Finsupp.single v (ij.1 v) + Finsupp.single v (ij.2 v) := congrArg₂ (· + ·) hvi hvj
      _ = Finsupp.single v (d v) := by rw [← Finsupp.single_add, ← Finsupp.add_apply, he]

/-- If the second factor is independent of `v`, coefficient extraction has one
possible split, even with noncommutative coefficients. -/
theorem coeff_axisSeries_mul (v : σ) (f : ℕ → R) (G : MvPowerSeries σ R)
    (hG : ∀ d, d v ≠ 0 → G d = 0) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff (R := R) d (axisSeries v f * G) = f (d v) * G (d.erase v) := by
  rw [MvPowerSeries.coeff_mul]
  have hmem : (Finsupp.single v (d v), d.erase v) ∈ Finset.antidiagonal d := by
    rw [Finset.mem_antidiagonal]
    exact Finsupp.single_add_erase v d
  rw [Finset.sum_eq_single (Finsupp.single v (d v), d.erase v)]
  · change axisSeries v f (Finsupp.single v (d v)) * G (d.erase v) = _
    rw [axisSeries_single]
  · intro ij hij hne
    change axisSeries v f ij.1 * G ij.2 = 0
    by_cases hi : axisSeries v f ij.1 = 0
    · rw [hi, zero_mul]
    by_cases hj : ij.2 v ≠ 0
    · rw [hG ij.2 hj, mul_zero]
    have hj0 : ij.2 v = 0 := not_ne_iff.mp hj
    exfalso
    apply hne
    have he := Finset.mem_antidiagonal.mp hij
    have hvi := axisSeries_ne_zero_support hi
    have hiv : ij.1 v = d v := by
      have := DFunLike.congr_fun he v
      simpa [hj0] using this
    apply Prod.ext
    · exact hvi.trans (congrArg (Finsupp.single v) hiv)
    · apply Finsupp.ext
      intro w
      by_cases hw : w = v
      · subst w; simp [hj0]
      · have hh := DFunLike.congr_fun he w
        rw [Finsupp.add_apply, hvi] at hh
        simp only [Finsupp.single_apply, hw, Ne.symm hw, if_false, zero_add] at hh
        simpa [Finsupp.erase_ne hw] using hh
  · exact fun hn => (hn hmem).elim

def axisProduct (vs : List σ) (f : σ → ℕ → R) : MvPowerSeries σ R :=
  (vs.map fun v => axisSeries v (f v)).prod

@[simp] theorem axisProduct_nil (f : σ → ℕ → R) : axisProduct [] f = 1 := rfl

@[simp] theorem axisProduct_cons (v : σ) (vs : List σ) (f : σ → ℕ → R) :
    axisProduct (v :: vs) f = axisSeries v (f v) * axisProduct vs f := rfl

theorem axisProduct_unsupported (vs : List σ) (f : σ → ℕ → R)
    (d : σ →₀ ℕ) {w : σ} (hw : w ∉ vs) (hd : d w ≠ 0) :
    axisProduct vs f d = 0 := by
  induction vs generalizing d with
  | nil =>
    have hne : d ≠ 0 := by intro h; exact hd (h ▸ rfl)
    exact MvPowerSeries.coeff_one d |>.trans (if_neg hne)
  | cons v vs ih =>
    rw [axisProduct_cons]
    change MvPowerSeries.coeff (R := R) d (axisSeries v (f v) * axisProduct vs f) = 0
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    change axisSeries v (f v) ij.1 * axisProduct vs f ij.2 = 0
    by_cases hi : axisSeries v (f v) ij.1 = 0
    · rw [hi, zero_mul]
    have hv : w ≠ v := fun h => hw (by simp [h])
    have hiw : ij.1 w = 0 := by
      rw [axisSeries_ne_zero_support hi]
      simp [Finsupp.single_apply, hv, Ne.symm hv]
    have hjw : ij.2 w ≠ 0 := by
      have he := DFunLike.congr_fun (Finset.mem_antidiagonal.mp hij) w
      rw [Finsupp.add_apply, hiw, zero_add] at he
      exact he.symm ▸ hd
    rw [ih _ (fun h => hw (List.mem_cons_of_mem _ h)) hjw, mul_zero]

theorem axisProduct_coeff (vs : List σ) (f : σ → ℕ → R) (hn : vs.Nodup)
    (d : σ →₀ ℕ) (hd : ∀ w, w ∉ vs → d w = 0) :
    axisProduct vs f d = (vs.map fun v => f v (d v)).prod := by
  induction vs generalizing d with
  | nil =>
    have hd0 : d = 0 := by ext w; exact hd w (by simp)
    subst d
    change MvPowerSeries.coeff (R := R) 0 (1 : MvPowerSeries σ R) = 1
    exact MvPowerSeries.coeff_zero_one (R := R)
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hn
    change MvPowerSeries.coeff (R := R) d (axisSeries v (f v) * axisProduct vs f) = _
    rw [coeff_axisSeries_mul v _ _ (fun e he => axisProduct_unsupported vs f e hv he)]
    rw [ih hvs (d.erase v)]
    · congr 1
      apply congrArg List.prod
      apply List.map_congr_left
      intro w hw
      rw [Finsupp.erase_ne (show w ≠ v from fun h => hv (h ▸ hw))]
    · intro w hw
      by_cases he : w = v
      · subst w; simp
      · rw [Finsupp.erase_ne he]
        exact hd w (by simp [he, hw])

end KhanSL2.Injectivity
