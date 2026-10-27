module

public import KhanSL2.Injectivity.CartanPolynomialEvaluation
public import KhanSL2.Injectivity.ExteriorSeries
public import KhanSL2.Injectivity.AxisSeries

/-! Degree-one generating series for the source-interleaved Cartan slots. -/

@[expose] public section
noncomputable section

namespace KhanSL2.FiniteExterior.Series

open KhanSL2.Injectivity

variable {σ α : Type*} [DecidableEq σ] [DecidableEq α] [GeneratorOrder α]

omit [GeneratorOrder α] in
@[simp] theorem coefficientPairing_generators (a b : α) :
    coefficientPairing (generator a) (generator b) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · simp [h, generator, monomial]
  · simp [h, Ne.symm h, generator, monomial, Finsupp.single_apply]

def axisLinear (v : σ) (color : ℕ → α) (scale : ℕ → ℂ) : LinearSeries σ α :=
  linearSeriesOfCoefficients (axisSeries v (fun n => scale n • generator (color n))) (by
    intro d
    refine ⟨color (d v), if d = Finsupp.single v (d v) then scale (d v) else 0, ?_⟩
    simp only [axisSeries]
    split_ifs <;> simp)

theorem pairing_axisLinear (m : α) (v : σ) (color : ℕ → α) (scale : ℕ → ℂ) :
    pairing (generator m) (axisLinear v color scale).val =
      axisSeries v (fun n => scale n * if m = color n then 1 else 0) := by
  apply MvPowerSeries.ext
  intro d
  change coefficientPairing (generator m)
    (axisSeries v (fun n => scale n • generator (color n)) d) =
    axisSeries v (fun n => scale n * if m = color n then 1 else 0) d
  simp only [axisSeries]
  by_cases h : d = Finsupp.single v (d v)
  · simp only [if_pos h, map_smul, coefficientPairing_generators, smul_eq_mul]
  · simp only [if_neg h, map_zero]

theorem pairing_axisLinear_same (v : σ) (color : ℕ → α)
    (hc : Function.Injective color) (scale : ℕ → ℂ) (j : ℕ) :
    pairing (generator (color j)) (axisLinear v color scale).val =
      MvPowerSeries.monomial (R := ℂ) (Finsupp.single v j) (scale j) := by
  rw [pairing_axisLinear]
  have h : (fun n => scale n * if color j = color n then 1 else 0) =
      (fun n => if n = j then scale j else 0) := by
    funext n
    by_cases hn : n = j
    · subst n; simp
    · simp [hc.eq_iff, hn, Ne.symm hn]
  rw [h, axisSeries_monomial]

theorem pairing_axisLinear_other (m : α) (v : σ) (color : ℕ → α)
    (h : ∀ n, m ≠ color n) (scale : ℕ → ℂ) :
    pairing (generator m) (axisLinear v color scale).val = 0 := by
  rw [pairing_axisLinear]
  apply MvPowerSeries.ext
  intro d
  change axisSeries v (fun n => scale n * if m = color n then 1 else 0) d = 0
  simp [axisSeries, h]

end KhanSL2.FiniteExterior.Series

namespace KhanSL2.Injectivity.Cartan

open FiniteExterior.Series

def sourceLinearSeries (r s : ℕ) : SourceSlot r s → LinearSeries (Fin r ⊕ Fin s) Mode
  | .inl (i, k) => if k = 0 then axisLinear (.inl i) Mode.neutral (fun _ => 1)
      else axisLinear (.inl i) Mode.cartan (fun j => (j : ℂ) + 1)
  | .inr (a, k) => if k = 0 then axisLinear (.inr a) Mode.neutral (fun _ => 1)
      else if k = 1 then axisLinear (.inr a) Mode.plus (fun _ => 1)
      else axisLinear (.inr a) Mode.minus (fun _ => 1)

def slotLinearSeries (r s : ℕ) (j : Fin (r * 2 + s * 3)) :
    LinearSeries (Fin r ⊕ Fin s) Mode :=
  sourceLinearSeries r s ((sourceSlotEquiv r s).symm j)

private theorem modeWeight_one {σ : Type*} [DecidableEq σ] (v : σ) (j : ℕ) :
    MvPowerSeries.monomial (R := ℂ) (Finsupp.single v j) 1 =
      ((MvPolynomial.X v ^ j : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) := by
  simp [MvPolynomial.X_pow_eq_monomial]

private theorem modeWeight_cartan {σ : Type*} [DecidableEq σ] (v : σ) (j : ℕ) :
    MvPowerSeries.monomial (R := ℂ) (Finsupp.single v j) ((j : ℂ) + 1) =
      MvPolynomial.toMvPowerSeries (((j + 1 : ℕ) : MvPolynomial σ ℂ) * MvPolynomial.X v ^ j) := by
  have hn : ((j + 1 : ℕ) : MvPolynomial σ ℂ) = MvPolynomial.C ((j : ℂ) + 1) := by simp
  rw [hn, MvPolynomial.C_mul_X_pow_eq_monomial]
  exact (MvPolynomial.coe_monomial _ _).symm

theorem pairing_axis_neutral {σ : Type*} [DecidableEq σ] (v : σ) (m : Mode) :
    pairing (generator m) (axisLinear v Mode.neutral (fun _ => 1)).val =
      match m with
      | .neutral j => ((MvPolynomial.X v ^ j : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ)
      | _ => 0 := by
  cases m with
  | neutral j => exact (pairing_axisLinear_same v Mode.neutral (fun _ _ h => Mode.neutral.inj h) (fun _ => 1) j).trans (modeWeight_one v j)
  | plus j => exact pairing_axisLinear_other (α := Mode) (.plus j) v Mode.neutral (by intro n h; cases h) (fun _ => 1)
  | minus j => exact pairing_axisLinear_other (α := Mode) (.minus j) v Mode.neutral (by intro n h; cases h) (fun _ => 1)
  | cartan j => exact pairing_axisLinear_other (α := Mode) (.cartan j) v Mode.neutral (by intro n h; cases h) (fun _ => 1)

theorem pairing_axis_plus {σ : Type*} [DecidableEq σ] (v : σ) (m : Mode) :
    pairing (generator m) (axisLinear v Mode.plus (fun _ => 1)).val =
      match m with
      | .plus j => ((MvPolynomial.X v ^ j : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ)
      | _ => 0 := by
  cases m with
  | neutral j => exact pairing_axisLinear_other (α := Mode) (.neutral j) v Mode.plus (by intro n h; cases h) (fun _ => 1)
  | plus j => exact (pairing_axisLinear_same v Mode.plus (fun _ _ h => Mode.plus.inj h) (fun _ => 1) j).trans (modeWeight_one v j)
  | minus j => exact pairing_axisLinear_other (α := Mode) (.minus j) v Mode.plus (by intro n h; cases h) (fun _ => 1)
  | cartan j => exact pairing_axisLinear_other (α := Mode) (.cartan j) v Mode.plus (by intro n h; cases h) (fun _ => 1)

theorem pairing_axis_minus {σ : Type*} [DecidableEq σ] (v : σ) (m : Mode) :
    pairing (generator m) (axisLinear v Mode.minus (fun _ => 1)).val =
      match m with
      | .minus j => ((MvPolynomial.X v ^ j : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ)
      | _ => 0 := by
  cases m with
  | neutral j => exact pairing_axisLinear_other (α := Mode) (.neutral j) v Mode.minus (by intro n h; cases h) (fun _ => 1)
  | plus j => exact pairing_axisLinear_other (α := Mode) (.plus j) v Mode.minus (by intro n h; cases h) (fun _ => 1)
  | minus j => exact (pairing_axisLinear_same v Mode.minus (fun _ _ h => Mode.minus.inj h) (fun _ => 1) j).trans (modeWeight_one v j)
  | cartan j => exact pairing_axisLinear_other (α := Mode) (.cartan j) v Mode.minus (by intro n h; cases h) (fun _ => 1)

theorem pairing_axis_cartan {σ : Type*} [DecidableEq σ] (v : σ) (m : Mode) :
    pairing (generator m) (axisLinear v Mode.cartan (fun j => (j : ℂ) + 1)).val =
      match m with
      | .cartan j => MvPolynomial.toMvPowerSeries
          (((j + 1 : ℕ) : MvPolynomial σ ℂ) * MvPolynomial.X v ^ j)
      | _ => 0 := by
  cases m with
  | neutral j => exact pairing_axisLinear_other (α := Mode) (.neutral j) v Mode.cartan (by intro n h; cases h) (fun n => (n : ℂ) + 1)
  | plus j => exact pairing_axisLinear_other (α := Mode) (.plus j) v Mode.cartan (by intro n h; cases h) (fun n => (n : ℂ) + 1)
  | minus j => exact pairing_axisLinear_other (α := Mode) (.minus j) v Mode.cartan (by intro n h; cases h) (fun n => (n : ℂ) + 1)
  | cartan j => exact (pairing_axisLinear_same v Mode.cartan (fun _ _ h => Mode.cartan.inj h) (fun n => (n : ℂ) + 1) j).trans (modeWeight_cartan v j)

theorem pairing_sourceLinearSeries (r s : ℕ) (m : Mode) (slot : SourceSlot r s) :
    pairing (generator m) (sourceLinearSeries r s slot).val =
      (sourceSlotWeight r s m slot : MvPowerSeries (Fin r ⊕ Fin s) ℂ) := by
  cases slot with
  | inl slot =>
    obtain ⟨i,k⟩ := slot
    fin_cases k <;> cases m <;>
      simp [sourceLinearSeries, sourceSlotWeight, pairing_axis_neutral,
        pairing_axis_cartan, Fin.ext_iff]
  | inr slot =>
    obtain ⟨a,k⟩ := slot
    fin_cases k <;> cases m <;>
      simp [sourceLinearSeries, sourceSlotWeight, pairing_axis_neutral,
        pairing_axis_plus, pairing_axis_minus, Fin.ext_iff]

theorem pairing_slotLinearSeries (r s : ℕ) (m : Mode) (j : Fin (r * 2 + s * 3)) :
    pairing (generator m) (slotLinearSeries r s j).val =
      (slotWeight r s m j : MvPowerSeries (Fin r ⊕ Fin s) ℂ) :=
  pairing_sourceLinearSeries r s m _

/-- The finite determinant polynomial is the coefficient pairing against the
ordered product of its linear generating series. -/
theorem chainPolynomial_eq_series_pairing (r s : ℕ) (c : Cochain) :
    (chainPolynomial r s c : MvPowerSeries (Fin r ⊕ Fin s) ℂ) =
      pairing c (orderedProduct fun j => (slotLinearSeries r s j).val) := by
  rw [pairing_orderedProduct_eq_determinantEvaluation]
  have hw : (fun m j => pairing (FiniteExterior.generator m) (slotLinearSeries r s j).val) =
      (fun m j => (slotWeight r s m j : MvPowerSeries (Fin r ⊕ Fin s) ℂ)) := by
    funext m j
    exact pairing_slotLinearSeries r s m j
  rw [hw]
  exact FiniteExterior.determinantEvaluation_map (r * 2 + s * 3) (slotWeight r s)
    (MvPolynomial.coeToMvPowerSeries.algHom ℂ) c

end KhanSL2.Injectivity.Cartan
