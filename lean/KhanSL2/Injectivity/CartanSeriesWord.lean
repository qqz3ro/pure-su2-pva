module

public import KhanSL2.Injectivity.CartanSeriesSlots
public import KhanSL2.Injectivity.CartanJets
public import Mathlib.Data.List.FinRange

/-! Coefficients of the ordered source series are precisely the
factorial-normalized source representative words. -/

@[expose] public section
noncomputable section

namespace KhanSL2.Injectivity

theorem orderedProduct_sum {A : Type*} [Ring A] {m n : ℕ} (f : Fin (m + n) → A) :
    orderedProduct f = orderedProduct (fun i => f (Fin.castAdd n i)) *
      orderedProduct (fun j => f (Fin.natAdd m j)) := by
  rw [orderedProduct, List.ofFn_add, List.prod_append]
  rfl

theorem orderedProduct_prod {A : Type*} [Ring A] {m n : ℕ} (f : Fin m × Fin n → A) :
    orderedProduct (fun k => f (finProdFinEquiv.symm k)) =
      orderedProduct (fun i => orderedProduct (fun j => f (i,j))) := by
  rw [orderedProduct, List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  have hij : (i : ℕ) * n + j < m * n :=
    (Nat.add_lt_add_left j.isLt _).trans_le (by
      simpa only [Nat.succ_mul] using Nat.mul_le_mul_right n i.isLt)
  have he : (⟨(i : ℕ) * n + j, hij⟩ : Fin (m * n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [he, Equiv.symm_apply_apply]

namespace Cartan

open FiniteExterior.Series

theorem sourceLinearSeries_xProduct (r s : ℕ) (i : Fin r) :
    orderedProduct (fun k : Fin 2 => (sourceLinearSeries r s (.inl (i,k))).val) =
      axisSeries (.inl i) (fun n => dividedTranslate n xBase) := by
  simp [orderedProduct_succ, Fin.tail_def, sourceLinearSeries, axisLinear,
    linearSeriesOfCoefficients]
  rw [axisSeries_mul]
  apply congrArg (axisSeries (R := Cochain) (.inl i : Fin r ⊕ Fin s))
  funext n
  rw [dividedTranslate_xBase]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [one_smul, mul_smul_comm, Nat.cast_add, Nat.cast_one, generator]

theorem sourceLinearSeries_yProduct (r s : ℕ) (a : Fin s) :
    orderedProduct (fun k : Fin 3 => (sourceLinearSeries r s (.inr (a,k))).val) =
      axisSeries (.inr a) (fun n => dividedTranslate n yBase) := by
  simp [orderedProduct_succ, Fin.tail_def, sourceLinearSeries, axisLinear,
    linearSeriesOfCoefficients]
  rw [← mul_assoc, axisSeries_mul, axisSeries_mul]
  apply congrArg (axisSeries (R := Cochain) (.inr a : Fin r ⊕ Fin s))
  funext n
  rw [dividedTranslate_yBase]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [one_smul, Finset.sum_mul, generator]

theorem sourceLinearSeries_grouped (r s : ℕ) :
    orderedProduct (fun j => (slotLinearSeries r s j).val) =
      orderedProduct (fun i : Fin r => axisSeries (.inl i) (fun n => dividedTranslate n xBase)) *
      orderedProduct (fun a : Fin s => axisSeries (.inr a) (fun n => dividedTranslate n yBase)) := by
  rw [orderedProduct_sum]
  have hx : (fun i : Fin (r * 2) => (slotLinearSeries r s (Fin.castAdd (s*3) i)).val) =
      (fun i => (sourceLinearSeries r s (.inl (finProdFinEquiv.symm i))).val) := by
    funext i
    simp [slotLinearSeries, sourceSlotEquiv]
  have hy : (fun a : Fin (s * 3) => (slotLinearSeries r s (Fin.natAdd (r*2) a)).val) =
      (fun a => (sourceLinearSeries r s (.inr (finProdFinEquiv.symm a))).val) := by
    funext a
    simp [slotLinearSeries, sourceSlotEquiv]
  rw [hx, hy, orderedProduct_prod (fun p : Fin r × Fin 2 => (sourceLinearSeries r s (.inl p)).val),
    orderedProduct_prod (fun p : Fin s × Fin 3 => (sourceLinearSeries r s (.inr p)).val)]
  simp only [sourceLinearSeries_xProduct, sourceLinearSeries_yProduct]

def sourceVariables (r s : ℕ) : List (Fin r ⊕ Fin s) :=
  List.ofFn Sum.inl ++ List.ofFn Sum.inr

theorem sourceVariables_nodup (r s : ℕ) : (sourceVariables r s).Nodup := by
  rw [sourceVariables, List.nodup_append']
  refine ⟨List.nodup_ofFn.mpr Sum.inl_injective, List.nodup_ofFn.mpr Sum.inr_injective, ?_⟩
  intro a ha hb
  simp only [List.mem_ofFn] at ha hb
  obtain ⟨i,rfl⟩ := ha
  obtain ⟨j,hj⟩ := hb
  cases hj

theorem mem_sourceVariables (r s : ℕ) (v : Fin r ⊕ Fin s) : v ∈ sourceVariables r s := by
  cases v <;> simp [sourceVariables, List.mem_ofFn]

def sourceVariableCoefficient (r s : ℕ) : (Fin r ⊕ Fin s) → ℕ → Cochain
  | .inl _, n => dividedTranslate n xBase
  | .inr _, n => dividedTranslate n yBase

@[simp] theorem sourceVariableCoefficient_inl (r s : ℕ) (i : Fin r) :
    sourceVariableCoefficient r s (.inl i) = fun n => dividedTranslate n xBase := rfl

@[simp] theorem sourceVariableCoefficient_inr (r s : ℕ) (a : Fin s) :
    sourceVariableCoefficient r s (.inr a) = fun n => dividedTranslate n yBase := rfl

theorem sourceLinearSeries_eq_axisProduct (r s : ℕ) :
    orderedProduct (fun j => (slotLinearSeries r s j).val) =
      axisProduct (sourceVariables r s) (sourceVariableCoefficient r s) := by
  rw [sourceLinearSeries_grouped]
  simp [axisProduct, sourceVariables, List.map_append, List.prod_append,
    List.map_ofFn, orderedProduct, Function.comp_def]

theorem coeff_sourceLinearSeries (r s : ℕ) (d : (Fin r ⊕ Fin s) →₀ ℕ) :
    MvPowerSeries.coeff (R := Cochain) d (orderedProduct fun j => (slotLinearSeries r s j).val) =
      normalizedWord (List.ofFn fun i => d (.inl i)) (List.ofFn fun a => d (.inr a)) := by
  rw [sourceLinearSeries_eq_axisProduct]
  change axisProduct _ _ d = _
  rw [axisProduct_coeff _ _ (sourceVariables_nodup r s) d
    (fun v hv => (hv (mem_sourceVariables r s v)).elim)]
  simp [sourceVariables, List.map_append, List.prod_append, List.map_ofFn,
    sourceVariableCoefficient, normalizedWord, dividedJetProduct, Function.comp_def]

/-- Exact coefficient adjunction for the finite Cartan generating polynomial. -/
theorem coeff_chainPolynomial (r s : ℕ) (c : Cochain) (d : (Fin r ⊕ Fin s) →₀ ℕ) :
    (chainPolynomial r s c).coeff d = FiniteExterior.coefficientPairing c
      (normalizedWord (List.ofFn fun i => d (.inl i)) (List.ofFn fun a => d (.inr a))) := by
  have h := congrArg (MvPowerSeries.coeff (R := ℂ) d) (chainPolynomial_eq_series_pairing r s c)
  simpa only [MvPolynomial.coeff_coe, coeff_pairing, coeff_sourceLinearSeries] using h

end Cartan
end KhanSL2.Injectivity
