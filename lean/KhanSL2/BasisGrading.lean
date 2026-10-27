module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Basic.Complex.Basic

@[expose] public section

/-! Direct-sum gradings and homogeneous projections for a graded basis. -/

noncomputable section

namespace KhanSL2.BasisGrading

variable {α ι : Type*} [DecidableEq ι] (degree : α → ι)

def piece (d : ι) : Submodule ℂ (α →₀ ℂ) :=
  Finsupp.supported ℂ ℂ {a | degree a = d}

def projection (d : ι) : Module.End ℂ (α →₀ ℂ) where
  toFun := Finsupp.filter (fun a => degree a = d)
  map_add' := fun _ _ => Finsupp.filter_add
  map_smul' := fun _ _ => Finsupp.filter_smul

@[simp] theorem projection_apply (d : ι) (v : α →₀ ℂ) (a : α) :
    projection degree d v a = if degree a = d then v a else 0 := rfl

omit [DecidableEq ι] in
theorem single_mem (a : α) (r : ℂ) :
    Finsupp.single a r ∈ piece degree (degree a) :=
  Finsupp.single_mem_supported ℂ r rfl

theorem projection_mem (d : ι) (v : α →₀ ℂ) :
    projection degree d v ∈ piece degree d := by
  rw [piece, Finsupp.mem_supported']
  intro a ha
  simp only [Set.mem_ofPred_eq] at ha
  simp [ha]

theorem projection_of_mem {d : ι} {v : α →₀ ℂ} (hv : v ∈ piece degree d) :
    projection degree d v = v := by
  ext a
  by_cases ha : degree a = d
  · simp [ha]
  · have hz := (Finsupp.mem_supported' ℂ v).mp hv a ha
    simp [ha, hz]

theorem projection_of_mem_ne {d e : ι} (hde : d ≠ e) {v : α →₀ ℂ}
    (hv : v ∈ piece degree e) : projection degree d v = 0 := by
  ext a
  by_cases ha : degree a = d
  · have hae : degree a ≠ e := by simpa [ha] using hde
    have hz := (Finsupp.mem_supported' ℂ v).mp hv a hae
    simp [ha, hz]
  · simp [ha]

@[simp] theorem projection_single (d : ι) (a : α) (r : ℂ) :
    projection degree d (Finsupp.single a r) =
      if degree a = d then Finsupp.single a r else 0 := by
  by_cases h : degree a = d
  · simpa [h] using projection_of_mem degree (single_mem degree a r)
  · simp only [ite_eq_right h]
    exact projection_of_mem_ne degree (Ne.symm h) (single_mem degree a r)

def coaction : (α →₀ ℂ) →ₗ[ℂ] (ι →₀ (α →₀ ℂ)) :=
  Finsupp.linearCombination ℂ fun a =>
    Finsupp.single (degree a) (Finsupp.single a 1)

omit [DecidableEq ι] in
@[simp] theorem coaction_single (a : α) (r : ℂ) :
    coaction degree (Finsupp.single a r) =
      Finsupp.single (degree a) (Finsupp.single a r) := by
  simp [coaction, Finsupp.linearCombination_single]

theorem coaction_apply (v : α →₀ ℂ) (d : ι) :
    coaction degree v d = projection degree d v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single a r =>
    simp only [coaction_single, projection_single, Finsupp.single_apply]

theorem coaction_of_mem {d : ι} {v : α →₀ ℂ} (hv : v ∈ piece degree d) :
    coaction degree v = Finsupp.single d v := by
  ext e a
  rw [coaction_apply]
  by_cases h : d = e
  · subst e
    rw [projection_of_mem degree hv, Finsupp.single_eq_same]
  · rw [projection_of_mem_ne degree (Ne.symm h) hv, Finsupp.single_eq_of_ne' h]

omit [DecidableEq ι] in
theorem piece_iSup_eq_top : (⨆ d, piece degree d) = ⊤ := by
  suffices h : ∀ v : α →₀ ℂ, v ∈ ⨆ d, piece degree d from top_unique (fun v _ => h v)
  intro v
  induction v using Finsupp.induction_linear with
  | zero => exact (⨆ d, piece degree d).zero_mem
  | add p q hp hq => exact (⨆ d, piece degree d).add_mem hp hq
  | single a r => exact Submodule.mem_iSup_of_mem (degree a) (single_mem degree a r)

theorem coaction_directSum_coe (v : DirectSum ι fun d => piece degree d) (d : ι) :
    coaction degree (DirectSum.coeLinearMap (piece degree) v) d = (v d : α →₀ ℂ) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of e v =>
    rw [DirectSum.coeLinearMap_of, coaction_of_mem degree v.property]
    by_cases h : e = d
    · subst e
      simp
    · simp [Finsupp.single_eq_of_ne' h, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add v w hv hw =>
    simp only [map_add]
    change coaction degree (DirectSum.coeLinearMap (piece degree) v) d +
      coaction degree (DirectSum.coeLinearMap (piece degree) w) d =
        (v d : α →₀ ℂ) + (w d : α →₀ ℂ)
    rw [hv, hw]

theorem isInternal : DirectSum.IsInternal (piece degree) := by
  change Function.Bijective (DirectSum.coeLinearMap (piece degree))
  constructor
  · intro v w hvw
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    rw [← coaction_directSum_coe degree v d, ← coaction_directSum_coe degree w d, hvw]
  · apply LinearMap.range_eq_top.mp
    rw [DirectSum.range_coeLinearMap, piece_iSup_eq_top]

/-- A homogeneous linear map commutes with the appropriate graded projections. -/
theorem projection_linearMap (F : Module.End ℂ (α →₀ ℂ)) (shift : ι → ι)
    (hinj : Function.Injective shift)
    (hF : ∀ d v, v ∈ piece degree d → F v ∈ piece degree (shift d))
    (d : ι) (v : α →₀ ℂ) :
    projection degree (shift d) (F v) = F (projection degree d v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single a r =>
    rw [projection_single]
    by_cases h : degree a = d
    · rw [ite_eq_left h]
      exact projection_of_mem degree (h ▸ hF _ _ (single_mem degree a r))
    · rw [ite_eq_right h, map_zero]
      apply projection_of_mem_ne degree
      · exact fun he => h (hinj he.symm)
      · exact hF _ _ (single_mem degree a r)

end KhanSL2.BasisGrading
