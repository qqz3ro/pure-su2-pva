module

public import KhanSL2.Conditional.BGGAction


@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

/-! # Actual BGG cycles and their coefficient action -/

noncomputable section
open scoped DirectSum KhanSL2.Conditional
namespace KhanSL2.Conditional
open BGGBridge BGGComplex

local instance homologyAction_termAddCommGroup (B p : ℕ) : AddCommGroup (Term B p) := inferInstance
local instance homologyAction_termComplexModule (B p : ℕ) : Module ℂ (Term B p) := inferInstance

local instance homologyAction_complexCyclesAddCommGroup (B p : ℕ) : AddCommGroup (Cycles B p) := inferInstance
local instance homologyAction_complexCyclesModule (B p : ℕ) : Module ℂ (Cycles B p) := inferInstance
local instance homologyAction_kAddCommGroup (B p : ℕ) : AddCommGroup (K B p) := inferInstance
local instance homologyAction_kComplexModule (B p : ℕ) : Module ℂ (K B p) := inferInstance
/-- Actual cycles with their canonical coefficient-ring module structure. -/
abbrev CoefficientCycles (B p : ℕ) := Depth.cycles (Term B) (bggDifferential B) p

local instance homologyAction_coefficientCyclesAddCommGroup (B p : ℕ) :
    AddCommGroup (CoefficientCycles B p) := inferInstance
local instance homologyAction_coefficientCyclesComplexModule (B p : ℕ) :
    Module ℂ (CoefficientCycles B p) := inferInstance
local instance homologyAction_coefficientCyclesModule (B p : ℕ) :
    Module (CoefficientRing B) (CoefficientCycles B p) := inferInstance

/-- Forgetting the coefficient action changes no cycle or complex scalar. -/
def coefficientCyclesForget (B p : ℕ) : CoefficientCycles B p ≃ₗ[ℂ] Cycles B p := by
  cases p <;> exact LinearEquiv.refl ℂ _

@[simp] theorem coefficientCyclesForget_coe (B p : ℕ) (x : CoefficientCycles B p) :
    (coefficientCyclesForget B p x).val = x.val := by cases p <;> rfl

@[simp] theorem coefficientCyclesForget_symm_coe (B p : ℕ) (x : Cycles B p) :
    ((coefficientCyclesForget B p).symm x).val = x.val := by cases p <;> rfl

/-- The prescribed comparison evaluated on an actual cycle. -/
def coefficientCyclesToK (B p : ℕ) : CoefficientCycles B p →ₗ[ℂ] K B p :=
  (homologyEquivK B p).toLinearMap.comp
    (((LinearMap.range (differential B p)).comap (Cycles B p).subtype).mkQ.comp
      (coefficientCyclesForget B p).toLinearMap)

/-- Every coefficient cycle is a finite sum of homogeneous cycles. -/
def sumCyclesToCoefficientCycles (B p : ℕ) : CycleSum B p →ₗ[ℂ] CoefficientCycles B p :=
  (coefficientCyclesForget B p).symm.toLinearMap.comp (sumCyclesToCycles B p)

theorem sumCyclesToCoefficientCycles_surjective (B p : ℕ) :
    Function.Surjective (sumCyclesToCoefficientCycles B p) :=
  (coefficientCyclesForget B p).symm.surjective.comp
    (sumCyclesToCycles_bijective B p).2

@[simp] theorem sumCyclesToCoefficientCycles_val (B p : ℕ) (x : CycleSum B p) :
    (sumCyclesToCoefficientCycles B p x).val =
      DirectSum.lmap (componentCyclesToTerm B p) x := by
  simp only [sumCyclesToCoefficientCycles, LinearMap.comp_apply,
    LinearEquiv.coe_coe, coefficientCyclesForget_symm_coe]
  rfl

/-- Taking the class of a sum uses the specified comparison in each spin. -/
theorem coefficientCyclesToK_sumCycles (B p : ℕ) (x : CycleSum B p) :
    coefficientCyclesToK B p (sumCyclesToCoefficientCycles B p x) =
      (Modules.kTotalEquivBGG B p).symm
        (DirectSum.lmap (fun S : ℤ => (bggWindow p B S).boundaries.mkQ) x) := by
  simp only [coefficientCyclesToK, sumCyclesToCoefficientCycles, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  change (Modules.kTotalEquivBGG B p).symm
    (cyclesToBGGTotal B p (sumCyclesToCycles B p x)) = _
  have h := (cyclesEquivSum B p).apply_symm_apply x
  change cyclesEquivSum B p (sumCyclesToCycles B p x) = x at h
  exact congrArg (fun y : CycleSum B p => (Modules.kTotalEquivBGG B p).symm
    (DirectSum.lmap (fun S : ℤ => (bggWindow p B S).boundaries.mkQ) y)) h

theorem coefficientCyclesToK_sumCycles_lof (B p : ℕ) (S : ℤ) (x : ComponentCycles B p S) :
    coefficientCyclesToK B p (sumCyclesToCoefficientCycles B p
      (DirectSum.lof ℂ ℤ (fun T => ↥(ComponentCycles B p T)) S x)) =
      DirectSum.lof ℂ ℤ (fun T => Current.K p B T) S
        ((Current.kEquivBGGHomology p B S).symm (Submodule.Quotient.mk x)) := by
  have h₁ := coefficientCyclesToK_sumCycles B p
    (DirectSum.lof ℂ ℤ (fun T => ↥(ComponentCycles B p T)) S x)
  have h₂ := congrArg (Modules.kTotalEquivBGG B p).symm
    (DirectSum.lmap_lof (fun T : ℤ => (bggWindow p B T).boundaries.mkQ) S x)
  have h₃ := DirectSum.lmap_lof
    (fun T : ℤ => (Current.kEquivBGGHomology p B T).symm.toLinearMap) S
    (Submodule.Quotient.mk x)
  exact h₁.trans (h₂.trans h₃)

/-- The actual shift preserves assembled cycles. -/
def coefficientCyclesPower (m B p : ℕ) : Module.End ℂ (CoefficientCycles B p) where
  toFun x := ⟨coefficientPower m B p x.val, by
    cases p with
    | zero => exact Submodule.mem_top
    | succ p =>
      change differential B p (coefficientPower m B (p + 1) x.val) = 0
      rw [← coefficientPower_differential]
      have hx : differential B p x.val = 0 := x.property
      rw [hx, map_zero]⟩
  map_add' x y := Subtype.ext ((coefficientPower m B p).map_add x.val y.val)
  map_smul' c x := Subtype.ext ((coefficientPower m B p).map_smul c x.val)

@[simp] theorem coefficientCyclesPower_val (m B p : ℕ) (x : CoefficientCycles B p) :
    (coefficientCyclesPower m B p x).val = coefficientPower m B p x.val := rfl

end KhanSL2.Conditional
