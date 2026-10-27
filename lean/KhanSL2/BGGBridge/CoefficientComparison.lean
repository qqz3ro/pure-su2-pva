module

public import KhanSL2.BGGBridge.CoefficientWindows
public import KhanSL2.BGGBridgeStatement

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

/-!
# Coefficient naturality of the specified BGG homology comparison

The maps below descend the actual coefficient shifts through cycles and
boundaries. The canonical BGG contraction intertwines them with the already
constructed coefficient shifts on relative CE homology.
-/

noncomputable section
namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

local instance comparisonRelAdd : AddCommGroup RelChains := inferInstance
local instance comparisonRelModule : Module ℂ RelChains := inferInstance
local instance comparisonRelCyclesAdd (p B : ℕ) (S : ℤ) :
    AddCommGroup (relCycles (kDegree p B S)) := inferInstance
local instance comparisonRelCyclesModule (p B : ℕ) (S : ℤ) :
    Module ℂ (relCycles (kDegree p B S)) := inferInstance
local instance comparisonKAdd (p B : ℕ) (S : ℤ) : AddCommGroup (K p B S) := inferInstance
local instance comparisonKModule (p B : ℕ) (S : ℤ) : Module ℂ (K p B S) := inferInstance
local instance comparisonHarmQuotAdd : AddCommGroup (HarmN NB ⧸ relH NB) := inferInstance
local instance comparisonHarmQuotModule : Module ℂ (HarmN NB ⧸ relH NB) := inferInstance
local instance comparisonCyclesAdd (p B : ℕ) (S : ℤ) :
    AddCommGroup (bggWindow p B S).cycles := inferInstance
local instance comparisonCyclesModule (p B : ℕ) (S : ℤ) :
    Module ℂ (bggWindow p B S).cycles := inferInstance

local instance comparisonHomologyAdd (p B : ℕ) (S : ℤ) :
    AddCommGroup (BGGHomology p B S) := inferInstance
local instance comparisonHomologyModule (p B : ℕ) (S : ℤ) :
    Module ℂ (BGGHomology p B S) := inferInstance

/-- The fixed contraction projection intertwines the natural coefficient shifts. -/
theorem relContraction_proj_coefficientRelPower (m : ℕ) (x : RelChains) :
    relContraction.proj (Modules.coefficientRelPower m x) =
      coefficientBGGPower m (relContraction.proj x) := by
  change (qcN NB).proj (Jq (Modules.coefficientRelPower m x)) =
    coefficientBGGPower m ((qcN NB).proj (Jq x))
  rw [Jq_coefficientRelPower, qproj_coefficientChainQuotPower]

/-- The fixed contraction inclusion intertwines the same natural shifts. -/
theorem relContraction_incl_coefficientBGGPower (m : ℕ) (x : HarmN NB ⧸ relH NB) :
    relContraction.incl (coefficientBGGPower m x) =
      Modules.coefficientRelPower m (relContraction.incl x) := by
  change Jq.symm ((qcN NB).incl (coefficientBGGPower m x)) =
    Modules.coefficientRelPower m (Jq.symm ((qcN NB).incl x))
  apply Jq.injective
  exact (Jq.apply_symm_apply _).trans
    ((qincl_coefficientBGGPower m x).trans
      ((congrArg (coefficientChainQuotPower m) (Jq.apply_symm_apply _)).symm.trans
        (Jq_coefficientRelPower m _).symm))

/-- The actual coefficient shift restricts to BGG cycles. -/
def coefficientBGGCyclesPower (m p B : ℕ) (S : ℤ) :
    (bggWindow p B S).cycles →ₗ[ℂ] (bggWindow p B (S + m)).cycles :=
  (coefficientBGGPower m).restrict fun x hx => by
    refine ⟨coefficientBGGPower_mem_term m hx.1, ?_⟩
    change dHq NB (coefficientBGGPower m x) = 0
    rw [coefficientBGGPower_dHq, hx.2, map_zero]

@[simp] theorem coefficientBGGCyclesPower_coe (m p B : ℕ) (S : ℤ)
    (x : (bggWindow p B S).cycles) :
    (coefficientBGGCyclesPower m p B S x : HarmN NB ⧸ relH NB) =
      coefficientBGGPower m x := rfl

/-- The actual coefficient shift carries BGG boundaries to shifted boundaries. -/
theorem coefficientBGGCyclesPower_mem_boundaries (m p B : ℕ) (S : ℤ)
    (x : (bggWindow p B S).cycles) (hx : x ∈ (bggWindow p B S).boundaries) :
    coefficientBGGCyclesPower m p B S x ∈ (bggWindow p B (S + m)).boundaries := by
  obtain ⟨y, hy, hye⟩ := hx
  refine ⟨coefficientBGGPower m y, coefficientBGGPower_mem_term m hy, ?_⟩
  change dHq NB (coefficientBGGPower m y) = coefficientBGGPower m x
  rw [coefficientBGGPower_dHq, hye]
  rfl

/-- The natural coefficient power sum on actual BGG homology. -/
def coefficientBGGHomologyPower (m p B : ℕ) (S : ℤ) :
    BGGHomology p B S →ₗ[ℂ] BGGHomology p B (S + m) :=
  (bggWindow p B S).boundaries.mapQ (bggWindow p B (S + m)).boundaries
    (coefficientBGGCyclesPower m p B S)
    (fun x hx => coefficientBGGCyclesPower_mem_boundaries m p B S x hx)

@[simp] theorem coefficientBGGHomologyPower_mk (m p B : ℕ) (S : ℤ)
    (x : (bggWindow p B S).cycles) :
    coefficientBGGHomologyPower m p B S (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (coefficientBGGCyclesPower m p B S x) := rfl

/-- The specified contraction projection restricted to actual relative cycles. -/
def comparisonProjectionCycles (p B : ℕ) (S : ℤ) :
    relCycles (kDegree p B S) →ₗ[ℂ] (bggWindow p B S).cycles :=
  (kWindow p B S).cyclesMap (bggWindow p B S) relContraction.proj
    relContraction.proj_comp_dM (fun _ hx => proj_mem_bggTerm hx)

/-- The canonical homology comparison on a specified cycle representative. -/
theorem kEquivBGGHomology_coefficientClass (p B : ℕ) (S : ℤ) (x : RelChains)
    (hx : x ∈ relCycles (kDegree p B S)) :
    kEquivBGGHomology p B S (Modules.coefficientClass p B S x hx) =
      (Submodule.Quotient.mk (comparisonProjectionCycles p B S ⟨x, hx⟩) :
        BGGHomology p B S) := rfl

/-- Naturality on a specified actual relative cycle. -/
theorem kEquivBGGHomology_coefficientClassPower (m p B : ℕ) (S : ℤ)
    (z : relCycles (kDegree p B S)) :
    kEquivBGGHomology p B (S + m)
        (Modules.coefficientKPower m p B S (Modules.coefficientClass p B S z z.property)) =
      coefficientBGGHomologyPower m p B S
        (kEquivBGGHomology p B S (Modules.coefficientClass p B S z z.property)) := by
  have h₁ := congrArg (kEquivBGGHomology p B (S + m))
    (Modules.coefficientKPower_class m p B S z z.property)
  have h₂ := kEquivBGGHomology_coefficientClass p B (S + m)
    (Modules.coefficientRelPower m z)
    (Modules.coefficientRelPower_mem_cycles m p B S z.property)
  have h₃ := congrArg (coefficientBGGHomologyPower m p B S)
    (kEquivBGGHomology_coefficientClass p B S z z.property)
  have h₄ := coefficientBGGHomologyPower_mk m p B S
    (comparisonProjectionCycles p B S z)
  have h₅ : comparisonProjectionCycles p B (S + m)
      ⟨Modules.coefficientRelPower m z,
        Modules.coefficientRelPower_mem_cycles m p B S z.property⟩ =
      coefficientBGGCyclesPower m p B S (comparisonProjectionCycles p B S z) :=
    Subtype.ext (relContraction_proj_coefficientRelPower m z)
  have h₆ := congrArg (fun w : (bggWindow p B (S + m)).cycles =>
    (Submodule.Quotient.mk w : BGGHomology p B (S + m))) h₅
  exact h₁.trans (h₂.trans (h₆.trans (h₄.symm.trans h₃.symm)))

/-- The prescribed BGG comparison intertwines the actual coefficient powers. -/
theorem kEquivBGGHomology_coefficientKPower (m p B : ℕ) (S : ℤ) (x : K p B S) :
    kEquivBGGHomology p B (S + m) (Modules.coefficientKPower m p B S x) =
      coefficientBGGHomologyPower m p B S (kEquivBGGHomology p B S x) := by
  exact ((Modules.coefficientClass_surjective p B S).forall
    (p := fun y : K p B S =>
      kEquivBGGHomology p B (S + m) (Modules.coefficientKPower m p B S y) =
        coefficientBGGHomologyPower m p B S (kEquivBGGHomology p B S y))).mpr
      (kEquivBGGHomology_coefficientClassPower m p B S) x

/-- The inverse comparison is natural for the same coefficient shifts. -/
theorem kEquivBGGHomology_symm_coefficientBGGHomologyPower (m p B : ℕ) (S : ℤ)
    (x : BGGHomology p B S) :
    (kEquivBGGHomology p B (S + m)).symm (coefficientBGGHomologyPower m p B S x) =
      Modules.coefficientKPower m p B S ((kEquivBGGHomology p B S).symm x) := by
  apply (kEquivBGGHomology p B (S + m)).injective
  exact ((kEquivBGGHomology p B (S + m)).apply_symm_apply _).trans
    ((congrArg (coefficientBGGHomologyPower m p B S)
      ((kEquivBGGHomology p B S).apply_symm_apply x)).symm.trans
        (kEquivBGGHomology_coefficientKPower m p B S _).symm)

end KhanSL2.BGGBridge
