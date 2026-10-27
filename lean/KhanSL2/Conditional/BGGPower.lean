module

public import KhanSL2.Conditional.BGGComplex
public import KhanSL2.BGGBridge.CoefficientWindows

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # The actual coefficient shifts on the assembled BGG complex -/

noncomputable section
open scoped DirectSum

namespace KhanSL2.Conditional.BGGComplex
open BGGBridge

local instance powerTermAddCommGroup (B p : ℕ) : AddCommGroup (Term B p) := inferInstance
local instance powerTermComplexModule (B p : ℕ) : Module ℂ (Term B p) := inferInstance

/-- A coefficient power sum acts on every spin component by the actual coefficient shift. -/
def coefficientPower (m B p : ℕ) : Module.End ℂ (Term B p) :=
  DirectSum.toModule ℂ ℤ (Term B p) fun S =>
    (DirectSum.lof ℂ ℤ (fun T => ↥(bggTerm p B T)) (S + m)).comp
      (componentCoefficientPower m B p S)

@[simp] theorem coefficientPower_lof (m B p : ℕ) (S : ℤ) (x : bggTerm p B S) :
    coefficientPower m B p (DirectSum.lof ℂ ℤ (fun T => ↥(bggTerm p B T)) S x) =
      DirectSum.lof ℂ ℤ (fun T => ↥(bggTerm p B T)) (S + m)
        (componentCoefficientPower m B p S x) :=
  by simp only [coefficientPower, DirectSum.toModule_lof, LinearMap.comp_apply]

/-- Equality of homogeneous terms respects both the spin index and the quotient representative. -/
theorem term_lof_congr (B p : ℕ) {S T : ℤ} (hST : S = T)
    (x : bggTerm p B S) (y : bggTerm p B T)
    (hxy : (x : HarmN Current.NB ⧸ relH Current.NB) = y) :
    DirectSum.lof ℂ ℤ (fun U => ↥(bggTerm p B U)) S x =
      DirectSum.lof ℂ ℤ (fun U => ↥(bggTerm p B U)) T y := by
  subst T
  exact congrArg (DirectSum.lof ℂ ℤ (fun U => ↥(bggTerm p B U)) S) (Subtype.ext hxy)

/-- The specified BGG differential commutes with each coefficient shift. -/
theorem coefficientPower_differential (m B p : ℕ) (x : Term B (p + 1)) :
    coefficientPower m B p (differential B p x) =
      differential B p (coefficientPower m B (p + 1) x) := by
  have h : (coefficientPower m B p).comp (differential B p) =
      (differential B p).comp (coefficientPower m B (p + 1)) := by
    apply DirectSum.linearMap_ext
    intro S
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, differential_lof, coefficientPower_lof]
    apply congrArg (DirectSum.lof ℂ ℤ (fun T => ↥(bggTerm p B T)) (S + m))
    apply Subtype.ext
    exact (coefficientBGGPower_dHq m z).symm
  exact LinearMap.congr_fun h x

/-- All coefficient shifts commute on the actual direct sum, including the shifted indices. -/
theorem coefficientPower_commute (m n B p : ℕ) :
    Commute (coefficientPower m B p) (coefficientPower n B p) := by
  apply DirectSum.linearMap_ext
  intro S
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, Module.End.mul_apply, coefficientPower_lof]
  apply term_lof_congr B p (by omega)
  exact LinearMap.congr_fun (coefficientBGGPower_commute m n).eq z

end KhanSL2.Conditional.BGGComplex



