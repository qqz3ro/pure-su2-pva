module

public import KhanSL2.PolynomialBGG.ColoredWords
public import KhanSL2.Conditional.TopEmbedding
public import KhanSL2.BGGBridge.TopAlternants
public import KhanSL2.BGGBridge.TermVanishing

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace KhanSL2.PolynomialBGG

open MvPolynomial BGG Current BGGBridge Conditional
open scoped TensorProduct KhanSL2.Conditional

/-- Tensor an exterior coefficient with a prescribed harmonic standard vector,
then pass to the actual diagonal constant-action quotient. -/
def coefficientClass (p : ℕ) (v : TauCeti.Sl2Std ℂ (2*p)) :
    NB →ₗ[ℂ] (HarmN NB ⧸ relH NB) :=
  (relH NB).mkQ.comp (standardTensorMap p v)

@[simp] theorem coefficientClass_apply (p : ℕ) (v : TauCeti.Sl2Std ℂ (2*p)) (ν : NB) :
    coefficientClass p v ν = Submodule.Quotient.mk (standardTensorMap p v ν) := rfl

/-- The colored polynomial map into the actual harmonic coinvariants. -/
def coloredClassMap (B p : ℕ) (v : TauCeti.Sl2Std ℂ (2*p)) (c : Fin B → Fin 3) :
    MvPolynomial (Fin B) ℂ →ₗ[ℂ] (HarmN NB ⧸ relH NB) :=
  (coefficientClass p v).comp (coloredPolynomialMap B c)

@[simp] theorem coloredClassMap_apply (B p : ℕ) (v : TauCeti.Sl2Std ℂ (2*p))
    (c : Fin B → Fin 3) (q : MvPolynomial (Fin B) ℂ) :
    coloredClassMap B p v c q = coefficientClass p v (coloredPolynomialMap B c q) := rfl

@[simp] theorem coloredClassMap_product (B p : ℕ) (v : TauCeti.Sl2Std ℂ (2*p))
    (c : Fin B → Fin 3) (a : Fin B → ℕ) :
    coloredClassMap B p v c (∏ i : Fin B, (X i : MvPolynomial (Fin B) ℂ) ^ a i) =
      coefficientClass p v (coloredWord B c a) := by
  rw [coloredClassMap_apply, coloredPolynomialMap_product]

/-- Multiplication by a power sum is the canonical coefficient operator. -/
theorem coloredClassMap_powerSum (m B p : ℕ) (v : TauCeti.Sl2Std ℂ (2*p))
    (c : Fin B → Fin 3) (q : MvPolynomial (Fin B) ℂ) :
    coloredClassMap B p v c (psum (Fin B) ℂ m * q) =
      coefficientBGGPower m (coloredClassMap B p v c q) := by
  simp only [coloredClassMap_apply, coloredPolynomialMap_powerSum,
    coefficientClass_apply, coefficientBGGPower_mk, standardTensorMap_apply,
    coefficientHarmPower_tmul]

/-- Symmetric multiplication intertwines with the fixed elementary-coordinate action. -/
theorem coloredClassMap_symmetric (B p : ℕ) (v : TauCeti.Sl2Std ℂ (2*p))
    (c : Fin B → Fin 3) (r : CoefficientRing B) (q : MvPolynomial (Fin B) ℂ) :
    coloredClassMap B p v c ((Modules.elementaryAlgEquiv B r : MvPolynomial (Fin B) ℂ) * q) =
      r • coloredClassMap B p v c q := by
  have h := TopAlternants.symmetric_intertwines_of_powerSums (coefficientCoordinates B)
    (coloredClassMap B p v c)
    (fun i q => (coloredClassMap_powerSum (i.val + 1) B p v c q).trans
      (globalCoefficientCoordinates_smul B i (coloredClassMap B p v c q)).symm)
    (Modules.elementaryAlgEquiv B r) q
  simpa only [coefficientCoordinates, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply] using h

end KhanSL2.PolynomialBGG
