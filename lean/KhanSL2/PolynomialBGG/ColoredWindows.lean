module

public import KhanSL2.PolynomialBGG.ColoredClasses
public import KhanSL2.BGGBridge.TopGeneratorWindow

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace KhanSL2.PolynomialBGG

open MvPolynomial BGG Current BGGBridge Conditional
open scoped TensorProduct KhanSL2.Conditional

/-- Every colored word with B factors has coefficient number B. -/
theorem coloredWord_degree (B : ℕ) (c : Fin B → Fin 3) (a : Fin B → ℕ) :
    LieChains.derivExt (1 : Module.End ℂ Cur) (coloredWord B c a) =
      (B : ℂ) • coloredWord B c a := by
  rw [coloredWord, ExteriorAlgebra.ιMulti_apply]
  have h := LieChains.derivExt_list_prod (k := ℂ)
    (fun i : Fin B => currentBasis (a i, c i)) (1 : Module.End ℂ Cur) (fun _ => 1)
    (fun _ => by simp) (List.ofFn fun i : Fin B => i)
  simpa [List.map_ofFn, Function.comp_def] using h

/-- Physical spin does not depend on the colors of the coefficient word. -/
theorem coloredWord_dilation (B : ℕ) (c : Fin B → Fin 3) (a : Fin B → ℕ) :
    dilN (coloredWord B c a) =
      (2 : ℂ) ^ (∑ i : Fin B, (a i + 1)) • coloredWord B c a := by
  change ExteriorAlgebra.map scaleCur _ = _
  rw [coloredWord, ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ B (fun i => scaleCur (currentBasis (a i, c i))) = _
  simp_rw [scaleCur_currentBasis]
  rw [AlternatingMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]

/-- A colored standard tensor lies in its prescribed actual spin window. -/
theorem standardColoredWord_mem_harmWin (p B : ℕ) (v : TauCeti.Sl2Std ℂ (2*p))
    (c : Fin B → Fin 3) (a : Fin B → ℕ) :
    standardTensorMap p v (coloredWord B c a) ∈
      harmWin p B ((generatorEnergy p + ∑ i : Fin B, (a i + 1) : ℕ) : ℤ) := by
  rw [standardTensorMap_apply]
  refine ⟨⟨tmul_mem_tensorLeft ?_ _, Module.End.mem_eigenspace_iff.mpr ?_⟩,
    Module.End.mem_eigenspace_iff.mpr ?_⟩
  · exact ((PositiveCE.harmonicDegreeStandardEquiv p).symm v).property
  · rw [numBH, LinearMap.lTensor_tmul, coloredWord_degree, TensorProduct.tmul_smul]
  · rw [dilH, TensorProduct.map_tmul, standardHarmonicEmbedding_energyScale,
      coloredWord_dilation, TensorProduct.smul_tmul_smul,
      zpow_natCast, zpow_natCast, pow_add]

/-- The colored coefficient classes come from the actual direct sum of BGG windows. -/
theorem coloredWordClass_mem_termRange (B p : ℕ) (v : TauCeti.Sl2Std ℂ (2*p))
    (c : Fin B → Fin 3) (a : Fin B → ℕ) :
    coefficientClass p v (coloredWord B c a) ∈
      (BGGComplex.termToCoinvariantsLinear B p).range := by
  let S : ℤ := ((generatorEnergy p + ∑ i : Fin B, (a i + 1) : ℕ) : ℤ)
  let z : bggTerm p B S := ⟨coefficientClass p v (coloredWord B c a),
    ⟨_, standardColoredWord_mem_harmWin p B v c a, rfl⟩⟩
  refine ⟨DirectSum.lof ℂ ℤ (fun T => ↥(bggTerm p B T)) S z, ?_⟩
  exact BGGComplex.termToCoinvariants_lof B p S z

/-- Every degree-B coefficient tensor with a standard harmonic vector comes
from the actual BGG term. -/
theorem coefficientClass_mem_termRange (B p : ℕ) (v : TauCeti.Sl2Std ℂ (2*p))
    (ν : NB) (hν : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν) :
    coefficientClass p v ν ∈ (BGGComplex.termToCoinvariantsLinear B p).range := by
  apply coefficient_degree_le_of_coloredWord B
    ((((BGGComplex.termToCoinvariantsLinear B p).range).restrictScalars ℂ).comap
      (coefficientClass p v)) _ ν hν
  intro c a
  exact coloredWordClass_mem_termRange B p v c a

/-- The full colored polynomial map has values in the actual BGG term. -/
theorem coloredClassMap_mem_termRange (B p : ℕ) (v : TauCeti.Sl2Std ℂ (2*p))
    (c : Fin B → Fin 3) (q : MvPolynomial (Fin B) ℂ) :
    coloredClassMap B p v c q ∈ (BGGComplex.termToCoinvariantsLinear B p).range := by
  let W := ((BGGComplex.termToCoinvariantsLinear B p).range).restrictScalars ℂ
  change coloredClassMap B p v c q ∈ W
  induction q using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [coloredClassMap_apply, coloredPolynomialMap_monomial, map_smul]
    exact W.smul_mem a (coloredWordClass_mem_termRange B p v c d)
  | add q r hq hr =>
    rw [map_add]
    exact W.add_mem hq hr

end KhanSL2.PolynomialBGG
