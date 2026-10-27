module

public import KhanSL2.BGGBridge.TopSpanning
public import KhanSL2.BGG.HarmonicEnergy

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # Explicit spin windows for the top coefficient words -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

/-- A word with B current factors has coefficient number B. -/
theorem topCoefficientWord_degree (B : ℕ) (d : Fin B → ℕ) :
    LieChains.derivExt (1 : Module.End ℂ Cur)
        (ExteriorAlgebra.ιMulti ℂ B (fun i => currentBasis (d i, 0))) =
      (B : ℂ) • ExteriorAlgebra.ιMulti ℂ B (fun i => currentBasis (d i, 0)) := by
  rw [ExteriorAlgebra.ιMulti_apply]
  have h := LieChains.derivExt_list_prod (k := ℂ)
    (fun i : Fin B => currentBasis (d i, 0)) (1 : Module.End ℂ Cur) (fun _ => 1)
    (fun _ => by simp) (List.ofFn fun i : Fin B => i)
  simpa [List.map_ofFn, Function.comp_def] using h

/-- Spin dilation multiplies a root-mode vector by its physical spin power. -/
theorem scaleCur_currentBasis (n : ℕ) (a : Fin 3) :
    scaleCur (currentBasis (n, a)) = (2 : ℂ) ^ (n+1) • currentBasis (n, a) := by
  rw [currentBasis_apply, scaleCur, LinearMap.smul_apply, LieHom.coe_toLinearMap,
    currentScale_mode, smul_smul, pow_succ, mul_comm]

/-- The coefficient word has spin equal to the sum of its mode spins. -/
theorem topCoefficientWord_dilation (B : ℕ) (d : Fin B → ℕ) :
    dilN (ExteriorAlgebra.ιMulti ℂ B (fun i => currentBasis (d i, 0))) =
      (2 : ℂ) ^ (∑ i : Fin B, (d i + 1)) •
        ExteriorAlgebra.ιMulti ℂ B (fun i => currentBasis (d i, 0)) := by
  change ExteriorAlgebra.map scaleCur _ = _
  rw [ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ B (fun i => scaleCur (currentBasis (d i, 0))) = _
  simp_rw [scaleCur_currentBasis]
  rw [AlternatingMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]

/-- Standard harmonic tensors with explicit coefficient words lie in one actual spin window. -/
theorem standardTensorWord_mem_harmWin (p B : ℕ)
    (v : TauCeti.Sl2Std ℂ (2*p)) (d : Fin B → ℕ) :
    standardTensorMap p v (ExteriorAlgebra.ιMulti ℂ B (fun i => currentBasis (d i, 0))) ∈
      harmWin p B ((generatorEnergy p + ∑ i : Fin B, (d i + 1) : ℕ) : ℤ) := by
  rw [standardTensorMap_apply]
  refine ⟨⟨tmul_mem_tensorLeft ?_ _, Module.End.mem_eigenspace_iff.mpr ?_⟩,
    Module.End.mem_eigenspace_iff.mpr ?_⟩
  · exact ((PositiveCE.harmonicDegreeStandardEquiv p).symm v).property
  · rw [numBH, LinearMap.lTensor_tmul, topCoefficientWord_degree, TensorProduct.tmul_smul]
  · rw [dilH, TensorProduct.map_tmul, standardHarmonicEmbedding_energyScale,
      topCoefficientWord_dilation, TensorProduct.smul_tmul_smul,
      zpow_natCast, zpow_natCast, pow_add]

/-- Physical spin of the consecutive-mode top generator. -/
def topGeneratorSpin (B : ℕ) : ℤ :=
  ((generatorEnergy B + ∑ i : Fin B, (i.val + 1) : ℕ) : ℤ)

/-- The specified consecutive-mode tensor defines a class in the actual top BGG window. -/
def topGeneratorWindow (B : ℕ) : bggTerm B B (topGeneratorSpin B) :=
  ⟨Submodule.Quotient.mk (standardTensorMap B
    (TauCeti.Sl2Std.basisVector ℂ (2*B) (2*B))
    (ExteriorAlgebra.ιMulti ℂ B (fun i => currentBasis (i.val, 0)))),
   ⟨_, standardTensorWord_mem_harmWin B B _ (fun i => i.val), rfl⟩⟩

end KhanSL2.BGGBridge

