module

public import KhanSL2.PolynomialBGG.ProjectiveModel
public import KhanSL2.BGGBridge.TopAlternantsMap

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The normalized alternating section commutes with the derivation induced
by every linear endomorphism. In particular this applies both to coefficient
mode shifts and to the constant Lie algebra action. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.PolynomialBGG

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Act on each labelled tensor slot, and sum. -/
def tensorDeriv (n : ℕ) (D : Module.End ℂ M) : Module.End ℂ (⨂[ℂ]^n M) :=
  ∑ i : Fin n, PiTensorProduct.map (Function.update (fun _ => LinearMap.id) i D)

@[simp] theorem tensorDeriv_tprod (n : ℕ) (D : Module.End ℂ M) (v : Fin n → M) :
    tensorDeriv n D (PiTensorProduct.tprod ℂ v) =
      ∑ i : Fin n, PiTensorProduct.tprod ℂ (Function.update v i (D (v i))) := by
  simp only [tensorDeriv, LinearMap.sum_apply, PiTensorProduct.map_tprod]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h]

/-- Restrict the actual exterior derivation to one exterior degree. -/
def exteriorDeriv (n : ℕ) (D : Module.End ℂ M) : Module.End ℂ (⋀[ℂ]^n M) :=
  (LieChains.derivExt D).restrict (fun _ h => LieChains.derivExt_mem_exteriorPower D h)

@[simp] theorem exteriorDeriv_ιMulti (n : ℕ) (D : Module.End ℂ M) (v : Fin n → M) :
    exteriorDeriv n D (exteriorPower.ιMulti ℂ n v) =
      ∑ i : Fin n, exteriorPower.ιMulti ℂ n (Function.update v i (D (v i))) := by
  apply Subtype.ext
  change LieChains.derivExt D (ExteriorAlgebra.ιMulti ℂ n v) = _
  rw [BGGBridge.TopAlternants.derivExt_ιMulti]
  simp

/-- Antisymmetrization intertwines all induced derivations. -/
theorem toTensorPower_exteriorDeriv (n : ℕ) (D : Module.End ℂ M) :
    (exteriorPower.toTensorPower ℂ M n).comp (exteriorDeriv n D) =
      (tensorDeriv n D).comp (exteriorPower.toTensorPower ℂ M n) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorDeriv_ιMulti, map_sum, exteriorPower.toTensorPower_apply_ιMulti,
    map_smul, tensorDeriv_tprod]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Units.smul_def, map_zsmul, tensorDeriv_tprod]
  simp only [← Int.cast_smul_eq_zsmul ℂ]
  rw [Finset.smul_sum]
  rw [← (Equiv.sum_comp σ)]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  exact Function.update_comp_eq_of_injective v σ.injective i (D (v (σ i)))

/-- The normalized section is natural for coefficient shifts and Lie actions. -/
theorem exteriorToTensor_exteriorDeriv (n : ℕ) (D : Module.End ℂ M) :
    (exteriorToTensor M n).comp (exteriorDeriv n D) =
      (tensorDeriv n D).comp (exteriorToTensor M n) := by
  rw [exteriorToTensor, LinearMap.smul_comp, LinearMap.comp_smul,
    toTensorPower_exteriorDeriv]

/-- The exterior quotient is natural for the same derivations. -/
theorem tensorToExterior_tensorDeriv (n : ℕ) (D : Module.End ℂ M) :
    (tensorToExterior M n).comp (tensorDeriv n D) =
      (exteriorDeriv n D).comp (tensorToExterior M n) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, tensorDeriv_tprod,
    map_sum, tensorToExterior_tprod, exteriorDeriv_ιMulti]

end KhanSL2.PolynomialBGG
