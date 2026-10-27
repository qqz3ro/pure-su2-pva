module

public import KhanSL2.Macdonald.MixedCoproductPairing
public import KhanSL2.Macdonald.RestrictedCohomology
public import KhanSL2.Factorization.ShuffleSymmetric

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The mixed-coordinate coproduct is the actual symmetric relative CE
comparison, before and after taking constant coinvariants. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open BGGBridge Factorization

/-- The actual primitive coefficient coproduct followed by the actual raw CE shuffle. -/
def rawSymmetricCoproduct : RawChains SymmetricCoefficients →ₗ[ℂ]
    RawChains SymmetricCoefficients ⊗[ℂ] RawChains SymmetricCoefficients :=
  (rawShuffle SymmetricCoefficients SymmetricCoefficients).comp
    (rawMap symmetricCoproduct.toLinearMap)

theorem chainModel_tensor_shuffle_reorder
    (t : ExteriorShuffle.Tensor Current.plus)
    (c : SymmetricCoefficients ⊗[ℂ] SymmetricCoefficients) :
    TensorProduct.map chainModel.toLinearMap chainModel.toLinearMap
      (tensorModelEquiv SymmetricCoefficients SymmetricCoefficients
        (CEShuffle.reorder Current.plus SymmetricCoefficients SymmetricCoefficients (t ⊗ₜ[ℂ] c))) =
      mixedCoproductReorder (c ⊗ₜ[ℂ]
        TensorProduct.map exteriorEquiv.toLinearMap exteriorEquiv.toLinearMap t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu => simp only [TensorProduct.add_tmul, map_add, ht, hu, TensorProduct.tmul_add]
  | tmul u v =>
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [TensorProduct.tmul_add, map_add, hc, hd, TensorProduct.add_tmul]
    | tmul p q => rfl

theorem chainModel_rawShuffle (v : ExteriorAlgebra ℂ Current.plus)
    (c : SymmetricCoefficients ⊗[ℂ] SymmetricCoefficients) :
    TensorProduct.map chainModel.toLinearMap chainModel.toLinearMap
      (rawShuffle SymmetricCoefficients SymmetricCoefficients (CEModel.J (v ⊗ₜ[ℂ] c))) =
      mixedCoproductReorder (c ⊗ₜ[ℂ] exteriorCoproduct (exteriorEquiv v)) := by
  rw [rawShuffle_J, CEShuffle.shuffle_tmul, chainModel_tensor_shuffle_reorder]
  simp only [exteriorCoproduct, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.symm_apply_apply]

/-- The precise chain map has the mixed primitive/signed formula. -/
theorem mixedCoproduct_chainModel (z : RawChains SymmetricCoefficients) :
    mixedCoproduct (chainModel z) =
      TensorProduct.map chainModel.toLinearMap chainModel.toLinearMap (rawSymmetricCoproduct z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul ω p =>
    obtain ⟨v,rfl⟩ := exteriorEquiv.surjective ω
    rw [chainModel_tmul, mixedCoproduct_tmul]
    change mixedCoproductReorder (symmetricCoproductAlg (symmetricCoefficientsEquiv p) ⊗ₜ[ℂ]
      exteriorCoproduct (exteriorEquiv v)) =
      TensorProduct.map chainModel.toLinearMap chainModel.toLinearMap
        (rawShuffle SymmetricCoefficients SymmetricCoefficients
          (CEModel.J (v ⊗ₜ[ℂ] symmetricCoproduct p)))
    rw [chainModel_rawShuffle]
    rfl

/-- Project the actual mixed chain coordinates onto constant coinvariants. -/
def mixedRelativeProjection : W →ₗ[ℂ] RelativeChains SymmetricCoefficients :=
  (relC SymmetricCoefficients).mkQ.comp chainModel.symm.toLinearMap

@[simp] theorem mixedRelativeProjection_chainModel (z : RawChains SymmetricCoefficients) :
    mixedRelativeProjection (chainModel z) = Submodule.Quotient.mk z := by
  simp [mixedRelativeProjection]

theorem symmetricChainCoproduct_mk (z : RawChains SymmetricCoefficients) :
    symmetricChainCoproduct (Submodule.Quotient.mk z) =
      projectRelativeTensor SymmetricCoefficients SymmetricCoefficients (rawSymmetricCoproduct z) := rfl

/-- The coproduct used in the harmonic calculation descends to the actual
specified relative-chain comparison. -/
theorem mixedRelativeProjection_coproduct (u : W) :
    TensorProduct.map mixedRelativeProjection mixedRelativeProjection (mixedCoproduct u) =
      symmetricChainCoproduct (mixedRelativeProjection u) := by
  obtain ⟨z,rfl⟩ := chainModel.surjective u
  rw [mixedCoproduct_chainModel, mixedRelativeProjection_chainModel, symmetricChainCoproduct_mk]
  have ht (t : RawChains SymmetricCoefficients ⊗[ℂ] RawChains SymmetricCoefficients) :
      TensorProduct.map mixedRelativeProjection mixedRelativeProjection
        (TensorProduct.map chainModel.toLinearMap chainModel.toLinearMap t) =
      projectRelativeTensor SymmetricCoefficients SymmetricCoefficients t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t s ht hs => simp only [map_add, ht, hs]
    | tmul z t =>
      simp only [TensorProduct.map_tmul, LinearEquiv.coe_coe,
        mixedRelativeProjection_chainModel]
      rfl
  exact ht _

end KhanSL2.Macdonald
