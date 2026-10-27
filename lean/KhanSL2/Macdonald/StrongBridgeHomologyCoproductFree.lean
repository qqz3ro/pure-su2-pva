module

public import KhanSL2.Macdonald.StrongBridgeHomologyCoproductTensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual primitive coproduct restricts to the colour-zero free algebra.
The retraction is the explicit colour projection, independent of homology. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

/-- Include the actual colour-zero generators in the mixed coordinate algebra. -/
def strongFreeEmbedding : strongFree →ₗ[ℂ] W := strongModel.toLinearMap.comp strongFree.subtype

/-- Kill forbidden colours and retain the resulting actual free element. -/
def strongFreeRetraction : W →ₗ[ℂ] strongFree :=
  (StrongMacdonald.projFull.toLinearMap.comp strongModel.symm.toLinearMap).codRestrict _ (by
    intro u
    exact strongProjFull_idempotent (strongModel.symm u))

@[simp] theorem strongFreeEmbedding_apply (u : strongFree) :
    strongFreeEmbedding u = strongModel u.val := rfl

@[simp] theorem strongFreeRetraction_embedding (u : strongFree) :
    strongFreeRetraction (strongFreeEmbedding u) = u := by
  apply Subtype.ext
  change StrongMacdonald.projFull (strongModel.symm (strongModel u.val)) = u.val
  rw [strongModel.symm_apply_apply]
  exact u.property

@[simp] theorem strongFreeEmbedding_retraction (u : W) :
    strongFreeEmbedding (strongFreeRetraction u) = strongColorProjection u := rfl

theorem strongColorProjection_embedding (u : strongFree) :
    strongColorProjection (strongFreeEmbedding u) = strongFreeEmbedding u := by
  rw [← strongFreeEmbedding_retraction,strongFreeRetraction_embedding]

/-- The tensor inclusion has the actual tensor colour retraction. -/
theorem strongFreeTensorRetraction_embedding (u : strongFree ⊗[ℂ] strongFree) :
    TensorProduct.map strongFreeRetraction strongFreeRetraction
      (TensorProduct.map strongFreeEmbedding strongFreeEmbedding u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul u v => simp only [TensorProduct.map_tmul,strongFreeRetraction_embedding]

theorem strongFreeTensorEmbedding_retraction (u : W ⊗[ℂ] W) :
    TensorProduct.map strongFreeEmbedding strongFreeEmbedding
      (TensorProduct.map strongFreeRetraction strongFreeRetraction u) =
      TensorProduct.map strongColorProjection.toLinearMap strongColorProjection.toLinearMap u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul u v => simp only [TensorProduct.map_tmul,strongFreeEmbedding_retraction,AlgHom.toLinearMap_apply]

theorem strongFreeTensorEmbedding_injective :
    Function.Injective (TensorProduct.map strongFreeEmbedding strongFreeEmbedding) :=
  Function.LeftInverse.injective strongFreeTensorRetraction_embedding

theorem strongColorProjection_tensorEmbedding (u : strongFree ⊗[ℂ] strongFree) :
    TensorProduct.map strongColorProjection.toLinearMap strongColorProjection.toLinearMap
      (TensorProduct.map strongFreeEmbedding strongFreeEmbedding u) =
      TensorProduct.map strongFreeEmbedding strongFreeEmbedding u := by
  rw [← strongFreeTensorEmbedding_retraction,strongFreeTensorRetraction_embedding]

/-- The specified primitive polynomial/signed exterior coproduct on the free source. -/
def strongFreePrimitiveCoproduct : strongFree →ₗ[ℂ] strongFree ⊗[ℂ] strongFree :=
  (TensorProduct.map strongFreeRetraction strongFreeRetraction).comp
    (mixedCoproduct.comp strongFreeEmbedding)

/-- The actual primitive coproduct lands in the actual free tensor subspace. -/
theorem strongFreePrimitiveCoproduct_embedding (u : strongFree) :
    TensorProduct.map strongFreeEmbedding strongFreeEmbedding (strongFreePrimitiveCoproduct u) =
      mixedCoproduct (strongFreeEmbedding u) := by
  change TensorProduct.map strongFreeEmbedding strongFreeEmbedding
    (TensorProduct.map strongFreeRetraction strongFreeRetraction
      (mixedCoproduct (strongFreeEmbedding u))) = _
  rw [strongFreeTensorEmbedding_retraction,← mixedCoproduct_colorProjection,
    strongColorProjection_embedding]

/-- The finite tensor pairing remains nondegenerate on the true free subspace. -/
theorem strongFree_tensor_pairing_ext {z t : strongFree ⊗[ℂ] strongFree}
    (h : ∀ u v : strongFree,
      tensorSquarePairing (strongFreeEmbedding u ⊗ₜ[ℂ] strongFreeEmbedding v)
        (TensorProduct.map strongFreeEmbedding strongFreeEmbedding z) =
      tensorSquarePairing (strongFreeEmbedding u ⊗ₜ[ℂ] strongFreeEmbedding v)
        (TensorProduct.map strongFreeEmbedding strongFreeEmbedding t)) : z = t := by
  apply strongFreeTensorEmbedding_injective
  apply tensorSquarePairing_ext
  intro a b
  have hh := h (strongFreeRetraction a) (strongFreeRetraction b)
  rw [strongFreeEmbedding_retraction,strongFreeEmbedding_retraction,
    tensorSquarePairing_projection,tensorSquarePairing_projection,
    strongColorProjection_tensorEmbedding,strongColorProjection_tensorEmbedding] at hh
  exact hh

end KhanSL2.Macdonald
