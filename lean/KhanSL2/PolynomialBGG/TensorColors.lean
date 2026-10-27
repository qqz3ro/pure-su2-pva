module

public import KhanSL2.PolynomialBGG.TensorModel

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.PolynomialBGG
open BGG Current

/-- Apply a root-color endomorphism independently in each labelled slot. -/
def colorDeriv (B : ℕ) (D : Module.End ℂ G) : Module.End ℂ (Color B) :=
  (Pi.basisFun ℂ (Fin B → Fin 3)).constr ℂ fun c =>
    ∑ i : Fin B, ∑ j : Fin 3,
      rootBasis.repr (D (rootBasis (c i))) j •
        Pi.basisFun ℂ (Fin B → Fin 3) (Function.update c i j)

@[simp] theorem colorDeriv_basis (B : ℕ) (D : Module.End ℂ G) (c : Fin B → Fin 3) :
    colorDeriv B D (Pi.basisFun ℂ (Fin B → Fin 3) c) =
      ∑ i : Fin B, ∑ j : Fin 3, rootBasis.repr (D (rootBasis (c i))) j •
        Pi.basisFun ℂ (Fin B → Fin 3) (Function.update c i j) :=
  Module.Basis.constr_basis _ _ _ _

/-- A color operator leaves the polynomial mode unchanged. -/
theorem currentColorMap_basis (D : Module.End ℂ G) (n : ℕ) (a : Fin 3) :
    LinearMap.lTensor (Polynomial ℂ) D (currentBasis (n, a)) =
      ∑ j : Fin 3, rootBasis.repr (D (rootBasis a)) j • currentBasis (n, j) := by
  rw [currentBasis_apply, mode_apply, LinearMap.lTensor_tmul]
  conv_lhs => rw [← rootBasis.sum_repr (D (rootBasis a)), TensorProduct.tmul_sum]
  simp only [TensorProduct.tmul_smul, currentBasis_apply, mode_apply]

/-- Expanding a color change in a single slot affects only that color word. -/
theorem tensorColorMap_word (B : ℕ) (D : Module.End ℂ G)
    (a : Fin B → ℕ) (c : Fin B → Fin 3) :
    tensorDeriv B (LinearMap.lTensor (Polynomial ℂ) D)
        (PiTensorProduct.tprod ℂ (fun i => currentBasis (a i, c i))) =
      ∑ i : Fin B, ∑ j : Fin 3, rootBasis.repr (D (rootBasis (c i))) j •
        PiTensorProduct.tprod ℂ (fun k => currentBasis (a k, Function.update c i j k)) := by
  classical
  rw [tensorDeriv_tprod]
  apply Finset.sum_congr rfl
  intro i _
  rw [currentColorMap_basis, (PiTensorProduct.tprod ℂ).map_update_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [(PiTensorProduct.tprod ℂ).map_update_smul]
  congr 1
  congr 1
  funext k
  by_cases h : k = i
  · subst k; simp
  · simp [Function.update_of_ne h]

/-- In the root-polynomial model the color operator acts only in its finite color factor. -/
theorem rootTensorEquiv_colorDeriv (B : ℕ) (D : Module.End ℂ G)
    (x : ⨂[ℂ]^B Cur) :
    rootTensorEquiv B (tensorDeriv B (LinearMap.lTensor (Polynomial ℂ) D) x) =
      LinearMap.lTensor (RootPolynomial B) (colorDeriv B D) (rootTensorEquiv B x) := by
  have he : (rootTensorEquiv B).toLinearMap.comp
      (tensorDeriv B (LinearMap.lTensor (Polynomial ℂ) D)) =
      (LinearMap.lTensor (RootPolynomial B) (colorDeriv B D)).comp
        (rootTensorEquiv B).toLinearMap := by
    apply (tensorCurrentBasis B).ext
    intro q
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorCurrentBasis_apply]
    rw [rootTensorEquiv_tprod, LinearMap.lTensor_tmul, colorDeriv_basis]
    rw [tensorColorMap_word B D (fun i => (q i).1) (fun i => (q i).2)]
    simp only [map_sum, map_smul, rootTensorEquiv_word,
      TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  exact LinearMap.congr_fun he x

/-- Constant current brackets act only in the root-color factor. -/
theorem constantLie_eq_colorMap (x : G) :
    LieModule.toEnd ℂ Cur Cur (constant x) =
      LinearMap.lTensor (Polynomial ℂ) (LieModule.toEnd ℂ G G x) := by
  apply currentBasis.ext
  rintro ⟨n, a⟩
  simp only [LieModule.toEnd_apply_apply]
  rw [currentBasis_apply, constant_apply, mode_lie, zero_add]
  simp only [mode_apply, LinearMap.lTensor_tmul, LieModule.toEnd_apply_apply]

/-- The actual constant sl₂ action has no root-polynomial component. -/
theorem rootTensorEquiv_constantLie (B : ℕ) (x : G) (v : ⨂[ℂ]^B Cur) :
    rootTensorEquiv B (tensorDeriv B (LieModule.toEnd ℂ Cur Cur (constant x)) v) =
      LinearMap.lTensor (RootPolynomial B) (colorDeriv B (LieModule.toEnd ℂ G G x))
        (rootTensorEquiv B v) := by
  rw [constantLie_eq_colorMap]
  exact rootTensorEquiv_colorDeriv B _ v

end KhanSL2.PolynomialBGG
