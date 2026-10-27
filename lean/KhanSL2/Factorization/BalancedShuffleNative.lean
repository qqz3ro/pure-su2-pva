module

public import KhanSL2.Factorization.CoefficientChainNative
public import KhanSL2.Factorization.BalancedShuffleComplex
public import KhanSL2.Factorization.BalancedTensorRestriction

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory HomologicalComplex
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily

variable (M N : Type) [AddCommGroup M] [Module ℂ M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent ℂ M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [CoefficientLinearCurrent ℂ N]

/-- Over the ground field the tensor of coefficient-linear complexes identifies
with the tensor of the original native complexes. -/
def balancedNativeTensorIso : balancedTensorComplex ℂ M N ≅ tensorComplex M N :=
  MonoidalCategory.tensorIso (coefficientNativeComplexIso M) (coefficientNativeComplexIso N)

/-- The inverse comparison has exactly the original ground-field balancing formula. -/
theorem balancedNativeTensorIso_inv_forget (j:ℕ) (z:(tensorComplex M N).X j) :
    balancedTensorDegreeForget ℂ M N j ((balancedNativeTensorIso M N).inv.f j z) =
      relativeTensorBalance ℂ M N (tensorDegreeForget M N j z) := by
  let P := (balancedTensorDegreeForgetRestricted ℂ M N j).comp
    (ModuleCat.restrictScalarsId'App (algebraMap ℂ ℂ) rfl
      ((balancedTensorComplex ℂ M N).X j)).inv.hom
  have he : ModuleCat.ofHom (P.comp
      ((balancedNativeTensorIso M N).inv.f j).hom) =
      ModuleCat.ofHom ((relativeTensorBalanceNative ℂ M N).comp (tensorDegreeForget M N j)) := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro u v
    have hι := congrArg (fun f => f.hom (u⊗ₜ[ℂ]v))
      (HomologicalComplex.ι_tensorHom
        (coefficientNativeComplexIso M).inv (coefficientNativeComplexIso N).inv p q j h)
    change (HomologicalComplex.tensorHom (coefficientNativeComplexIso M).inv
      (coefficientNativeComplexIso N).inv).f j
        (ιTensorObj (complex M) (complex N) p q j h (u⊗ₜ[ℂ]v)) =
      ιTensorObj (coefficientRelativeComplex ℂ M) (coefficientRelativeComplex ℂ N) p q j h
        ((coefficientNativeComplexIso M).inv.f p u ⊗ₜ[ℂ]
          (coefficientNativeComplexIso N).inv.f q v) at hι
    change P ((HomologicalComplex.tensorHom (coefficientNativeComplexIso M).inv
      (coefficientNativeComplexIso N).inv).f j
        (ιTensorObj (complex M) (complex N) p q j h (u⊗ₜ[ℂ]v))) = _
    rw [hι]
    change balancedTensorDegreeForget ℂ M N j
      (balancedTensorDegreeInclusion ℂ M N p q j h _) = _
    rw [balancedTensorDegreeForget_inclusion]
    change relativeTensorBalance ℂ M N (u.val⊗ₜ[ℂ]v.val) =
      relativeTensorBalance ℂ M N (tensorDegreeForget M N j
        (tensorDegreeInclusion M N p q j h (u⊗ₜ[ℂ]v)))
    rw [tensorDegreeForget_inclusion,TensorProduct.map_tmul]
    rfl
  exact congrArg (fun f=>f.hom z) he

/-- The balanced shuffle over ℂ is the previously specified native shuffle,
through its literal coefficient and degree identifications. -/
theorem balancedShuffleComplex_native :
    complexMap (balancedCoefficientLieHom ℂ M N) ≫
      (coefficientNativeComplexIso (BalancedCoefficients ℂ M N)).inv ≫
        balancedShuffleComplex ℂ M N =
          shuffleComplex M N ≫ (balancedNativeTensorIso M N).inv := by
  ext j : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change degree (M⊗[ℂ]N) j at z
  apply balancedTensorDegreeForget_injective ℂ M N j
  change balancedTensorDegreeForget ℂ M N j
    (balancedDegreeShuffle ℂ M N j
      (coefficientDegreeMap (balancedCoefficientLieHom ℂ M N).toLinearMap
        (constantEquivariant_of_lieHom (balancedCoefficientLieHom ℂ M N)) j z)) =
    balancedTensorDegreeForget ℂ M N j
      ((balancedNativeTensorIso M N).inv.f j (degreeShuffle M N j z))
  rw [balancedTensorDegreeForget_degreeShuffle,balancedNativeTensorIso_inv_forget,
    tensorDegreeForget_degreeShuffle]
  exact balancedRelativeShuffle_balance ℂ M N z.val

/-- The original coefficient balancing over ℂ induces the specified chain isomorphism. -/
def nativeBalancedCoefficientComplexIso :
    complex (M⊗[ℂ]N) ≅ complex (BalancedCoefficients ℂ M N) where
  hom := complexMap (balancedCoefficientLieHom ℂ M N)
  inv := complexMap (balancedComplexEquiv M N).toLieModuleHom
  hom_inv_id := by
    apply complexMap_retraction
    ext m n
    rfl
  inv_hom_id := by
    apply complexMap_retraction
    apply TensorProduct.ext'
    intro m n
    rfl

/-- The native and balanced ground-field comparisons have the same quasi-isomorphism property. -/
theorem balancedShuffleComplex_quasiIso_of_native [QuasiIso (shuffleComplex M N)] :
    QuasiIso (balancedShuffleComplex ℂ M N) := by
  let e := nativeBalancedCoefficientComplexIso M N ≪≫
    (coefficientNativeComplexIso (BalancedCoefficients ℂ M N)).symm
  have h : QuasiIso (e.hom ≫ balancedShuffleComplex ℂ M N) := by
    change QuasiIso ((complexMap (balancedCoefficientLieHom ℂ M N) ≫
      (coefficientNativeComplexIso (BalancedCoefficients ℂ M N)).inv) ≫
        balancedShuffleComplex ℂ M N)
    rw [Category.assoc,balancedShuffleComplex_native]
    infer_instance
  let := h
  exact quasiIso_of_comp_left e.hom (balancedShuffleComplex ℂ M N)

end KhanSL2.Factorization







