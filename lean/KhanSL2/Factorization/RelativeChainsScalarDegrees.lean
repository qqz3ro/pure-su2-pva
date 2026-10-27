module

public import KhanSL2.Factorization.RelativeChainsScalarEquivalence
public import KhanSL2.Factorization.RelativeChainsGrading

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M] [LieRingModule Current M] [LieModule ℂ Current M]
  [CoefficientLinearCurrent R M]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

/-- The existing exterior-degree projection also preserves coefficient scalars. -/
theorem degreeProjection_coefficient_smul (j : ℕ) (r : R) (z : RelativeChains M) :
    degreeProjection M j (r • z) = r • degreeProjection M j z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change (relC M).mkQ (rawDegreeProjection M j
      (rawMap (coefficientScalarLieHom R M r).toLinearMap z)) =
        (relC M).mkQ (rawMap (coefficientScalarLieHom R M r).toLinearMap
          (rawDegreeProjection M j z))
    congr 1
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add,hz,hw]
    | tmul ω m => rfl

def coefficientDegreeProjectionLinear (j : ℕ) : Module.End R (RelativeChains M) where
  __ := (degreeProjection M j).toAddMonoidHom
  map_smul' := degreeProjection_coefficient_smul R M j

def coefficientDegreeInclusionLinear (j : ℕ) : degree M j →ₗ[R] RelativeChains M where
  toFun z := z.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficientDegreeComponentLinear (j : ℕ) : RelativeChains M →ₗ[R] degree M j where
  toFun z := degreeComponent M j z
  map_add' z w := (degreeComponent M j).map_add z w
  map_smul' r z := Subtype.ext (degreeProjection_coefficient_smul R M j r z)

theorem coefficientDegreeComponent_inclusion (j : ℕ) :
    (coefficientDegreeComponentLinear R M j).comp (coefficientDegreeInclusionLinear R M j) =
      LinearMap.id := by
  apply LinearMap.ext
  exact degreeComponent_subtype M j

/-- Exterior degree is an actual coefficient submodule, with the unchanged carrier. -/
def coefficientDegreeSubmodule (j : ℕ) : Submodule R (RelativeChains M) where
  carrier := degree M j
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' r _z hz := coefficientMap_mem_degree (coefficientScalarLieHom R M r).toLinearMap
    (constantEquivariant_of_lieHom (coefficientScalarLieHom R M r)) hz

variable (A : Type) [CommRing A] [Algebra R A] [Algebra ℂ A] [IsScalarTower ℂ R A]

theorem relativeChainsScalarMap_degreeProjection (j : ℕ) (z : A ⊗[R] RelativeChains M) :
    degreeProjection (CoefficientBaseChange R M A) j (relativeChainsScalarMap R M A z) =
      relativeChainsScalarMap R M A ((coefficientDegreeProjectionLinear R M j).baseChange A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul a z =>
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [Submodule.Quotient.mk_add,map_add,TensorProduct.tmul_add,hz,hw]
      | tmul ω m =>
        change degreeProjection (CoefficientBaseChange R M A) j
          (relativeChainsScalarMap R M A (a ⊗ₜ[R] (relC M).mkQ (ω ⊗ₜ[ℂ] m))) =
          relativeChainsScalarMap R M A
            (a ⊗ₜ[R] (relC M).mkQ (exteriorDegreeProjection j ω ⊗ₜ[ℂ] m))
        rw [relativeChainsScalarMap_tmul_mk,relativeChainsScalarMap_tmul_mk]
        rfl

/-- Scalar extension preserves the actual exterior-degree subspace. -/
theorem relativeChainsScalarMap_mem_degree (j : ℕ) (z : A ⊗[R] degree M j) :
    relativeChainsScalarMap R M A ((coefficientDegreeInclusionLinear R M j).baseChange A z) ∈
      degree (CoefficientBaseChange R M A) j := by
  change _ ∈ coefficientDegreeSubmodule A (CoefficientBaseChange R M A) j
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using Submodule.add_mem _ hz hw
  | tmul a z =>
    change a • coefficientMap (coefficientBaseChangeUnit R M A).toLinearMap
      (constantEquivariant_of_lieHom (coefficientBaseChangeUnit R M A)) z.val ∈ _
    apply Submodule.smul_mem
    exact coefficientMap_mem_degree _ _ z.property

def relativeChainsScalarDegreeMap (j : ℕ) :
    A ⊗[R] degree M j →ₗ[A] degree (CoefficientBaseChange R M A) j where
  toFun z := ⟨relativeChainsScalarMap R M A
    ((coefficientDegreeInclusionLinear R M j).baseChange A z),
      relativeChainsScalarMap_mem_degree R M A j z⟩
  map_add' z w := Subtype.ext (by simp only [map_add,Submodule.coe_add])
  map_smul' a z := Subtype.ext (by simp only [map_smul]; rfl)

def relativeChainsScalarDegreeInverse (j : ℕ) :
    degree (CoefficientBaseChange R M A) j →ₗ[A] A ⊗[R] degree M j :=
  ((coefficientDegreeComponentLinear R M j).baseChange A).comp
    ((relativeChainsScalarEquiv R M A).symm.toLinearMap.comp
      (coefficientDegreeInclusionLinear A (CoefficientBaseChange R M A) j))

theorem relativeChainsScalarDegreeInverse_map (j : ℕ) (z : A ⊗[R] degree M j) :
    relativeChainsScalarDegreeInverse R M A j (relativeChainsScalarDegreeMap R M A j z) = z := by
  change (coefficientDegreeComponentLinear R M j).baseChange A
    ((relativeChainsScalarEquiv R M A).symm (relativeChainsScalarEquiv R M A
      ((coefficientDegreeInclusionLinear R M j).baseChange A z))) = z
  rw [LinearEquiv.symm_apply_apply]
  have h := congrArg (fun f => f.baseChange A) (coefficientDegreeComponent_inclusion R M j)
  rw [LinearMap.baseChange_comp,LinearMap.baseChange_id] at h
  exact LinearMap.congr_fun h z

theorem relativeChainsScalarDegreeMap_inverse (j : ℕ)
    (z : degree (CoefficientBaseChange R M A) j) :
    relativeChainsScalarDegreeMap R M A j (relativeChainsScalarDegreeInverse R M A j z) = z := by
  apply Subtype.ext
  change relativeChainsScalarMap R M A
    ((coefficientDegreeInclusionLinear R M j).baseChange A
      ((coefficientDegreeComponentLinear R M j).baseChange A
        ((relativeChainsScalarEquiv R M A).symm z.val))) = z.val
  have h : (coefficientDegreeInclusionLinear R M j).comp
      (coefficientDegreeComponentLinear R M j) = coefficientDegreeProjectionLinear R M j := rfl
  have hA := congrArg (fun f => f.baseChange A) h
  rw [LinearMap.baseChange_comp] at hA
  have he := LinearMap.congr_fun hA ((relativeChainsScalarEquiv R M A).symm z.val)
  change (coefficientDegreeInclusionLinear R M j).baseChange A
      ((coefficientDegreeComponentLinear R M j).baseChange A
        ((relativeChainsScalarEquiv R M A).symm z.val)) = _ at he
  rw [he,← relativeChainsScalarMap_degreeProjection]
  change degreeProjection (CoefficientBaseChange R M A) j
    (relativeChainsScalarEquiv R M A ((relativeChainsScalarEquiv R M A).symm z.val)) = z.val
  rw [LinearEquiv.apply_symm_apply]
  exact degreeProjection_of_mem _ z.property

/-- The actual degree-j relative chain group commutes with every scalar extension. -/
def relativeChainsScalarDegreeEquiv (j : ℕ) :
    A ⊗[R] degree M j ≃ₗ[A] degree (CoefficientBaseChange R M A) j where
  __ := relativeChainsScalarDegreeMap R M A j
  invFun := relativeChainsScalarDegreeInverse R M A j
  left_inv := relativeChainsScalarDegreeInverse_map R M A j
  right_inv := relativeChainsScalarDegreeMap_inverse R M A j

end KhanSL2.Factorization

