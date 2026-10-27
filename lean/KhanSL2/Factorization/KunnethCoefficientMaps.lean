module

public import KhanSL2.Factorization.ShuffleTotalQuasiIso
public import KhanSL2.Factorization.ShuffleRelativeNaturality

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Actual coefficient maps on the signed total tensor complex and its homology. -/

noncomputable section
open scoped TensorProduct DirectSum
namespace KhanSL2.Factorization
open BGG

variable {M N M' N' : Type*}
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M'] [Module ℂ M'] [LieRingModule Current M'] [LieModule ℂ Current M']
  [AddCommGroup N'] [Module ℂ N'] [LieRingModule Current N'] [LieModule ℂ Current N']

theorem coefficientMap_parity (f : M →ₗ[ℂ] M') (hf : ConstantEquivariant f)
    (z : RelativeChains M) :
    coefficientMap f hf (relativeParity M z) = relativeParity M' (coefficientMap f hf z) := by
  obtain ⟨u,rfl⟩ := (degreeSumEquiv M).surjective z
  induction u using DirectSum.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | of j u =>
    rw [degreeSumEquiv_of,relativeParity_of_mem_degree M u.property,map_smul,
      relativeParity_of_mem_degree M' (coefficientMap_mem_degree f hf u.property)]

/-- The same tensor of coefficient maps commutes with the signed total boundary. -/
theorem tensorCoefficientMap_differential
    (f : M →ₗ⁅ℂ,Current⁆ M') (g : N →ₗ⁅ℂ,Current⁆ N')
    (z : RelativeChains M ⊗[ℂ] RelativeChains N) :
    TensorProduct.map (coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f))
      (coefficientMap g.toLinearMap (constantEquivariant_of_lieHom g))
        (relativeTensorDifferential M N z) =
      relativeTensorDifferential M' N' (TensorProduct.map
        (coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f))
        (coefficientMap g.toLinearMap (constantEquivariant_of_lieHom g)) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul u v =>
    simp only [relativeTensorDifferential_tmul,map_add,TensorProduct.map_tmul,
      coefficientMap_differential,coefficientMap_parity]

abbrev TensorTotalHomology (M N : Type*)
    [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
    [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N] :=
  PerfectDuality.PairHomology (relativeTensorDifferential M N) (relativeTensorDifferential M N)
    (relativeTensorDifferential_comp_self M N)

def tensorCoefficientTotalHomologyMap
    (f : M →ₗ⁅ℂ,Current⁆ M') (g : N →ₗ⁅ℂ,Current⁆ N') :
    TensorTotalHomology M N →ₗ[ℂ] TensorTotalHomology M' N' :=
  (totalPairMap (TensorProduct.map
    (coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f))
    (coefficientMap g.toLinearMap (constantEquivariant_of_lieHom g)))
      (LinearMap.ext (tensorCoefficientMap_differential f g))).homologyMap
        (relativeTensorDifferential_comp_self M N) (relativeTensorDifferential_comp_self M' N')

end KhanSL2.Factorization
