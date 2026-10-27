module

public import KhanSL2.Factorization.KunnethTotal

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The canonical total Künneth equivalence respects actual coefficient maps.
In particular it retains all fixed-degree projections and coefficient power sums. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG

variable {M N M' N' : Type}
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M'] [Module ℂ M'] [LieRingModule Current M'] [LieModule ℂ Current M']
  [AddCommGroup N'] [Module ℂ N'] [LieRingModule Current N'] [LieModule ℂ Current N']

/-- The original coefficient map on the total actual relative homology. -/
def coefficientTotalHomologyMap (f : M →ₗ⁅ℂ,Current⁆ M') :
    TotalHomology M →ₗ[ℂ] TotalHomology M' :=
  (totalPairMap (coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f))
    (LinearMap.ext (coefficientMap_differential f))).homologyMap
      (differential_comp_self M) (differential_comp_self M')

/-- Tensoring cycle classes is natural for the specified coefficient homomorphisms. -/
theorem totalHomologyCross_natural (f : M →ₗ⁅ℂ,Current⁆ M')
    (g : N →ₗ⁅ℂ,Current⁆ N')
    (z : TotalHomology M ⊗[ℂ] TotalHomology N) :
    tensorCoefficientTotalHomologyMap f g (totalHomologyCross M N z) =
      totalHomologyCross M' N'
        (TensorProduct.map (coefficientTotalHomologyMap f) (coefficientTotalHomologyMap g) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul u v =>
    obtain ⟨u,rfl⟩ := Submodule.mkQ_surjective
      (PerfectDuality.pairBoundaries (differential M) (differential M)) u
    obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective
      (PerfectDuality.pairBoundaries (differential N) (differential N)) v
    simp only [Submodule.mkQ_apply]
    rw [totalHomologyCross_mk_tmul_mk,TensorProduct.map_tmul]
    change Submodule.Quotient.mk _ = totalHomologyCross M' N'
      (Submodule.Quotient.mk _ ⊗ₜ[ℂ] Submodule.Quotient.mk _)
    rw [totalHomologyCross_mk_tmul_mk]
    congr 1

/-- The actual Künneth isomorphism retains coefficient naturality. -/
theorem totalKunnethEquiv_natural (f : M →ₗ⁅ℂ,Current⁆ M')
    (g : N →ₗ⁅ℂ,Current⁆ N')
    (z : TotalHomology M ⊗[ℂ] TotalHomology N) :
    tensorCoefficientTotalHomologyMap f g (totalKunnethEquiv M N z) =
      totalKunnethEquiv M' N'
        (TensorProduct.map (coefficientTotalHomologyMap f) (coefficientTotalHomologyMap g) z) := by
  change tensorCoefficientTotalHomologyMap f g ((totalKunnethEquiv M N).toLinearMap z) =
    (totalKunnethEquiv M' N').toLinearMap _
  rw [totalKunnethEquiv_eq_cross,totalKunnethEquiv_eq_cross,totalHomologyCross_natural]

/-- The inverse Künneth map reads a pure tensor cycle as the tensor of its classes. -/
@[simp] theorem totalKunnethEquiv_symm_tensorCycles
    (u : LinearMap.ker (differential M)) (v : LinearMap.ker (differential N)) :
    (totalKunnethEquiv M N).symm (Submodule.Quotient.mk (tensorCycles M N u v)) =
      Submodule.Quotient.mk u ⊗ₜ[ℂ] Submodule.Quotient.mk v := by
  apply (totalKunnethEquiv M N).injective
  rw [LinearEquiv.apply_symm_apply,totalKunnethEquiv_mk_tmul_mk]

/-- The inverse canonical equivalence also retains the original coefficient maps. -/
theorem totalKunnethEquiv_symm_natural (f : M →ₗ⁅ℂ,Current⁆ M')
    (g : N →ₗ⁅ℂ,Current⁆ N') (z : TensorTotalHomology M N) :
    (totalKunnethEquiv M' N').symm (tensorCoefficientTotalHomologyMap f g z) =
      TensorProduct.map (coefficientTotalHomologyMap f) (coefficientTotalHomologyMap g)
        ((totalKunnethEquiv M N).symm z) := by
  apply (totalKunnethEquiv M' N').injective
  rw [LinearEquiv.apply_symm_apply,← totalKunnethEquiv_natural,LinearEquiv.apply_symm_apply]

end KhanSL2.Factorization
