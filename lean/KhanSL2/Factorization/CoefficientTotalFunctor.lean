module

public import KhanSL2.Factorization.KunnethTotalNaturality

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual total relative-homology coefficient functor preserves the
original linear operations and composition, directly on cycle classes. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG BGGBridge

variable {M N P : Type}
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup P] [Module ℂ P] [LieRingModule Current P] [LieModule ℂ Current P]

/-- The original coefficient map restricted to actual cycles. -/
def coefficientCyclesMap (f : M →ₗ⁅ℂ,Current⁆ N) :
    LinearMap.ker (differential M) →ₗ[ℂ] LinearMap.ker (differential N) :=
  (totalPairMap (coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f))
    (LinearMap.ext (coefficientMap_differential f))).cyclesMap

@[simp] theorem coefficientTotalHomologyMap_mk (f : M →ₗ⁅ℂ,Current⁆ N)
    (z : LinearMap.ker (differential M)) :
    coefficientTotalHomologyMap f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (coefficientCyclesMap f z) := rfl

@[simp] theorem coefficientTotalHomologyMap_id :
    coefficientTotalHomologyMap (LieModuleHom.id : M →ₗ⁅ℂ,Current⁆ M) = LinearMap.id := by
  apply LinearMap.ext
  intro u
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (differential M) (differential M)) u
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk z
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun coefficientMap_id z.val

theorem coefficientTotalHomologyMap_comp (f : M →ₗ⁅ℂ,Current⁆ N)
    (g : N →ₗ⁅ℂ,Current⁆ P) :
    coefficientTotalHomologyMap (g.comp f) =
      (coefficientTotalHomologyMap g).comp (coefficientTotalHomologyMap f) := by
  apply LinearMap.ext
  intro u
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (differential M) (differential M)) u
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (coefficientMap_comp f.toLinearMap g.toLinearMap
    (constantEquivariant_of_lieHom f) (constantEquivariant_of_lieHom g)) z.val

@[simp] theorem coefficientTotalHomologyMap_zero :
    coefficientTotalHomologyMap (0 : M →ₗ⁅ℂ,Current⁆ N) = 0 := by
  apply LinearMap.ext
  intro u
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (differential M) (differential M)) u
  have hz : coefficientCyclesMap (0 : M →ₗ⁅ℂ,Current⁆ N) z = 0 := by
    apply Subtype.ext
    exact LinearMap.congr_fun coefficientMap_zero z.val
  change Submodule.Quotient.mk (coefficientCyclesMap (0 : M →ₗ⁅ℂ,Current⁆ N) z) = 0
  rw [hz,Submodule.Quotient.mk_zero]

theorem coefficientTotalHomologyMap_add (f g : M →ₗ⁅ℂ,Current⁆ N) :
    coefficientTotalHomologyMap (f+g) =
      coefficientTotalHomologyMap f + coefficientTotalHomologyMap g := by
  apply LinearMap.ext
  intro u
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (differential M) (differential M)) u
  change (Submodule.Quotient.mk (coefficientCyclesMap (f+g) z) : TotalHomology N) =
    Submodule.Quotient.mk (coefficientCyclesMap f z) + Submodule.Quotient.mk (coefficientCyclesMap g z)
  rw [← Submodule.Quotient.mk_add]
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (coefficientMap_add f.toLinearMap g.toLinearMap
    (constantEquivariant_of_lieHom f) (constantEquivariant_of_lieHom g)) z.val

theorem coefficientMap_smul (c : ℂ) (f : M →ₗ[ℂ] N) (hf : ConstantEquivariant f) :
    coefficientMap (c • f) (fun x m => by
      change c • f ⁅constant x,m⁆ = ⁅constant x,c • f m⁆
      rw [hf,lie_smul]) = c • coefficientMap f hf := by
  apply Submodule.linearMap_qext
  apply TensorProduct.ext'
  intro ω m
  change (relC N).mkQ (ω ⊗ₜ[ℂ] (c • f m)) = c • (relC N).mkQ (ω ⊗ₜ[ℂ] f m)
  rw [TensorProduct.tmul_smul,map_smul]

theorem coefficientTotalHomologyMap_smul (c : ℂ) (f : M →ₗ⁅ℂ,Current⁆ N) :
    coefficientTotalHomologyMap (c • f) = c • coefficientTotalHomologyMap f := by
  apply LinearMap.ext
  intro u
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (differential M) (differential M)) u
  change (Submodule.Quotient.mk (coefficientCyclesMap (c • f) z) : TotalHomology N) =
    c • Submodule.Quotient.mk (coefficientCyclesMap f z)
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (coefficientMap_smul c f.toLinearMap
    (constantEquivariant_of_lieHom f)) z.val

end KhanSL2.Factorization
