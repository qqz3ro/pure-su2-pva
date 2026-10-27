module

public import KhanSL2.Factorization.ShuffleComplex

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The categorical shuffle retains the naturality of the actual coefficient maps. -/

noncomputable section
open scoped TensorProduct
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization
open KhanSL2.BGG

variable {M N M' N' : Type}
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M'] [Module ℂ M'] [LieRingModule Current M'] [LieModule ℂ Current M']
  [AddCommGroup N'] [Module ℂ N'] [LieRingModule Current N'] [LieModule ℂ Current N']

/-- Forgetting tensor degree commutes with the actual categorical coefficient map. -/
theorem tensorDegreeForget_tensorHom (f : M →ₗ⁅ℂ,Current⁆ M')
    (g : N →ₗ⁅ℂ,Current⁆ N') (j : ℕ) :
    (HomologicalComplex.tensorHom (complexMap f) (complexMap g)).f j ≫
      ModuleCat.ofHom (tensorDegreeForget M' N' j) =
        ModuleCat.ofHom (tensorDegreeForget M N j) ≫ ModuleCat.ofHom
          (TensorProduct.map (coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f))
            (coefficientMap g.toLinearMap (constantEquivariant_of_lieHom g))) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.ι_tensorHom_assoc, tensorDegreeInclusion_forget,
    tensorDegreeInclusion_forget_assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  rfl

/-- The specified shuffle is natural as a genuine morphism of tensor complexes. -/
theorem shuffleComplex_natural (f : M →ₗ⁅ℂ,Current⁆ M')
    (g : N →ₗ⁅ℂ,Current⁆ N') :
    complexMap (TensorProduct.LieModule.map f g) ≫ shuffleComplex M' N' =
      shuffleComplex M N ≫ HomologicalComplex.tensorHom (complexMap f) (complexMap g) := by
  ext j : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change degree (M ⊗[ℂ] N) j at z
  apply tensorDegreeForget_injective M' N' j
  have hn := congrArg (fun φ => φ.hom (degreeShuffle M N j z))
    (tensorDegreeForget_tensorHom f g j)
  change tensorDegreeForget M' N' j
    ((HomologicalComplex.tensorHom (complexMap f) (complexMap g)).f j
      (degreeShuffle M N j z)) =
        TensorProduct.map
          (coefficientMap f.toLinearMap (constantEquivariant_of_lieHom f))
          (coefficientMap g.toLinearMap (constantEquivariant_of_lieHom g))
          (tensorDegreeForget M N j (degreeShuffle M N j z)) at hn
  change tensorDegreeForget M' N' j (degreeShuffle M' N' j
      (coefficientDegreeMap (TensorProduct.LieModule.map f g).toLinearMap
        (constantEquivariant_of_lieHom (TensorProduct.LieModule.map f g)) j z)) =
    tensorDegreeForget M' N' j
      ((HomologicalComplex.tensorHom (complexMap f) (complexMap g)).f j
        (degreeShuffle M N j z))
  rw [hn, tensorDegreeForget_degreeShuffle, tensorDegreeForget_degreeShuffle]
  exact relativeShuffle_coeffMap f.toLinearMap g.toLinearMap
    (constantEquivariant_of_lieHom f) (constantEquivariant_of_lieHom g)
    (show degree (M ⊗[ℂ] N) j from z).val

end KhanSL2.Factorization
