module

public import KhanSL2.Factorization.KunnethTensorDifferential
public import KhanSL2.Factorization.KunnethTensorBigrading
public import KhanSL2.Factorization.ShuffleRelativeNaturality

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The specified relative CE shuffle as a morphism to the genuine categorical
tensor complex. The construction is transported through the actual homogeneous
components, and its value in ungraded chains is the original shuffle. -/

noncomputable section
open scoped TensorProduct
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization
open KhanSL2.BGG

variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

/-- The degree-j component of the actual canonical relative shuffle. -/
def degreeShuffle (j : ℕ) :
    degree (M ⊗[ℂ] N) j →ₗ[ℂ] (tensorComplex M N).X j :=
  (tensorDegreeComponent M N j).comp
    ((relativeShuffle M N).comp (degree (M ⊗[ℂ] N) j).subtype)

/-- Forgetting the degree-sum packaging returns the specified shuffle exactly. -/
@[simp] theorem tensorDegreeForget_degreeShuffle (j : ℕ)
    (z : degree (M ⊗[ℂ] N) j) :
    tensorDegreeForget M N j (degreeShuffle M N j z) = relativeShuffle M N z.val := by
  apply tensorDegreeForget_component_of_eigen M N
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [← relativeShuffle_euler, relativeEuler_of_mem_degree (M ⊗[ℂ] N) z.property,
    map_smul]

/-- The canonical relative shuffle is a morphism of the actual degree-sum complexes. -/
def shuffleComplex : complex (M ⊗[ℂ] N) ⟶ tensorComplex M N :=
  ChainComplex.ofHom (fun j => ModuleCat.ofHom (degreeShuffle M N j)) (fun j => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change degree (M ⊗[ℂ] N) (j+1) at z
    apply tensorDegreeForget_injective M N j
    have hd := congrArg (fun f => f.hom (degreeShuffle M N (j+1) z))
      (tensorDegreeForget_differential M N j)
    change tensorDegreeForget M N j
      ((tensorComplex M N).d (j+1) j (degreeShuffle M N (j+1) z)) =
        relativeTensorDifferential M N
          (tensorDegreeForget M N (j+1) (degreeShuffle M N (j+1) z)) at hd
    change tensorDegreeForget M N j
      ((tensorComplex M N).d (j+1) j (degreeShuffle M N (j+1) z)) =
        tensorDegreeForget M N j
          (degreeShuffle M N j ((complex (M ⊗[ℂ] N)).d (j+1) j z))
    rw [hd, tensorDegreeForget_degreeShuffle, tensorDegreeForget_degreeShuffle]
    rw [complex_d]
    exact (relativeShuffle_differential M N
      (show degree (M ⊗[ℂ] N) (j+1) from z).val).symm)

@[simp] theorem shuffleComplex_f (j : ℕ) :
    (shuffleComplex M N).f j = ModuleCat.ofHom (degreeShuffle M N j) := rfl

/-- The induced canonical homology comparison, before invoking any factorization theorem. -/
def shuffleHomology (j : ℕ) :
    (complex (M ⊗[ℂ] N)).homology j ⟶ (tensorComplex M N).homology j :=
  HomologicalComplex.homologyMap (shuffleComplex M N) j

/-- The same canonical comparison with target the degree-sum of factor homologies,
using the inverse of the actual field Künneth isomorphism. -/
def shuffleKunnethHomology (j : ℕ) :
    (complex (M ⊗[ℂ] N)).homology j ⟶
      CategoryTheory.GradedObject.Monoidal.tensorObj
        (fun p => (complex M).homology p) (fun q => (complex N).homology q) j := by
  have := relativeComplex_kunneth M N j
  exact shuffleHomology M N j ≫
    CategoryTheory.inv (HomologicalComplex.homologyKunneth (complex M) (complex N) j)

end KhanSL2.Factorization
