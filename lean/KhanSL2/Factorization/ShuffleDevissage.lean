module

public import KhanSL2.Factorization.TensorCoefficientDegrees
public import KhanSL2.Factorization.NonnegativeConeDevissage

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG

variable {N M P : Type}
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup P] [Module ℂ P] [LieRingModule Current P] [LieModule ℂ Current P]
variable (T : Type) [AddCommGroup T] [Module ℂ T]
  [LieRingModule Current T] [LieModule ℂ Current T]
variable {i : N →ₗ⁅ℂ,Current⁆ M} {p : M →ₗ⁅ℂ,Current⁆ P}

/-- The underlying tensor-complex terms retain a constant splitting degree by degree. -/
theorem ConstantSplitExact.tensorDegree_shortExact (h : ConstantSplitExact i p) (j : ℕ) :
    Function.Injective (tensorCoefficientDegreeMap T i.toLinearMap (constantEquivariant_of_lieHom i) j) ∧
      Function.Exact (tensorCoefficientDegreeMap T i.toLinearMap (constantEquivariant_of_lieHom i) j)
        (tensorCoefficientDegreeMap T p.toLinearMap (constantEquivariant_of_lieHom p) j) ∧
      Function.Surjective (tensorCoefficientDegreeMap T p.toLinearMap (constantEquivariant_of_lieHom p) j) := by
  let I := tensorCoefficientDegreeMap T i.toLinearMap (constantEquivariant_of_lieHom i) j
  let P := tensorCoefficientDegreeMap T p.toLinearMap (constantEquivariant_of_lieHom p) j
  let R := tensorCoefficientDegreeMap T h.retraction h.retraction_constant j
  let S := tensorCoefficientDegreeMap T h.sectionMap h.section_constant j
  have hRI : R.comp I = LinearMap.id := by
    dsimp [R,I]
    rw [← tensorCoefficientDegreeMap_comp]
    simp only [h.left_inverse,tensorCoefficientDegreeMap_id]
  have hPS : P.comp S = LinearMap.id := by
    dsimp [P,S]
    rw [← tensorCoefficientDegreeMap_comp]
    simp only [h.right_inverse,tensorCoefficientDegreeMap_id]
  have hPI : P.comp I = 0 := by
    dsimp [P,I]
    rw [← tensorCoefficientDegreeMap_comp]
    simp only [h.zero_comp,tensorCoefficientDegreeMap_zero]
  have hdecomp : I.comp R + S.comp P = LinearMap.id := by
    dsimp [I,R,S,P]
    rw [← tensorCoefficientDegreeMap_comp,← tensorCoefficientDegreeMap_comp,
      ← tensorCoefficientDegreeMap_add]
    simp only [h.decomposition,tensorCoefficientDegreeMap_id]
  change Function.Injective I ∧ Function.Exact I P ∧ Function.Surjective P
  have hRI' : Function.LeftInverse R I := fun x => LinearMap.congr_fun hRI x
  have hPS' : Function.RightInverse S P := fun x => LinearMap.congr_fun hPS x
  refine ⟨hRI'.injective,?_,hPS'.surjective⟩
  intro y
  constructor
  · intro hy
    refine ⟨R y,?_⟩
    have he := LinearMap.congr_fun hdecomp y
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,hy,map_zero,add_zero,LinearMap.id_apply] using he
  · rintro ⟨x,rfl⟩
    exact LinearMap.congr_fun hPI x

/-- The same exactness statement for the actual categorical tensor maps. -/
theorem ConstantSplitExact.tensorChain_shortExact (h : ConstantSplitExact i p) (j : ℕ) :
    Function.Injective ((HomologicalComplex.tensorHom (complexMap i)
      (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T))).f j) ∧
    Function.Exact ((HomologicalComplex.tensorHom (complexMap i)
      (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T))).f j)
      ((HomologicalComplex.tensorHom (complexMap p)
      (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T))).f j) ∧
    Function.Surjective ((HomologicalComplex.tensorHom (complexMap p)
      (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T))).f j) := by
  simpa only [tensorCoefficientDegreeMap_lie] using h.tensorDegree_shortExact T j

/-- Appendix A.4 extension step for the specified relative CE shuffle.
Both coefficient splittings are only constant-equivariant. -/
theorem shuffle_quasiIso_of_constantSplitExact (h : ConstantSplitExact i p)
    [QuasiIso (shuffleComplex N T)] [QuasiIso (shuffleComplex P T)] :
    QuasiIso (shuffleComplex M T) := by
  apply NonnegativeCone.quasiIso_of_shortExact_rows
    (complexMap (TensorProduct.LieModule.map i (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (complexMap (TensorProduct.LieModule.map p (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (HomologicalComplex.tensorHom (complexMap i) (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (HomologicalComplex.tensorHom (complexMap p) (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (shuffleComplex N T) (shuffleComplex M T) (shuffleComplex P T)
    (shuffleComplex_natural i (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)).symm
    (shuffleComplex_natural p (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)).symm
  · intro j; exact ((h.tensorRight T).chain_shortExact j).1
  · intro j; exact ((h.tensorRight T).chain_shortExact j).2.1
  · intro j; exact ((h.tensorRight T).chain_shortExact j).2.2
  · intro j; exact (h.tensorChain_shortExact T j).1
  · intro j; exact (h.tensorChain_shortExact T j).2.1
  · intro j; exact (h.tensorChain_shortExact T j).2.2

/-- Appendix A.4 quotient step for the specified relative CE shuffle.
Both coefficient splittings are only constant-equivariant. -/
theorem shuffle_quasiIso_quotient_of_constantSplitExact (h : ConstantSplitExact i p)
    [QuasiIso (shuffleComplex N T)] [QuasiIso (shuffleComplex M T)] :
    QuasiIso (shuffleComplex P T) := by
  apply NonnegativeCone.quasiIso_quotient_of_shortExact_rows
    (complexMap (TensorProduct.LieModule.map i (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (complexMap (TensorProduct.LieModule.map p (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (HomologicalComplex.tensorHom (complexMap i) (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (HomologicalComplex.tensorHom (complexMap p) (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (shuffleComplex N T) (shuffleComplex M T) (shuffleComplex P T)
    (shuffleComplex_natural i (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)).symm
    (shuffleComplex_natural p (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)).symm
  · intro j; exact ((h.tensorRight T).chain_shortExact j).1
  · intro j; exact ((h.tensorRight T).chain_shortExact j).2.1
  · intro j; exact ((h.tensorRight T).chain_shortExact j).2.2
  · intro j; exact (h.tensorChain_shortExact T j).1
  · intro j; exact (h.tensorChain_shortExact T j).2.1
  · intro j; exact (h.tensorChain_shortExact T j).2.2

/-- Appendix A.4 submodule step for the specified relative CE shuffle.
Both coefficient splittings are only constant-equivariant. -/
theorem shuffle_quasiIso_submodule_of_constantSplitExact (h : ConstantSplitExact i p)
    [QuasiIso (shuffleComplex M T)] [QuasiIso (shuffleComplex P T)] :
    QuasiIso (shuffleComplex N T) := by
  apply NonnegativeCone.quasiIso_subcomplex_of_shortExact_rows
    (complexMap (TensorProduct.LieModule.map i (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (complexMap (TensorProduct.LieModule.map p (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (HomologicalComplex.tensorHom (complexMap i) (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (HomologicalComplex.tensorHom (complexMap p) (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (shuffleComplex N T) (shuffleComplex M T) (shuffleComplex P T)
    (shuffleComplex_natural i (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)).symm
    (shuffleComplex_natural p (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)).symm
  · intro j; exact ((h.tensorRight T).chain_shortExact j).1
  · intro j; exact ((h.tensorRight T).chain_shortExact j).2.1
  · intro j; exact ((h.tensorRight T).chain_shortExact j).2.2
  · intro j; exact (h.tensorChain_shortExact T j).1
  · intro j; exact (h.tensorChain_shortExact T j).2.1
  · intro j; exact (h.tensorChain_shortExact T j).2.2

end KhanSL2.Factorization