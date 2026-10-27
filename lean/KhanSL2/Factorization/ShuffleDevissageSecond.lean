module

public import KhanSL2.Factorization.TensorCoefficientDegreesLeft
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
theorem ConstantSplitExact.tensorDegree_shortExact_second (h : ConstantSplitExact i p) (j : ℕ) :
    Function.Injective (tensorCoefficientDegreeMapLeft T i.toLinearMap (constantEquivariant_of_lieHom i) j) ∧
      Function.Exact (tensorCoefficientDegreeMapLeft T i.toLinearMap (constantEquivariant_of_lieHom i) j)
        (tensorCoefficientDegreeMapLeft T p.toLinearMap (constantEquivariant_of_lieHom p) j) ∧
      Function.Surjective (tensorCoefficientDegreeMapLeft T p.toLinearMap (constantEquivariant_of_lieHom p) j) := by
  let I := tensorCoefficientDegreeMapLeft T i.toLinearMap (constantEquivariant_of_lieHom i) j
  let P := tensorCoefficientDegreeMapLeft T p.toLinearMap (constantEquivariant_of_lieHom p) j
  let R := tensorCoefficientDegreeMapLeft T h.retraction h.retraction_constant j
  let S := tensorCoefficientDegreeMapLeft T h.sectionMap h.section_constant j
  have hRI : R.comp I = LinearMap.id := by
    dsimp [R,I]
    rw [← tensorCoefficientDegreeMapLeft_comp]
    simp only [h.left_inverse,tensorCoefficientDegreeMapLeft_id]
  have hPS : P.comp S = LinearMap.id := by
    dsimp [P,S]
    rw [← tensorCoefficientDegreeMapLeft_comp]
    simp only [h.right_inverse,tensorCoefficientDegreeMapLeft_id]
  have hPI : P.comp I = 0 := by
    dsimp [P,I]
    rw [← tensorCoefficientDegreeMapLeft_comp]
    simp only [h.zero_comp,tensorCoefficientDegreeMapLeft_zero]
  have hdecomp : I.comp R + S.comp P = LinearMap.id := by
    dsimp [I,R,S,P]
    rw [← tensorCoefficientDegreeMapLeft_comp,← tensorCoefficientDegreeMapLeft_comp,
      ← tensorCoefficientDegreeMapLeft_add]
    simp only [h.decomposition,tensorCoefficientDegreeMapLeft_id]
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
theorem ConstantSplitExact.tensorChain_shortExact_second (h : ConstantSplitExact i p) (j : ℕ) :
    Function.Injective ((HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap i)).f j) ∧
    Function.Exact ((HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap i)).f j)
      ((HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap p)).f j) ∧
    Function.Surjective ((HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap p)).f j) := by
  simpa only [tensorCoefficientDegreeMapLeft_lie] using h.tensorDegree_shortExact_second T j

/-- Appendix A.4 extension step for the specified relative CE shuffle.
Both coefficient splittings are only constant-equivariant. -/
theorem shuffle_quasiIso_second_of_constantSplitExact (h : ConstantSplitExact i p)
    [QuasiIso (shuffleComplex T N)] [QuasiIso (shuffleComplex T P)] :
    QuasiIso (shuffleComplex T M) := by
  apply NonnegativeCone.quasiIso_of_shortExact_rows
    (complexMap (TensorProduct.LieModule.map (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) i))
    (complexMap (TensorProduct.LieModule.map (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) p))
    (HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap i))
    (HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap p))
    (shuffleComplex T N) (shuffleComplex T M) (shuffleComplex T P)
    (shuffleComplex_natural (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) i).symm
    (shuffleComplex_natural (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) p).symm
  · intro j; exact ((h.tensorLeft T).chain_shortExact j).1
  · intro j; exact ((h.tensorLeft T).chain_shortExact j).2.1
  · intro j; exact ((h.tensorLeft T).chain_shortExact j).2.2
  · intro j; exact (h.tensorChain_shortExact_second T j).1
  · intro j; exact (h.tensorChain_shortExact_second T j).2.1
  · intro j; exact (h.tensorChain_shortExact_second T j).2.2

/-- Appendix A.4 quotient step for the specified relative CE shuffle.
Both coefficient splittings are only constant-equivariant. -/
theorem shuffle_quasiIso_quotient_second_of_constantSplitExact (h : ConstantSplitExact i p)
    [QuasiIso (shuffleComplex T N)] [QuasiIso (shuffleComplex T M)] :
    QuasiIso (shuffleComplex T P) := by
  apply NonnegativeCone.quasiIso_quotient_of_shortExact_rows
    (complexMap (TensorProduct.LieModule.map (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) i))
    (complexMap (TensorProduct.LieModule.map (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) p))
    (HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap i))
    (HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap p))
    (shuffleComplex T N) (shuffleComplex T M) (shuffleComplex T P)
    (shuffleComplex_natural (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) i).symm
    (shuffleComplex_natural (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) p).symm
  · intro j; exact ((h.tensorLeft T).chain_shortExact j).1
  · intro j; exact ((h.tensorLeft T).chain_shortExact j).2.1
  · intro j; exact ((h.tensorLeft T).chain_shortExact j).2.2
  · intro j; exact (h.tensorChain_shortExact_second T j).1
  · intro j; exact (h.tensorChain_shortExact_second T j).2.1
  · intro j; exact (h.tensorChain_shortExact_second T j).2.2

/-- Appendix A.4 submodule step for the specified relative CE shuffle.
Both coefficient splittings are only constant-equivariant. -/
theorem shuffle_quasiIso_submodule_second_of_constantSplitExact (h : ConstantSplitExact i p)
    [QuasiIso (shuffleComplex T M)] [QuasiIso (shuffleComplex T P)] :
    QuasiIso (shuffleComplex T N) := by
  apply NonnegativeCone.quasiIso_subcomplex_of_shortExact_rows
    (complexMap (TensorProduct.LieModule.map (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) i))
    (complexMap (TensorProduct.LieModule.map (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) p))
    (HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap i))
    (HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap p))
    (shuffleComplex T N) (shuffleComplex T M) (shuffleComplex T P)
    (shuffleComplex_natural (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) i).symm
    (shuffleComplex_natural (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) p).symm
  · intro j; exact ((h.tensorLeft T).chain_shortExact j).1
  · intro j; exact ((h.tensorLeft T).chain_shortExact j).2.1
  · intro j; exact ((h.tensorLeft T).chain_shortExact j).2.2
  · intro j; exact (h.tensorChain_shortExact_second T j).1
  · intro j; exact (h.tensorChain_shortExact_second T j).2.1
  · intro j; exact (h.tensorChain_shortExact_second T j).2.2

end KhanSL2.Factorization