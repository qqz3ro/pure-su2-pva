module

public import KhanSL2.Macdonald.Evaluation
public import KhanSL2.BGG.CurrentBasis

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Recognizing genuine evaluation modules from their original current action.
The constant action is restricted along the actual constant-current inclusion. -/

noncomputable section
namespace KhanSL2.Macdonald

/-- A separate type for the actual constant restriction of a current module. -/
def ConstantRestriction (M : Type*) : Type _ := M

instance (M : Type*) [AddCommGroup M] : AddCommGroup (ConstantRestriction M) :=
  inferInstanceAs (AddCommGroup M)
instance (M : Type*) [AddCommGroup M] [Module ℂ M] : Module ℂ (ConstantRestriction M) :=
  inferInstanceAs (Module ℂ M)
instance (M : Type*) [AddCommGroup M] [LieRingModule BGG.Current M] :
    LieRingModule BGG.G (ConstantRestriction M) := LieRingModule.compLieHom M BGG.constant
instance (M : Type*) [AddCommGroup M] [Module ℂ M]
    [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M] :
    LieModule ℂ BGG.G (ConstantRestriction M) := LieModule.compLieHom M BGG.constant
instance (M : Type*) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] :
    FiniteDimensional ℂ (ConstantRestriction M) := inferInstanceAs (FiniteDimensional ℂ M)

/-- The underlying vector space of the constant restriction. -/
def constantRestrictionEquiv (M : Type*) [AddCommGroup M] [Module ℂ M] :
    ConstantRestriction M ≃ₗ[ℂ] M := LinearEquiv.refl ℂ M

@[simp] theorem constantRestriction_lie (M : Type*) [AddCommGroup M] [Module ℂ M]
    [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
    (x : BGG.G) (v : ConstantRestriction M) :
    constantRestrictionEquiv M ⁅x,v⁆ = ⁅BGG.constant x,constantRestrictionEquiv M v⁆ := rfl

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]

/-- The mode-wise evaluation identities imply the identity for every actual current. -/
theorem lie_eq_evaluated_of_modes (a : ℂ)
    (h : ∀ (n : ℕ) (x : BGG.G) (v : M), ⁅BGG.mode n x,v⁆ = a^n • ⁅BGG.constant x,v⁆)
    (u : BGG.Current) (v : M) : ⁅u,v⁆ = ⁅BGG.constant (currentEvaluation a u),v⁆ := by
  let f : BGG.Current →ₗ[ℂ] M :=
    { toFun := fun x => ⁅x,v⁆
      map_add' := fun x y => add_lie x y v
      map_smul' := fun z x => smul_lie z x v }
  have he : f = f.comp (BGG.constant.toLinearMap.comp (currentEvaluation a).toLinearMap) := by
    apply BGG.currentBasis.ext
    rintro ⟨n,c⟩
    change ⁅BGG.currentBasis (n,c),v⁆ = ⁅BGG.constant (currentEvaluation a (BGG.currentBasis (n,c))),v⁆
    rw [BGG.currentBasis_apply,currentEvaluation_mode,map_smul]
    rw [smul_lie (a^n) (BGG.constant (BGG.rootBasis c)) v]
    exact h n (BGG.rootBasis c) v
  exact LinearMap.congr_fun he u

/-- A module satisfying the proved mode identities is its actual constant restriction
pulled back by evaluation; this equivalence changes no underlying vector. -/
def evaluationRecognition (a : ℂ)
    (h : ∀ (n : ℕ) (x : BGG.G) (v : M), ⁅BGG.mode n x,v⁆ = a^n • ⁅BGG.constant x,v⁆) :
    M ≃ₗ⁅ℂ,BGG.Current⁆ Evaluation a (ConstantRestriction M) :=
  { ((constantRestrictionEquiv M).symm.trans (evaluationEquiv a (ConstantRestriction M)).symm) with
    map_lie' := fun {u v} => lie_eq_evaluated_of_modes a h u v }

end KhanSL2.Macdonald
