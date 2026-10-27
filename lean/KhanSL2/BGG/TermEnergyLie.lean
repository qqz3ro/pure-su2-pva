module

public import KhanSL2.BGG.TermFiniteEnergy
public import KhanSL2.BGG.TermResolutionGradedExactness
public import KhanSL2.BGG.TermResolutionAugmentation
public import KhanSL2.BGG.RelativeCoefficientAction
public import TauCeti.Algebra.Lie.Submodule.DirectSum

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped DirectSum
namespace KhanSL2.BGG.TermResolution
open scoped RelativeCochains

/-- Each actual energy component is a subrepresentation for the constant sl₂ action. -/
def energyLiePiece (p : ℕ) (n : ℤ) : LieSubmodule ℂ G (Term p) :=
  { termPiece p n with
    lie_mem := fun {x _u} hu => constant_lie_mem_termPiece p x hu }

@[simp] theorem energyLiePiece_toSubmodule (p : ℕ) (n : ℤ) :
    (energyLiePiece p n).toSubmodule = termPiece p n := rfl

instance finiteDimensional_energyLiePiece (p : ℕ) (n : ℤ) :
    FiniteDimensional ℂ (energyLiePiece p n) :=
  inferInstanceAs (FiniteDimensional ℂ (termPiece p n))

/-- The genuine internal energy decomposition, now as an sl₂-module equivalence. -/
def energyLieEquiv (p : ℕ) : (⨁ n : ℤ, energyLiePiece p n) ≃ₗ⁅ℂ,G⁆ Term p :=
  DirectSum.lieModuleEquivOfIsInternal (energyLiePiece p) (termPiece_isInternal p)

@[simp] theorem energyLieEquiv_of (p : ℕ) (n : ℤ) (u : energyLiePiece p n) :
    energyLieEquiv p (DirectSum.of (fun n => energyLiePiece p n) n u) = u := by
  simp only [energyLieEquiv, DirectSum.lieModuleEquivOfIsInternal_apply,
    DirectSum.coeLieModuleHom_of]

@[simp] theorem energyLieEquiv_symm_coe (p : ℕ) (n : ℤ) (u : energyLiePiece p n) :
    (energyLieEquiv p).symm (u : Term p) = DirectSum.of (fun n => energyLiePiece p n) n u := by
  exact (energyLieEquiv p).toLinearEquiv.symm_apply_eq.mpr (energyLieEquiv_of p n u).symm

/-- The actual homogeneous BGG map is a morphism of the finite sl₂ representations. -/
def energyLieDifferential (p : ℕ) (n : ℤ) :
    energyLiePiece (p+1) n →ₗ⁅ℂ,G⁆ energyLiePiece p n where
  toLinearMap := energyDifferential p n
  map_lie' {x} {u} := by
    apply Subtype.ext
    change differential p (constGenerator x • (u : Term (p+1))) =
      constGenerator x • differential p u
    exact (differential p).map_smul _ _

@[simp] theorem energyLieDifferential_coe (p : ℕ) (n : ℤ) (u : energyLiePiece (p+1) n) :
    (energyLieDifferential p n u : Term p) = differential p u := rfl

/-- The augmentation on energy zero lands in the actual trivial sl₂ representation. -/
def energyLieAugmentation : energyLiePiece 0 0 →ₗ⁅ℂ,G⁆ TrivialLieModule ℂ G ℂ where
  toLinearMap := (TrivialLieModule.equiv ℂ G ℂ).symm.toLinearMap.comp (energyAugmentation 0)
  map_lie' {x} {u} := by
    change augmentation (constGenerator x • (u : Term 0)) = 0
    exact augmentation_constant x u

theorem energyLieAugmentation_surjective : Function.Surjective energyLieAugmentation := by
  intro r
  obtain ⟨u, hu⟩ := energyAugmentation_zero_surjective ((TrivialLieModule.equiv ℂ G ℂ) r)
  refine ⟨u, ?_⟩
  apply (TrivialLieModule.equiv ℂ G ℂ).injective
  exact hu

end KhanSL2.BGG.TermResolution
