module

public import KhanSL2.Factorization.ShuffleEquivalences
public import KhanSL2.Factorization.CoefficientSplitFinite

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Quotient dévissage for the actual kernel of a surjective current map. -/
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
open BGG
variable {M P : Type}
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup P] [Module ℂ P] [LieRingModule Current P] [LieModule ℂ Current P]
  [FiniteDimensional ℂ M] [FiniteDimensional ℂ P]

/-- A surjective current map has its genuine kernel constant-split from its source. -/
def kernelSplitOfSurjective (p : M →ₗ⁅ℂ,Current⁆ P) (hp : Function.Surjective p) :
    ConstantSplitExact p.ker.incl p :=
  Classical.choice (nonempty_constantSplitExact p.ker.incl p p.ker.injective_incl (by
    intro x
    constructor
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
    · rintro ⟨y,rfl⟩; exact y.property) hp)

variable (T : Type) [AddCommGroup T] [Module ℂ T]
  [LieRingModule Current T] [LieModule ℂ Current T]

/-- First-variable descent along a genuine surjective coefficient map. -/
theorem shuffle_quasiIso_surjective_first (p : M →ₗ⁅ℂ,Current⁆ P) (hp : Function.Surjective p)
    [QuasiIso (shuffleComplex p.ker T)] [QuasiIso (shuffleComplex M T)] :
    QuasiIso (shuffleComplex P T) :=
  shuffle_quasiIso_quotient_of_constantSplitExact T (kernelSplitOfSurjective p hp)

/-- Second-variable descent along a genuine surjective coefficient map. -/
theorem shuffle_quasiIso_surjective_second (p : M →ₗ⁅ℂ,Current⁆ P) (hp : Function.Surjective p)
    [QuasiIso (shuffleComplex T p.ker)] [QuasiIso (shuffleComplex T M)] :
    QuasiIso (shuffleComplex T P) :=
  shuffle_quasiIso_quotient_second_of_constantSplitExact T (kernelSplitOfSurjective p hp)

end KhanSL2.Factorization
