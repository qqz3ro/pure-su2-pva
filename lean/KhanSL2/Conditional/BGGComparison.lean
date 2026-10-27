module

public import KhanSL2.Conditional.BGGHomologyAction

@[expose] public section

/-! # The unconditional coefficient-linear BGG homology comparison -/

noncomputable section
namespace KhanSL2.Conditional
open scoped KhanSL2.Conditional

/-- The fixed canonical comparison with its proved coefficient-ring linearity. -/
def bggHomologyEquiv (B p : ℕ) : BGGHomology B p ≃ₗ[CoefficientRing B] K B p where
  __ := canonicalComparison B p
  map_smul' := canonicalComparison_smul B p

@[simp] theorem bggHomologyEquiv_apply (B p : ℕ) (x : BGGHomology B p) :
    bggHomologyEquiv B p x = canonicalComparison B p x := rfl

end KhanSL2.Conditional
