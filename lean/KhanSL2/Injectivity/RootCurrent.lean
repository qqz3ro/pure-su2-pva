module

public import KhanSL2.Injectivity.CartanRestriction

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity.Cartan

/-- Positive Cartan currents shift plus modes and negatively shift minus modes. -/
def rootCurrentGenerator (k : ℕ) : Mode → Cochain
  | .plus j => generator (.plus (j + k))
  | .minus j => -generator (.minus (j + k))
  | .neutral _ => 0
  | .cartan _ => 0

def rootCurrentAction (k : ℕ) : Cochain →ₗ[ℂ] Cochain :=
  FiniteExterior.extendDerivation Mode.code (rootCurrentGenerator k)

@[simp] theorem rootCurrentAction_generator (k : ℕ) (m : Mode) :
    rootCurrentAction k (generator m) = rootCurrentGenerator k m := by
  simp [rootCurrentAction, generator, FiniteExterior.generator,
    FiniteExterior.extendDerivation_monomial, FiniteExterior.position,
    Finset.filter_singleton, FiniteExterior.wedge_one_right]

@[simp] theorem rootCurrentAction_one (k : ℕ) : rootCurrentAction k 1 = 0 := by
  change rootCurrentAction k (FiniteExterior.monomial ∅) = 0
  simp [rootCurrentAction, FiniteExterior.extendDerivation_monomial]

theorem rootCurrentGenerator_odd (k : ℕ) (m : Mode) :
    FiniteExterior.parityLinear (rootCurrentGenerator k m) = -rootCurrentGenerator k m := by
  cases m <;> simp [rootCurrentGenerator]

theorem rootCurrentAction_mul (k : ℕ) (u v : Cochain) :
    rootCurrentAction k (u * v) = rootCurrentAction k u * v + u * rootCurrentAction k v := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_odd Mode.code Mode.code_injective
    (rootCurrentGenerator k m) (rootCurrentGenerator_odd k m) u).symm

end KhanSL2.Injectivity.Cartan
