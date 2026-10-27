module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Basic.Complex.Basic

@[expose] public section

/-! A specified perfect evaluation pairing identifies the annihilator of actual
relations with the dual of their quotient. No splitting of the quotient is chosen. -/

noncomputable section
namespace KhanSL2.Factorization.PerfectDuality

variable {A C : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup C] [Module ℂ C]

/-- Cochains annihilating a specified relation subspace under a specified perfect pairing. -/
def annihilator (e : A ≃ₗ[ℂ] Module.Dual ℂ C) (R : Submodule ℂ C) : Submodule ℂ A :=
  R.dualAnnihilator.comap e.toLinearMap

@[simp] theorem mem_annihilator (e : A ≃ₗ[ℂ] Module.Dual ℂ C)
    (R : Submodule ℂ C) (a : A) :
    a ∈ annihilator e R ↔ ∀ r ∈ R, e a r = 0 :=
  Submodule.mem_dualAnnihilator (e a)

/-- The canonical dual of a quotient, transported along the specified perfect pairing. -/
def annihilatorEquivDualQuotient (e : A ≃ₗ[ℂ] Module.Dual ℂ C)
    (R : Submodule ℂ C) : annihilator e R ≃ₗ[ℂ] Module.Dual ℂ (C ⧸ R) :=
  (e.ofSubmodule' R.dualAnnihilator).trans R.dualQuotEquivDualAnnihilator.symm

/-- The equivalence is characterized by the original evaluation pairing. -/
@[simp] theorem annihilatorEquivDualQuotient_apply_mk
    (e : A ≃ₗ[ℂ] Module.Dual ℂ C) (R : Submodule ℂ C)
    (a : annihilator e R) (c : C) :
    annihilatorEquivDualQuotient e R a (Submodule.Quotient.mk c) = e a.val c := rfl

end KhanSL2.Factorization.PerfectDuality
