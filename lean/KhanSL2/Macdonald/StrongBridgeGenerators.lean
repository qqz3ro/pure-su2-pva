module

public import KhanSL2.Macdonald.StrongBridgeAlgebra
public import KhanSL2.Macdonald.Generators
public import KhanSL2.StrongMacdonald.Generators

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The algebra comparison preserves the named Macdonald generators exactly.
The harmless -S and 2E normalization of the harmonic normal-form map is kept
explicit, rather than absorbed into unspecified cohomology generators. -/
noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

@[simp] theorem strongModel_sigOf (n : ℕ) (a : Fin 3) :
    strongModel (StrongMacdonald.sigOf n a) = sigma a n := strongModel_sig _

@[simp] theorem strongModel_psiOf (n : ℕ) (a : Fin 3) :
    strongModel (StrongMacdonald.psiOf n a) = psi a n := strongModel_psi _

@[simp] theorem strongModel_Sgen (n : ℕ) : strongModel (StrongMacdonald.Sgen n) = S n := by
  simp only [StrongMacdonald.Sgen, map_sum, strongModel_mul, strongModel_sigOf, S]
  exact Finset.sum_comm

@[simp] theorem strongModel_Egen (n : ℕ) : strongModel (StrongMacdonald.Egen n) = E n := by
  simp only [StrongMacdonald.Egen, map_sum, map_smul, strongModel_mul,
    strongModel_sigOf, strongModel_psiOf, E, Nat.cast_add, Nat.cast_one]
  exact Finset.sum_comm

@[simp] theorem strongModel_neg_Sgen (n : ℕ) :
    strongModel (-StrongMacdonald.Sgen n) = -S n := by simp

@[simp] theorem strongModel_two_Egen (n : ℕ) :
    strongModel ((2 : ℂ) • StrongMacdonald.Egen n) = (2 : ℂ) • E n := by simp

end KhanSL2.Macdonald
