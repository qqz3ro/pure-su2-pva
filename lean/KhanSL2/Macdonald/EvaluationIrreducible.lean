module

public import KhanSL2.Macdonald.Evaluation
public import KhanSL2.BGG.Terms

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Even standard evaluation modules are actual finite-dimensional irreducible
representations of the polynomial current algebra. -/

noncomputable section
namespace KhanSL2.Macdonald

instance (a : ℂ) (V : Type*) [Nontrivial V] : Nontrivial (Evaluation a V) :=
  inferInstanceAs (Nontrivial V)

/-- Evaluation preserves irreducibility because every constant Lie element is in its image. -/
instance evaluation_irreducible (a : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule BGG.G V] [LieModule ℂ BGG.G V] [Nontrivial V]
    [LieModule.IsIrreducible ℂ BGG.G V] :
    LieModule.IsIrreducible ℂ BGG.Current (Evaluation a V) := by
  refine LieModule.IsIrreducible.mk fun N hN => ?_
  let Q : LieSubmodule ℂ BGG.G V :=
    { toSubmodule := N.toSubmodule
      lie_mem := by
        intro x v hv
        have h := N.lie_mem (x := BGG.constant x) hv
        change ⁅currentEvaluation a (BGG.constant x),v⁆ ∈ N at h
        change ⁅x,v⁆ ∈ N
        simpa only [currentEvaluation_constant] using h }
  have hQ : Q ≠ ⊥ := by
    intro h
    apply hN
    apply (LieSubmodule.toSubmodule_eq_bot N).mp
    exact congrArg LieSubmodule.toSubmodule h
  have ht : Q = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top Q).resolve_left hQ
  apply (LieSubmodule.toSubmodule_eq_top N).mp
  exact congrArg LieSubmodule.toSubmodule ht

/-- The module V(2p) evaluated at a complex point, as used in the even factorization category. -/
abbrev EvenEvaluation (a : ℂ) (p : ℕ) := Evaluation a (BGG.Coefficient p)

theorem evenEvaluation_finrank (a : ℂ) (p : ℕ) :
    Module.finrank ℂ (EvenEvaluation a p) = 2*p+1 :=
  (evaluationEquiv a (BGG.Coefficient p)).finrank_eq.trans (BGG.coefficient_finrank p)

end KhanSL2.Macdonald
