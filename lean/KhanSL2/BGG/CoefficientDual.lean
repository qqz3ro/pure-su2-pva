module

public import KhanSL2.BGG.Terms
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Algebra.Lie.Sl2.Classification
public import TauCeti.Algebra.Lie.Dual

@[expose] public section
noncomputable section
namespace KhanSL2.BGG

/-- The actual standard coefficient V(2p) is self-dual as a constant sl₂ module.
This follows from the proved classification, irreducibility of the dual, and dimension. -/
theorem coefficient_nonempty_dual_equiv (p : ℕ) :
    Nonempty (Coefficient p ≃ₗ⁅ℂ,G⁆ Module.Dual ℂ (Coefficient p)) := by
  let : LieModule.IsIrreducible ℂ G (Module.Dual ℂ (Coefficient p)) :=
    TauCeti.LieModule.isIrreducible_dual
  obtain ⟨n, ⟨e⟩, _⟩ := TauCeti.Sl2Std.existsUnique_nonempty_lieModuleEquiv
    (K := ℂ) (Module.Dual ℂ (Coefficient p))
  have hn : n = 2*p := by
    have h := e.toLinearEquiv.finrank_eq
    rw [Subspace.dual_finrank_eq, coefficient_finrank, TauCeti.Sl2Std.finrank_eq] at h
    omega
  subst n
  exact ⟨e.symm⟩

/-- A chosen, proved equivariant self-duality of the specified standard module. -/
def coefficientDualEquiv (p : ℕ) : Coefficient p ≃ₗ⁅ℂ,G⁆ Module.Dual ℂ (Coefficient p) :=
  Classical.choice (coefficient_nonempty_dual_equiv p)

end KhanSL2.BGG