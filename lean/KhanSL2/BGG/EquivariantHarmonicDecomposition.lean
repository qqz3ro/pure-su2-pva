module

public import KhanSL2.BGG.PositiveHarmonicDecomposition
public import TauCeti.Algebra.Lie.Submodule.DirectSum

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The proved harmonic decomposition as an actual sl₂-module equivalence. -/
noncomputable section
open scoped DirectSum
namespace KhanSL2.BGG.PositiveCE

/-- Summing the actual harmonic degree pieces is an sl₂-module equivalence. -/
def harmonicDegreeEquiv : (⨁ p : ℕ, harmonicDegree p) ≃ₗ⁅ℂ,G⁆ Harmonic :=
  DirectSum.lieModuleEquivOfIsInternal harmonicDegree harmonicDegree_isInternal

/-- Choose one of the proved identifications of the actual degree-p harmonics
with the standard highest-weight `2p` module. -/
def harmonicDegreeStandardEquiv (p : ℕ) : harmonicDegree p ≃ₗ⁅ℂ,G⁆ TauCeti.Sl2Std ℂ (2*p) :=
  Classical.choice (harmonicDegree_nonempty_equiv_standard p)

/-- The actual harmonic space is the algebraic direct sum of `V(2p)`, one copy
in each degree p. This is an equivalence of actual constant-sl₂ representations. -/
def harmonicStandardEquiv : Harmonic ≃ₗ⁅ℂ,G⁆ (⨁ p : ℕ, TauCeti.Sl2Std ℂ (2*p)) :=
  harmonicDegreeEquiv.symm.trans (DirectSum.lieModuleEquivCongrRight harmonicDegreeStandardEquiv)

/-- The chosen standard module embeds in the actual harmonic space. -/
def standardHarmonicEmbedding (p : ℕ) : TauCeti.Sl2Std ℂ (2*p) →ₗ⁅ℂ,G⁆ Harmonic :=
  (harmonicDegree p).incl.comp (harmonicDegreeStandardEquiv p).symm.toLieModuleHom

/-- The embedded `V(2p)` has exterior degree p and physical energy p(p+1)/2. -/
theorem standardHarmonicEmbedding_mem_piece (p : ℕ) (v : TauCeti.Sl2Std ℂ (2*p)) :
    (standardHarmonicEmbedding p v : Cochain) ∈ piece p (triangular p) := by
  exact harmonic_mem_piece_of_degree p ((harmonicDegreeStandardEquiv p).symm v : Harmonic)
    ((harmonicDegreeStandardEquiv p).symm v).property

end KhanSL2.BGG.PositiveCE
