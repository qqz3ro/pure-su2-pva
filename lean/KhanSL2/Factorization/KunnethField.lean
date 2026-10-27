module

public import KhanSL2.Factorization.RelativeChainsComplex
public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Basic

@[expose] public section

/-! Field Künneth for the actual bundled relative CE complexes. -/

noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
open KhanSL2.BGG

variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

/-- The canonical Künneth map is an isomorphism for the actual relative CE complexes
because their terms and cycle spaces are complex vector spaces. -/
theorem relativeComplex_kunneth (j : ℕ) :
    IsIso (HomologicalComplex.homologyKunneth (complex M) (complex N) j) := by
  infer_instance

end KhanSL2.Factorization
