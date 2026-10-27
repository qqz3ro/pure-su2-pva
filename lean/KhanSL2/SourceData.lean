module

public import KhanSL2.Source
public import KhanSL2.PVA
public import Mathlib.Algebra.Algebra.Bilinear

@[expose] public section

/-!
# The source data, independent of the cohomology construction

This module fixes the algebra, translation, grading and desired generator
brackets.  The associated structural claims are proved in the source modules.
-/

noncomputable section

namespace KhanSL2

def sourceData : DifferentialData Source where
  one := 1
  mul := LinearMap.mul ℂ Source
  translation := Source.translation
  piece := Source.piece

/-- The three specified generator brackets. -/
structure IsSourceBracket (br : LambdaBracket Source) : Prop where
  xx : br (Source.X 0) (Source.X 0) =
    Finsupp.single 0 (Source.X 1) + Finsupp.single 1 ((2 : ℂ) • Source.X 0)
  xy : br (Source.X 0) (Source.Y 0) =
    Finsupp.single 0 (Source.Y 1) + Finsupp.single 1 ((3 : ℂ) • Source.Y 0)
  yy : br (Source.Y 0) (Source.Y 0) = 0

end KhanSL2
