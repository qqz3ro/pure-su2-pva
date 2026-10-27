module

public import KhanSL2.SourceData
public import KhanSL2.SourceGrading
public import KhanSL2.SourceSupercomm

@[expose] public section

/-!
# The source is a graded differential superalgebra

All algebra and grading laws are proved here independently of cohomology and
of the main isomorphism statement.
-/

namespace KhanSL2

theorem source_isGradedDifferentialSuperalgebra :
    IsGradedDifferentialSuperalgebra Source sourceData where
  grading_internal := Source.grading_internal
  one_mul := one_mul
  mul_one := mul_one
  mul_assoc := mul_assoc
  supercomm := fun _ _ _ _ ha hb => Source.supercomm ha hb
  one_degree := Source.one_mem
  mul_degree := fun _ _ _ _ ha hb => Source.mul_mem ha hb
  translation_degree := by
    intro d a ha
    have hd : d + (0, 0, 1) = (d.1, d.2.1, d.2.2 + 1) := by
      ext <;> simp
    simpa only [sourceData, Degree.translate, hd] using Source.translation_mem ha
  translation_one := rfl
  translation_mul := Source.translation_mul

end KhanSL2
