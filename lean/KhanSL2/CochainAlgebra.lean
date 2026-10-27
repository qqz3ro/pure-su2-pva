module

public import KhanSL2.CELeibniz
public import KhanSL2.Data

@[expose] public section

/-! All graded differential superalgebra laws for the fixed cochain operations. -/

noncomputable section

namespace KhanSL2

theorem cochain_algebra : IsGradedDifferentialSuperalgebra Cochain cochainData where
  grading_internal := cochain_grading_internal
  one_mul := cochainOne_wedge
  mul_one := wedge_cochainOne
  mul_assoc := wedge_assoc
  supercomm _ _ _ _ hu hv := cochain_supercomm hu hv
  one_degree := cochain_one_mem
  mul_degree _ _ _ _ hu hv := cochain_wedge_mem hu hv
  translation_degree d a hu := by
    rcases d with ⟨k, b, s⟩
    simpa [cochainData, Degree.translate, Prod.add_def] using translation_degree hu
  translation_one := by
    change translation cochainOne = 0
    simp [translation]
  translation_mul := translation_wedge

end KhanSL2
