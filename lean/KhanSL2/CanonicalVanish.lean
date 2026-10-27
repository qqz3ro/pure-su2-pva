module

public import KhanSL2.CanonicalTarget

@[expose] public section

/-! Two source relations vanish already as exterior polynomials. -/

noncomputable section
namespace KhanSL2.CanonicalVanish

theorem x_y : wedge xRepresentative yRepresentative = 0 := by
  simp [xRepresentative, yRepresentative, wedge, wedgeLinear,
    generator, Finsupp.linearCombination_single, Fin.sum_univ_succ,
    monomialWedge, inversionCount, Mode.code, ← Finset.insert_eq]

theorem y_translation_y : wedge yRepresentative (translation yRepresentative) = 0 := by
  simp only [yRepresentative, translation_wedge, translation_generator,
    translationGenerator]
  simp [wedge, wedgeLinear, generator, Finsupp.linearCombination_single,
    monomialWedge, inversionCount, Mode.code, Mode.next, Mode.order,
    ← Finset.insert_eq, Finset.filter_insert, Finset.filter_singleton]

theorem xClass_yClass : targetData.mul xClass yClass = 0 := by
  rw [xClass, yClass, target_mul_classOf]
  simp [x_y]

theorem yClass_translation_yClass :
    targetData.mul yClass (targetData.translation yClass) = 0 := by
  rw [yClass, target_translation_classOf, target_mul_classOf]
  simp [y_translation_y]

end KhanSL2.CanonicalVanish
