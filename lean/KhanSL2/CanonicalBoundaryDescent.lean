module

public import KhanSL2.CanonicalRelations
public import KhanSL2.CanonicalMixed
public import KhanSL2.CanonicalInvariants

@[expose] public section

/-! The invariant primitives prove the two remaining relations in cohomology. -/

noncomputable section
namespace KhanSL2.CanonicalRelations

theorem xClass_sq : targetData.mul xClass xClass = 0 := by
  rw [xClass, target_mul_classOf, classOf_eq_zero_iff]
  exact ⟨squarePrimitive, squarePrimitive_mem_invariants, q_squarePrimitive⟩

theorem xClass_translation_yClass :
    targetData.mul xClass (targetData.translation yClass) = 0 := by
  rw [xClass, yClass, target_translation_classOf, target_mul_classOf,
    classOf_eq_zero_iff]
  refine ⟨(1 / 4 : ℂ) • wedge contraction contraction,
    relativeInvariants.smul_mem _
      (invariant_wedge contraction_mem_invariants contraction_mem_invariants), ?_⟩
  rw [map_smul, q_contraction_square, smul_smul]
  norm_num

end KhanSL2.CanonicalRelations
