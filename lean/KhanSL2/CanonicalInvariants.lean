module

public import KhanSL2.CanonicalPrimitives

@[expose] public section

/-! Invariance of the explicitly supplied primitives. -/

noncomputable section
namespace KhanSL2.CanonicalRelations

private theorem wedge_add_left (u v w : Cochain) :
    wedge (u + v) w = wedge u w + wedge v w := by simp [wedge]
private theorem wedge_add_right (u v w : Cochain) :
    wedge u (v + w) = wedge u v + wedge u w := by simp [wedge]
private theorem wedge_neg_left (u v : Cochain) :
    wedge (-u) v = -wedge u v := by simp [wedge]
private theorem wedge_neg_right (u v : Cochain) :
    wedge u (-v) = -wedge u v := by simp [wedge]

set_option maxHeartbeats 400000 in
theorem colorAction_contraction (a : Fin 3) :
    colorAction a contraction = 0 := by
  simp only [contraction, map_sum, colorAction_wedge, colorAction_generator,
    colorGenerator, Fin.sum_univ_succ, Mode.color, Mode.recolor]
  fin_cases a <;> norm_num [epsilon]
  all_goals simp only [colorAction_wedge, colorAction_generator, colorGenerator,
    Fin.sum_univ_succ, Mode.color, Mode.recolor]
  all_goals norm_num [epsilon]
  all_goals simp only [wedge_add_left, wedge_add_right, wedge_neg_left,
    wedge_neg_right, wedge_zero, zero_wedge, add_zero, zero_add]
  all_goals abel

set_option maxHeartbeats 400000 in
theorem colorAction_squarePrimitive (a : Fin 3) :
    colorAction a squarePrimitive = 0 := by
  simp only [squarePrimitive, map_sum, map_smul, colorAction_wedge,
    colorAction_generator, colorGenerator, Fin.sum_univ_succ, Mode.color, Mode.recolor]
  fin_cases a <;> norm_num [epsilon]
  all_goals simp only [colorAction_wedge, colorAction_generator, colorGenerator,
    Fin.sum_univ_succ, Mode.color, Mode.recolor]
  all_goals norm_num [epsilon]
  all_goals simp only [wedge_add_left, wedge_add_right, wedge_neg_left,
    wedge_neg_right, wedge_zero, zero_wedge, add_zero, zero_add]
  all_goals abel

theorem contraction_mem_invariants : contraction ∈ relativeInvariants :=
  (mem_relativeInvariants_iff _).mpr colorAction_contraction

theorem squarePrimitive_mem_invariants : squarePrimitive ∈ relativeInvariants :=
  (mem_relativeInvariants_iff _).mpr colorAction_squarePrimitive

end KhanSL2.CanonicalRelations
