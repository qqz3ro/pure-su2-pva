module

public import KhanSL2.CanonicalPrimitives

@[expose] public section

/-! An explicit invariant boundary for the mixed translated source relation. -/

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
private theorem wedge_smul_left (r : ℂ) (u v : Cochain) :
    wedge (r • u) v = r • wedge u v := by simp [wedge]
private theorem wedge_smul_right (r : ℂ) (u v : Cochain) :
    wedge u (r • v) = r • wedge u v := by simp [wedge]

private theorem contraction_parity : cochainParity contraction = contraction := by
  simp only [contraction, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  change cochainParity (generator (.b 0 a) * generator (.b 1 a)) = _
  simp only [map_mul, cochainParity_generator, neg_mul_neg]
  rfl

private theorem insert_swap (a b : Mode) (s : Finset Mode) :
    insert a (insert b s) = insert b (insert a s) := by
  ext m
  simp [or_left_comm]

set_option maxHeartbeats 500000 in
set_option maxRecDepth 1000 in
theorem q_contraction_square : q (wedge contraction contraction) =
    (4 : ℂ) • wedge xRepresentative (translation yRepresentative) := by
  rw [q_wedge, contraction_parity]
  simp only [contraction, map_sum, q_wedge, q_generator,
    qGenerator_b_zero, zero_wedge, zero_add, cochainParity_generator]
  simp only [Fin.sum_univ_three]
  simp only [qGenerator, Finset.sum_range_one, Fin.sum_univ_three]
  simp [epsilon]
  simp only [xRepresentative, yRepresentative, translation_wedge,
    translation_generator, translationGenerator, Mode.translationCoefficient,
    Mode.next, Fin.sum_univ_three]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_smul]
  simp only [wedge_add_left, wedge_add_right, wedge_neg_left, wedge_neg_right,
    wedge_smul_left, wedge_smul_right]
  simp [generator, monomialWedge, inversionCount, Mode.code,
    ← Finset.insert_eq, Finset.filter_insert, Finset.filter_singleton,
    wedge_neg_left, wedge_neg_right, wedge_smul_left, wedge_smul_right]
  try simp only [insert_swap, Finset.pair_comm]
  have h0 : ({Mode.b 0 0, Mode.b 0 1, Mode.b 1 0, Mode.c 0 0, Mode.b 0 2} : Finset Mode) =
      {Mode.b 0 0, Mode.b 0 1, Mode.b 0 2, Mode.c 0 0, Mode.b 1 0} := by decide
  have h1 : ({Mode.b 0 0, Mode.b 0 1, Mode.b 1 1, Mode.c 0 1, Mode.b 0 2} : Finset Mode) =
      {Mode.b 0 0, Mode.b 0 1, Mode.b 0 2, Mode.c 0 1, Mode.b 1 1} := by decide
  try simp only [h0, h1]
  ext1 s
  simp only [Finsupp.add_apply, Finsupp.neg_apply, Finsupp.smul_apply,
    Finsupp.single_apply]
  split_ifs <;> ring

end KhanSL2.CanonicalRelations
