module

public import KhanSL2.CanonicalInvariants

@[expose] public section

/-! The explicit invariant primitive of the square of the canonical even cocycle. -/

noncomputable section

namespace KhanSL2
namespace CanonicalRelations

private theorem parity_wedge (u v : Cochain) :
    cochainParity (wedge u v) = wedge (cochainParity u) (cochainParity v) :=
  map_mul cochainParity u v

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

private theorem insert_swap (a b : Mode) (s : Finset Mode) :
    insert a (insert b s) = insert b (insert a s) := by
  ext m
  simp [or_left_comm]

set_option maxHeartbeats 200000 in
theorem q_squarePrimitive :
    q squarePrimitive = wedge xRepresentative xRepresentative := by
  simp only [squarePrimitive, map_sum, map_smul, q_wedge, q_generator,
    qGenerator_b_zero, zero_wedge, wedge_zero, add_zero, zero_add,
    parity_wedge, cochainParity_generator]
  simp only [Fin.sum_univ_three]
  simp [epsilon]
  simp only [qGenerator, Finset.sum_range_one, Fin.sum_univ_three]
  simp [epsilon]
  simp only [xRepresentative, Fin.sum_univ_three, wedge_add_left, wedge_add_right,
    wedge_neg_left, wedge_neg_right, wedge_smul_left, wedge_smul_right]
  simp [generator, monomialWedge, inversionCount, Mode.code,
    ← Finset.insert_eq, Finset.filter_insert, Finset.filter_singleton]
  simp only [wedge_neg_left, wedge_neg_right, wedge_smul_left, wedge_smul_right]
  simp [monomialWedge, inversionCount, Mode.code,
    ← Finset.insert_eq, Finset.filter_insert, Finset.filter_singleton]
  simp only [insert_swap, Finset.pair_comm]
  norm_num1
  have h01 : ({Mode.b 0 0, Mode.c 0 0, Mode.c 0 1, Mode.b 0 1} : Finset Mode) =
      {Mode.b 0 0, Mode.b 0 1, Mode.c 0 0, Mode.c 0 1} := by decide
  have h02 : ({Mode.b 0 0, Mode.c 0 0, Mode.c 0 2, Mode.b 0 2} : Finset Mode) =
      {Mode.b 0 0, Mode.b 0 2, Mode.c 0 0, Mode.c 0 2} := by decide
  have h10 : ({Mode.b 0 1, Mode.c 0 0, Mode.c 0 1, Mode.b 0 0} : Finset Mode) =
      {Mode.b 0 0, Mode.b 0 1, Mode.c 0 0, Mode.c 0 1} := by decide
  have h12 : ({Mode.b 0 1, Mode.c 0 1, Mode.c 0 2, Mode.b 0 2} : Finset Mode) =
      {Mode.b 0 1, Mode.b 0 2, Mode.c 0 1, Mode.c 0 2} := by decide
  have h20 : ({Mode.b 0 2, Mode.c 0 0, Mode.c 0 2, Mode.b 0 0} : Finset Mode) =
      {Mode.b 0 0, Mode.b 0 2, Mode.c 0 0, Mode.c 0 2} := by decide
  have h21 : ({Mode.b 0 2, Mode.c 0 1, Mode.c 0 2, Mode.b 0 1} : Finset Mode) =
      {Mode.b 0 1, Mode.b 0 2, Mode.c 0 1, Mode.c 0 2} := by decide
  have hr01 : ({Mode.b 0 0, Mode.b 0 1, Mode.c 0 1, Mode.c 0 0} : Finset Mode) =
      {Mode.b 0 0, Mode.b 0 1, Mode.c 0 0, Mode.c 0 1} := by decide
  have hr02 : ({Mode.b 0 0, Mode.b 0 2, Mode.c 0 2, Mode.c 0 0} : Finset Mode) =
      {Mode.b 0 0, Mode.b 0 2, Mode.c 0 0, Mode.c 0 2} := by decide
  have hr12 : ({Mode.b 0 1, Mode.b 0 2, Mode.c 0 2, Mode.c 0 1} : Finset Mode) =
      {Mode.b 0 1, Mode.b 0 2, Mode.c 0 1, Mode.c 0 2} := by decide
  simp only [h01, h02, h10, h12, h20, h21, hr01, hr02, hr12]
  ext1 s
  simp only [Finsupp.add_apply, Finsupp.neg_apply, Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs <;> ring

end CanonicalRelations
end KhanSL2

