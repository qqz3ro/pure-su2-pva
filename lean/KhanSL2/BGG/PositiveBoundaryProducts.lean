module

public import KhanSL2.BGG.PositiveBoundary

@[expose] public section

/-! The boundary on exterior words of length three. -/
noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PositiveCE

/-- Two contractions of a length-three word, without distinctness assumptions. -/
theorem contract_contract_triple (m n p q r : Mode) :
    contract n (contract m ((FiniteExterior.generator p * FiniteExterior.generator q) *
      FiniteExterior.generator r)) =
    (if m = p then (if n = q then FiniteExterior.generator r else 0) -
      (if n = r then FiniteExterior.generator q else 0) else 0) -
    (if m = q then (if n = p then FiniteExterior.generator r else 0) -
      (if n = r then FiniteExterior.generator p else 0) else 0) +
    (if m = r then (if n = p then FiniteExterior.generator q else 0) -
      (if n = q then FiniteExterior.generator p else 0) else 0) := by
  rw [mul_assoc]
  have hc (u : Cochain) : contract m (FiniteExterior.generator p * u) =
      (if m=p then u else 0) - FiniteExterior.generator p * contract m u :=
    contraction_generator_wedge Mode.code Mode.code_injective m p u
  rw [hc, contract_pair, mul_sub, map_sub, map_sub]
  split_ifs <;> simp_all [contract_pair]

private theorem finiteBoundary_triple (S : Finset Mode) (p q r : Mode)
    (hp : p∈S) (hq : q∈S) (hr : r∈S) :
    finiteBoundary S ((FiniteExterior.generator p * FiniteExterior.generator q) *
      FiniteExterior.generator r) =
    boundary (FiniteExterior.generator p * FiniteExterior.generator q) * FiniteExterior.generator r -
    boundary (FiniteExterior.generator p * FiniteExterior.generator r) * FiniteExterior.generator q +
    boundary (FiniteExterior.generator q * FiniteExterior.generator r) * FiniteExterior.generator p := by
  rw [finiteBoundary_apply]
  simp_rw [contract_contract_triple]
  simp only [mul_add, mul_sub, mul_ite, mul_zero, smul_add, smul_sub, smul_ite, smul_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq', hp, hq, hr, ite_true]
  simp_rw [mergeMode_swap, epsilon_swap_right _ q.color p.color,
    epsilon_swap_right _ r.color p.color, epsilon_swap_right _ r.color q.color]
  simp only [boundary_pair, Finset.sum_mul, smul_mul_assoc, neg_smul, smul_sub,
    smul_add, Finset.sum_neg_distrib, neg_mul]
  module

/-- The actual CE boundary on three generators is the signed sum over bracket pairs. -/
theorem boundary_triple (p q r : Mode) :
    boundary ((FiniteExterior.generator p * FiniteExterior.generator q) *
      FiniteExterior.generator r) =
    boundary (FiniteExterior.generator p * FiniteExterior.generator q) * FiniteExterior.generator r -
    boundary (FiniteExterior.generator p * FiniteExterior.generator r) * FiniteExterior.generator q +
    boundary (FiniteExterior.generator q * FiniteExterior.generator r) * FiniteExterior.generator p := by
  let S : Finset Mode := {p,q,r}
  have hu : supportModes ((FiniteExterior.generator p * FiniteExterior.generator q) *
      FiniteExterior.generator r) ⊆ S := by
    have hg (m : Mode) (hm : m ∈ S) : FiniteExterior.generator m ∈ generatorsIn (S : Set Mode) :=
      generator_mem_generatorsIn _ _ hm
    have h := mul_mem_generatorsIn _ (mul_mem_generatorsIn _
      (hg p (by simp [S])) (hg q (by simp [S]))) (hg r (by simp [S]))
    intro m hm
    obtain ⟨s, hs, hms⟩ := Finset.mem_biUnion.mp hm
    exact h hs m hms
  rw [← finiteBoundary_eq S _ hu]
  exact finiteBoundary_triple S p q r (by simp [S]) (by simp [S]) (by simp [S])

end KhanSL2.BGG.PositiveCE
