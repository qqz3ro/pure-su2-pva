module

public import KhanSL2.ExteriorParity

@[expose] public section

/-! Supercommutativity for homogeneous finite exterior cochains. -/

noncomputable section

namespace KhanSL2.FiniteExterior

variable {α : Type*} [DecidableEq α]

theorem wedge_sum_formula (code : α → ℕ) (u v : Exterior α) :
    wedge code u v =
      ∑ s ∈ u.support, ∑ t ∈ v.support,
        (u s * v t) • monomialWedge code s t := by
  simp [wedge, wedgeLinear, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, Finset.smul_sum, smul_smul]

theorem wedge_supercomm_of_card (code : α → ℕ) (hinj : Function.Injective code)
    (p q : ℕ) (u v : Exterior α)
    (hu : ∀s ∈ u.support, s.card = p)
    (hv : ∀t ∈ v.support, t.card = q) :
    wedge code u v = (-1 : ℂ) ^ (p * q) • wedge code v u := by
  rw [wedge_sum_formula, wedge_sum_formula]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro s hs
  rw [monomialWedge_supercomm code hinj s t, hu s hs, hv t ht]
  simp only [smul_smul]
  congr 1
  ac_rfl

omit [DecidableEq α] in
theorem parity_of_card (p : ℕ) (u : Exterior α)
    (hu : ∀s ∈ u.support, s.card = p) :
    parityLinear u = (-1 : ℂ) ^ p • u := by
  conv_rhs => rw [← Finsupp.sum_single u]
  simp only [parityLinear, Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hu s hs]
  simp [monomial, smul_smul, mul_comm]

theorem wedge_generator_supercomm (code : α → ℕ) (hinj : Function.Injective code)
    (a : α) (u : Exterior α) :
    wedge code (generator a) u =
      wedge code (parityLinear u) (generator a) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [wedge_add_right, map_add, wedge_add_left, hu, hv]
  | single s r =>
    simp only [generator, monomial, parity_single, wedge_smul_left, wedge_single,
      one_mul, mul_one]
    rw [monomialWedge_supercomm code hinj {a} s]
    simp [smul_smul, mul_comm]

theorem wedge_comm_of_parity_even (code : α → ℕ) (hinj : Function.Injective code)
    (v : Exterior α) (hv : parityLinear v = v) (u : Exterior α) :
    wedge code u v = wedge code v u := by
  induction u using induction_on code with
  | hzero => simp
  | hone => rw [wedge_one_left, wedge_one_right]
  | hadd u w hu hw => simp only [wedge_add_left, wedge_add_right, hu, hw]
  | hsmul r u hu => simp only [wedge_smul_left, wedge_smul_right, hu]
  | hgen a u hu =>
    rw [wedge_assoc, hu, ← wedge_assoc, wedge_generator_supercomm code hinj,
      hv, wedge_assoc]

theorem wedge_comm_of_parity_odd (code : α → ℕ) (hinj : Function.Injective code)
    (v : Exterior α) (hv : parityLinear v = -v) (u : Exterior α) :
    wedge code u v = wedge code v (parityLinear u) := by
  induction u using induction_on code with
  | hzero => simp
  | hone => simp only [parity_one, wedge_one_left, wedge_one_right]
  | hadd u w hu hw => simp only [wedge_add_left, map_add, wedge_add_right, hu, hw]
  | hsmul r u hu => simp only [wedge_smul_left, map_smul, wedge_smul_right, hu]
  | hgen a u hu =>
    rw [wedge_assoc, hu, ← wedge_assoc, wedge_generator_supercomm code hinj, hv,
      parity_generator_wedge]
    change (wedgeLinear code ((wedgeLinear code (-v)) (generator a))) (parityLinear u) =
      (wedgeLinear code v) (-wedge code (generator a) (parityLinear u))
    simp only [map_neg, LinearMap.neg_apply]
    congr 1
    exact wedge_assoc code v (generator a) (parityLinear u)

end KhanSL2.FiniteExterior
