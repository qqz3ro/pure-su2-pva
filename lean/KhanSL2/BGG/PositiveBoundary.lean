module

public import KhanSL2.BGG.PositiveCE
public import KhanSL2.Injectivity.FiniteSupport
public import KhanSL2.ExteriorDerivation

@[expose] public section

/-!
# The homology boundary of positive currents

The boundary merges two occupied positive modes using the compact epsilon
structure constants. Every defining sum is finite. Its normalization is the
coefficient transpose of the cochain differential, including the minus sign.
-/

noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior

namespace KhanSL2.BGG.PositiveCE

/-- The positive mode produced by bracketing two current modes. -/
def mergeMode (m n : Mode) (a : Fin 3) : Mode := ⟨m.index + n.index + 1, a⟩

@[simp] theorem mergeMode_swap (m n : Mode) (a : Fin 3) : mergeMode n m a = mergeMode m n a := by
  simp [mergeMode, Nat.add_comm]

abbrev contract (m : Mode) : Module.End ℂ Cochain := contraction Mode.code m

@[simp] theorem contract_one (m : Mode) : contract m 1 = 0 := by
  change contraction Mode.code m (monomial ∅) = 0
  simp

@[simp] theorem contract_generator (m n : Mode) :
    contract m (FiniteExterior.generator n) = if m = n then 1 else 0 := by
  by_cases h : m = n
  · subst n
    change contraction Mode.code m (monomial {m}) = _
    have hp : FiniteExterior.position Mode.code m {m} = 0 :=
      (position_insert_self Mode.code m ∅).trans (by simp [FiniteExterior.position])
    simp only [contraction_monomial, Finset.mem_singleton, ite_true,
      hp, pow_zero, one_smul, Finset.erase_singleton]
    rfl
  · change contraction Mode.code m (monomial {n}) = _
    simp [h]

/-- One finite summand of the bracket boundary. -/
def boundaryTerm (m n : Mode) (a : Fin 3) : Module.End ℂ Cochain :=
  (FiniteExterior.wedgeLinear Mode.code (FiniteExterior.generator (mergeMode m n a))).comp
    ((contract n).comp (contract m))

@[simp] theorem boundaryTerm_apply (m n : Mode) (a : Fin 3) (u : Cochain) :
    boundaryTerm m n a u = FiniteExterior.generator (mergeMode m n a) * contract n (contract m u) := rfl

/-- Restrict the two contracted inputs to a finite set of modes. -/
def finiteBoundary (S : Finset Mode) : Module.End ℂ Cochain :=
  (-(1 / 2 : ℂ)) • ∑ m ∈ S, ∑ n ∈ S, ∑ a : Fin 3,
    epsilon a m.color n.color • boundaryTerm m n a

@[simp] theorem finiteBoundary_apply (S : Finset Mode) (u : Cochain) :
    finiteBoundary S u = (-(1 / 2 : ℂ)) •
      ∑ m ∈ S, ∑ n ∈ S, ∑ a : Fin 3,
        epsilon a m.color n.color •
          (FiniteExterior.generator (mergeMode m n a) * contract n (contract m u)) := by
  simp only [finiteBoundary, LinearMap.smul_apply, LinearMap.sum_apply, boundaryTerm_apply]

/-- The actual homology boundary, defined on the finite exterior-monomial basis. -/
def boundary : Module.End ℂ Cochain :=
  Finsupp.linearCombination ℂ fun s => finiteBoundary s (monomial s)

@[simp] theorem boundary_monomial (s : Finset Mode) :
    boundary (monomial s) = finiteBoundary s (monomial s) := by
  simp [boundary, monomial]

@[simp] theorem boundary_one : boundary 1 = 0 := by
  change boundary (monomial ∅) = 0
  simp

@[simp] theorem boundary_generator (m : Mode) : boundary (FiniteExterior.generator m) = 0 := by
  change boundary (monomial {m}) = 0
  rw [boundary_monomial]
  change finiteBoundary {m} (FiniteExterior.generator m) = 0
  simp

private theorem contract_contract_monomial_eq_zero (m n : Mode) (s : Finset Mode)
    (hn : n ∉ s) : contract n (contract m (monomial s)) = 0 := by
  by_cases hm : m ∈ s
  · have hne : n ∉ s.erase m := fun h => hn (Finset.mem_of_mem_erase h)
    simp only [contract, contraction_monomial, if_pos hm, map_smul, if_neg hne, smul_zero]
  · simp [contract, contraction_monomial, hm]

/-- Enlarging the finite set of contracted modes does not change its action on a basis monomial. -/
theorem finiteBoundary_monomial (S s : Finset Mode) (hs : s ⊆ S) :
    finiteBoundary S (monomial s) = boundary (monomial s) := by
  rw [boundary_monomial, finiteBoundary_apply, finiteBoundary_apply]
  congr 1
  let F (m n : Mode) : Cochain := ∑ a : Fin 3,
    epsilon a m.color n.color •
      (FiniteExterior.generator (mergeMode m n a) * contract n (contract m (monomial s)))
  change (∑ m ∈ S, ∑ n ∈ S, F m n) = ∑ m ∈ s, ∑ n ∈ s, F m n
  calc
    (∑ m ∈ S, ∑ n ∈ S, F m n) = ∑ m ∈ s, ∑ n ∈ S, F m n := by
      symm
      apply Finset.sum_subset hs
      intro m _ hms
      simp [F, contract, contraction_monomial, hms]
    _ = ∑ m ∈ s, ∑ n ∈ s, F m n := by
      apply Finset.sum_congr rfl
      intro m _
      symm
      apply Finset.sum_subset hs
      intro n _ hns
      dsimp only [F]
      simp only [contract_contract_monomial_eq_zero m n s hns, mul_zero,
        smul_zero, Finset.sum_const_zero]

/-- The finite formula computes the boundary whenever its mode set contains the input support. -/
theorem finiteBoundary_eq (S : Finset Mode) (u : Cochain)
    (hu : supportModes u ⊆ S) : finiteBoundary S u = boundary u := by
  rw [eq_sum_support u]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [finiteBoundary_monomial S s ((subset_supportModes hs).trans hu)]

/-- A single contraction of a two-FiniteExterior.generator exterior word. -/
theorem contract_pair (p m n : Mode) :
    contract p (FiniteExterior.generator m * FiniteExterior.generator n) =
      (if p = m then FiniteExterior.generator n else 0) - (if p = n then FiniteExterior.generator m else 0) := by
  change contraction Mode.code p (FiniteExterior.wedge Mode.code (FiniteExterior.generator m) (FiniteExterior.generator n)) = _
  rw [contraction_generator_wedge Mode.code Mode.code_injective, contract_generator]
  change (if p = m then FiniteExterior.generator n else 0) -
      FiniteExterior.generator m * (if p = n then 1 else 0) = _
  split_ifs <;> simp_all

private theorem supportModes_subset_of_generatorsIn (S : Finset Mode) (u : Cochain)
    (hu : u ∈ generatorsIn (S : Set Mode)) : supportModes u ⊆ S := by
  intro m hm
  obtain ⟨s, hs, hms⟩ := Finset.mem_biUnion.mp hm
  exact hu hs m hms

/-- On two generators, the boundary is minus the current bracket in compact color coordinates. -/
theorem boundary_pair (m n : Mode) :
    boundary (FiniteExterior.generator m * FiniteExterior.generator n) =
      - ∑ a : Fin 3, epsilon a m.color n.color • FiniteExterior.generator (mergeMode m n a) := by
  by_cases h : m = n
  · subst n
    have hz : FiniteExterior.generator m * FiniteExterior.generator m = (0 : Cochain) :=
      wedge_generator_monomial_of_mem Mode.code m {m} (by simp)
    rw [hz, map_zero]
    simp
  · have hu : supportModes (FiniteExterior.generator m * FiniteExterior.generator n) ⊆ ({m, n} : Finset Mode) := by
      apply supportModes_subset_of_generatorsIn
      apply mul_mem_generatorsIn
      · exact generator_mem_generatorsIn _ _ (by simp)
      · exact generator_mem_generatorsIn _ _ (by simp)
    rw [← finiteBoundary_eq {m, n} _ hu, finiteBoundary_apply]
    simp only [Finset.sum_insert, Finset.mem_singleton, h, not_false_eq_true,
      Finset.sum_singleton, contract_pair, contract_generator, ite_true,
      if_neg h, if_neg (Ne.symm h), ite_false, neg_zero, map_sub, epsilon_self_right,
      sub_zero, zero_sub, map_zero, map_neg,
      sub_self, mul_zero, smul_zero, Finset.sum_const_zero, zero_add,
      mul_one, mul_neg_one, add_zero]
    have hswap :
        (∑ a : Fin 3, epsilon a n.color m.color • (-FiniteExterior.generator (mergeMode n m a))) =
          ∑ a : Fin 3, epsilon a m.color n.color • FiniteExterior.generator (mergeMode m n a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [epsilon_swap_right a n.color m.color, mergeMode_swap]
      simp
    rw [hswap, ← two_smul ℂ _, smul_smul]
    norm_num

/-- The coefficient transpose of one finite boundary summand. -/
def coboundaryTerm (m n : Mode) (a : Fin 3) : Module.End ℂ Cochain :=
  (FiniteExterior.wedgeLinear Mode.code (FiniteExterior.generator m)).comp
    ((FiniteExterior.wedgeLinear Mode.code (FiniteExterior.generator n)).comp (contract (mergeMode m n a)))

@[simp] theorem coboundaryTerm_apply (m n : Mode) (a : Fin 3) (u : Cochain) :
    coboundaryTerm m n a u = FiniteExterior.generator m * (FiniteExterior.generator n * contract (mergeMode m n a) u) := rfl

/-- Multiplication and contraction transpose term by term, with their order reversed. -/
theorem boundaryTerm_pairing (m n : Mode) (a : Fin 3) (u v : Cochain) :
    coefficientPairing (boundaryTerm m n a u) v =
      coefficientPairing u (coboundaryTerm m n a v) := by
  rw [boundaryTerm_apply, coboundaryTerm_apply]
  calc
    coefficientPairing
        (FiniteExterior.generator (mergeMode m n a) * contract n (contract m u)) v =
        coefficientPairing (contract n (contract m u)) (contract (mergeMode m n a) v) :=
      coefficientPairing_generator_mul (α := Mode) _ _ _
    _ = coefficientPairing (contract m u)
        (FiniteExterior.generator n * contract (mergeMode m n a) v) :=
      coefficientPairing_contraction (α := Mode) _ _ _
    _ = coefficientPairing u
        (FiniteExterior.generator m * (FiniteExterior.generator n * contract (mergeMode m n a) v)) :=
      coefficientPairing_contraction (α := Mode) _ _ _

/-- A finite sum of the transposed cochain summands. -/
def finiteCoboundary (S : Finset Mode) : Module.End ℂ Cochain :=
  (-(1 / 2 : ℂ)) • ∑ m ∈ S, ∑ n ∈ S, ∑ a : Fin 3,
    epsilon a m.color n.color • coboundaryTerm m n a

@[simp] theorem finiteCoboundary_apply (S : Finset Mode) (u : Cochain) :
    finiteCoboundary S u = (-(1 / 2 : ℂ)) •
      ∑ m ∈ S, ∑ n ∈ S, ∑ a : Fin 3,
        epsilon a m.color n.color •
          (FiniteExterior.generator m * (FiniteExterior.generator n * contract (mergeMode m n a) u)) := by
  simp only [finiteCoboundary, LinearMap.smul_apply, LinearMap.sum_apply, coboundaryTerm_apply]

/-- Exact finite coefficient-pairing adjointness, without infinite sums or support assumptions. -/
theorem finiteBoundary_pairing (S : Finset Mode) (u v : Cochain) :
    coefficientPairing (finiteBoundary S u) v = coefficientPairing u (finiteCoboundary S v) := by
  simp only [finiteBoundary, finiteCoboundary, LinearMap.smul_apply, LinearMap.sum_apply,
    map_sum, map_smul, boundaryTerm_pairing]

/-- Pairing against all finite exterior cochains detects a chain uniquely. -/
theorem coefficientPairing_left_nondegenerate (u : Cochain)
    (hu : ∀ v, coefficientPairing u v = 0) : u = 0 := by
  ext s
  simpa using hu (monomial s)

/-- Each cochain summand is an odd derivation: its coefficient is an even quadratic word. -/
theorem coboundaryTerm_mul (m n : Mode) (a : Fin 3) (u v : Cochain) :
    coboundaryTerm m n a (u * v) =
      coboundaryTerm m n a u * v + parityLinear u * coboundaryTerm m n a v := by
  have heven : parityLinear (FiniteExterior.generator m * FiniteExterior.generator n) = FiniteExterior.generator m * FiniteExterior.generator n := by
    change parity (FiniteExterior.generator m * FiniteExterior.generator n) = FiniteExterior.generator m * FiniteExterior.generator n
    rw [map_mul]
    simp only [parity_apply, parity_generator, neg_mul_neg]
  have hcomm : (FiniteExterior.generator m * FiniteExterior.generator n) * parityLinear u =
      parityLinear u * (FiniteExterior.generator m * FiniteExterior.generator n) :=
    (wedge_comm_of_parity_even Mode.code Mode.code_injective _ heven (parityLinear u)).symm
  have hc : contract (mergeMode m n a) (u * v) =
      contract (mergeMode m n a) u * v + parityLinear u * contract (mergeMode m n a) v :=
    contraction_wedge Mode.code Mode.code_injective _ u v
  simp only [coboundaryTerm_apply]
  rw [hc, mul_add, mul_add]
  apply congrArg₂ (· + ·)
  · simp only [mul_assoc]
  · calc
      FiniteExterior.generator m * (FiniteExterior.generator n * (parityLinear u * contract (mergeMode m n a) v)) =
          ((FiniteExterior.generator m * FiniteExterior.generator n) * parityLinear u) * contract (mergeMode m n a) v := by
            simp only [mul_assoc]
      _ = (parityLinear u * (FiniteExterior.generator m * FiniteExterior.generator n)) * contract (mergeMode m n a) v := by
        rw [hcomm]
      _ = parityLinear u * (FiniteExterior.generator m * (FiniteExterior.generator n * contract (mergeMode m n a) v)) := by
        simp only [mul_assoc]

@[simp] theorem finiteCoboundary_one (S : Finset Mode) : finiteCoboundary S 1 = 0 := by
  simp

/-- The finite transpose formula is an odd cochain derivation. -/
theorem finiteCoboundary_mul (S : Finset Mode) (u v : Cochain) :
    finiteCoboundary S (u * v) = finiteCoboundary S u * v + parityLinear u * finiteCoboundary S v := by
  simp only [finiteCoboundary, LinearMap.smul_apply, LinearMap.sum_apply, coboundaryTerm_mul,
    smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum]

end KhanSL2.BGG.PositiveCE
