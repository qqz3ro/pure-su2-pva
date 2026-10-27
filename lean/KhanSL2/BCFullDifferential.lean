module

public import KhanSL2.BCFullEmbedding
public import KhanSL2.BCFullAlgebra
public import KhanSL2.CELeibniz

@[expose] public section

/-!
# The full CE differential after adjoining zero ghosts

On old generators the added terms are exactly the infinitesimal constant-color
action multiplied by the zero ghosts. The resulting identity is proved on every
finite cochain, not assumed.
-/

noncomputable section

namespace KhanSL2

def fullDifferentialGenerator : FullMode → FullCochain
  | .inl a =>
    -(1 / 2 : ℂ) • ∑ b : Fin 3, ∑ c : Fin 3,
      epsilon a b c • (ghost b * ghost c)
  | .inr m =>
    fullInclusion (qGenerator m) +
      ∑ a : Fin 3, ghost a * fullInclusion (colorGenerator a m)

def fullDifferential : Module.End ℂ FullCochain :=
  FiniteExterior.extendDerivation FullMode.code fullDifferentialGenerator

/-- The cubic Hamiltonian in the enlarged odd `bc` system. -/
def omegaHamiltonian : FullCochain :=
  -(1 / 2 : ℂ) • ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    epsilon a b c • (fullGenerator (.inr (.b 0 a)) * ghost b * ghost c)

@[simp] theorem fullParity_ghost (a : Fin 3) :
    fullParity (ghost a) = -ghost a := fullParity_generator (.inl a)

@[simp] theorem fullDifferential_one : fullDifferential fullOne = 0 := by
  simp [fullDifferential, fullOne, FiniteExterior.extendDerivation_monomial]

@[simp] theorem fullDifferential_generator (m : FullMode) :
    fullDifferential (fullGenerator m) = fullDifferentialGenerator m := by
  have h : ({m} : Finset FullMode).filter
      (fun a => FullMode.code a < FullMode.code m) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha
    simpa only [Finset.mem_singleton.mp ha] using Nat.lt_irrefl (FullMode.code m)
  simp only [fullGenerator, FiniteExterior.generator,
    fullDifferential, FiniteExterior.extendDerivation_monomial,
    Finset.sum_singleton, FiniteExterior.position, h, Finset.card_empty,
    pow_zero, one_smul, Finset.erase_singleton]
  exact FiniteExterior.wedge_one_right FullMode.code _

theorem fullDifferentialGenerator_parity (m : FullMode) :
    fullParity (fullDifferentialGenerator m) = fullDifferentialGenerator m := by
  cases m with
  | inl a =>
    simp only [fullDifferentialGenerator, map_smul, map_sum, map_mul,
      fullParity_ghost, neg_mul_neg]
  | inr m =>
    simp only [fullDifferentialGenerator, map_add, map_sum, map_mul,
      fullParity_ghost, ← fullInclusion_parity,
      qGenerator_parity, colorGenerator_parity, map_neg, neg_mul_neg]

theorem fullDifferential_mul (u v : FullCochain) :
    fullDifferential (u * v) =
      fullDifferential u * v + fullParity u * fullDifferential v := by
  apply FiniteExterior.extendDerivation_wedge_twist FullMode.code
    FullMode.code_injective fullDifferentialGenerator u v (fullParity u)
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_even FullMode.code FullMode.code_injective
    (fullDifferentialGenerator m) (fullDifferentialGenerator_parity m)
      (fullParity u)).symm

private theorem fullDifferential_inclusion_monomial (s : ExteriorMonomial) :
    fullDifferential (fullInclusion (FiniteExterior.monomial s)) =
      ∑ m ∈ s, ((-1 : ℂ) ^ position m s) •
        (fullDifferentialGenerator (.inr m) *
          fullInclusion (FiniteExterior.monomial (s.erase m))) := by
  rw [show fullInclusion (FiniteExterior.monomial s) =
      FiniteExterior.monomial (s.map modeInclusion) from
        FiniteExterior.reindex_monomial modeInclusion s]
  rw [fullDifferential, FiniteExterior.extendDerivation_monomial]
  simp only [Finset.sum_map, FiniteExterior.position_map Mode.code FullMode.code
    modeInclusion FullMode.code_inr_lt, Finset.map_erase,
    fullInclusion_apply, FiniteExterior.reindex_monomial]
  rfl

/-- The precise zero-ghost correction on every original finite cochain. -/
theorem fullDifferential_inclusion (u : Cochain) :
    fullDifferential (fullInclusion u) =
      fullInclusion (q u) +
        ∑ a : Fin 3, ghost a * fullInclusion (colorAction a u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
    simp only [map_add, hu, hv, mul_add, Finset.sum_add_distrib]
    abel
  | single s r =>
    have hr : Finsupp.single s r = r • FiniteExterior.monomial s := by
      simp [FiniteExterior.monomial]
    rw [hr]
    simp only [map_smul, mul_smul_comm, ← Finset.smul_sum, ← smul_add]
    congr 1
    rw [fullDifferential_inclusion_monomial]
    simp only [fullDifferentialGenerator, add_mul, Finset.sum_mul, smul_add,
      Finset.smul_sum, Finset.sum_add_distrib]
    have hq : fullInclusion (q (FiniteExterior.monomial s)) =
        ∑ m ∈ s, ((-1 : ℂ) ^ position m s) •
          (fullInclusion (qGenerator m) *
            fullInclusion (FiniteExterior.monomial (s.erase m))) := by
      simp only [q, extendDerivation, FiniteExterior.monomial,
        Finsupp.linearCombination_single, one_smul, map_sum, map_smul]
      simp only [← cochain_mul_eq_wedge, map_mul]
    have hc (a : Fin 3) :
        fullInclusion (colorAction a (FiniteExterior.monomial s)) =
          ∑ m ∈ s, ((-1 : ℂ) ^ position m s) •
            (fullInclusion (colorGenerator a m) *
              fullInclusion (FiniteExterior.monomial (s.erase m))) := by
      simp only [colorAction, extendDerivation, FiniteExterior.monomial,
        Finsupp.linearCombination_single, one_smul, map_sum, map_smul]
      simp only [← cochain_mul_eq_wedge, map_mul]
    rw [hq]
    simp only [hc, Finset.mul_sum, mul_smul_comm, mul_assoc]
    congr 1
    exact Finset.sum_comm

end KhanSL2
