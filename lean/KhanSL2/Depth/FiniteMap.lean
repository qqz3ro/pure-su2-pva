module

public import KhanSL2.Depth.Toolkit
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Regular.Category

@[expose] public section

/-!
# Depth along a ring map (blueprint `lem:depthfinite`, the direction used)

Let `R → S` be a ring map with `S` Noetherian, `M` a finite `S`-module and `I ⊆ R` an ideal.
If `depth_{IS} M ≥ n` over `S`, then `I` contains an `M`-weakly-regular sequence of length `n`
of elements of `R` (`exists_isWeaklyRegular_of_le_depth_map`). The proof is the usual one:
positive depth puts `IS` outside every associated prime of `M`, prime avoidance in `R` gives
`x ∈ I` outside all their contractions, `x` is then `M`-regular, and depth drops by at most one
in `M / xM`.

If moreover `R` is Noetherian and `M` is finite over `R`, Rees' theorem turns this into the
`Ext`-depth bound `depth_I M ≥ n` over `R` (`le_depth_of_le_depth_map`).
-/

noncomputable section

universe u

open CategoryTheory RingTheory.Sequence Pointwise

namespace KhanSL2.Depth

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- In `M / rM`, the `R`-submodule `x • M` and the `S`-submodule `(algebraMap x) • M` agree. -/
theorem smul_top_restrictScalars (M : Type u) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] (x : R) :
    ((algebraMap R S x) • (⊤ : Submodule S M)).restrictScalars R = x • (⊤ : Submodule R M) := by
  ext m
  rw [Submodule.restrictScalars_mem, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, algebraMap_smul]

/-- `M / xM` over `R` is `M / (algebraMap x) M` over `S`. -/
def quotSMulTopEquiv (M : Type u) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] (x : R) :
    QuotSMulTop x M ≃ₗ[R] QuotSMulTop (algebraMap R S x) M :=
  (Submodule.quotEquivOfEq _ _ (smul_top_restrictScalars M x).symm).trans
    (Submodule.Quotient.restrictScalarsEquiv R _)

variable [IsNoetherianRing S]

/-- Positive depth puts `IS` outside every associated prime. -/
theorem not_le_of_mem_associatedPrimes {M : Type u} [AddCommGroup M] [Module S M]
    {J : Ideal S} (h : 1 ≤ J.depth (ModuleCat.of S M)) {P : Ideal S}
    (hP : P ∈ associatedPrimes S M) : ¬ J ≤ P := by
  intro hJ
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hP
  obtain ⟨hprime, m, rfl⟩ := hP
  have hm : m = 0 := eq_zero_of_one_le_depth h (fun a ha => by
    have := hJ ha
    rwa [Submodule.mem_colon_singleton, Submodule.mem_bot] at this)
  apply hprime.ne_top
  rw [eq_top_iff]
  intro a _
  rw [Submodule.mem_colon_singleton, hm, smul_zero]
  exact Submodule.zero_mem _

/-- **Prime avoidance**: positive depth of `IS` gives an `M`-regular element of `I`. -/
theorem exists_isSMulRegular_of_one_le_depth (I : Ideal R) (M : Type u) [AddCommGroup M]
    [Module S M] [Module.Finite S M]
    (h : 1 ≤ (I.map (algebraMap R S)).depth (ModuleCat.of S M)) :
    ∃ x ∈ I, IsSMulRegular M (algebraMap R S x) := by
  have hfin := associatedPrimes.finite S M
  have hnot : ¬ ((I : Set R) ⊆ ⋃ P ∈ associatedPrimes S M, (P.comap (algebraMap R S) : Set R)) := by
    rw [Ideal.subset_union_prime_finite hfin ⊥ ⊥ (fun P hP _ _ => by
      have : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
      exact Ideal.comap_isPrime (algebraMap R S) P)]
    rintro ⟨P, hP, hle⟩
    exact not_le_of_mem_associatedPrimes h hP (Ideal.map_le_iff_le_comap.mpr hle)
  rw [Set.not_subset] at hnot
  obtain ⟨x, hxI, hx⟩ := hnot
  refine ⟨x, hxI, ?_⟩
  have hx' : algebraMap R S x ∉ ⋃ P ∈ associatedPrimes S M, (P : Set S) := by
    intro hmem
    apply hx
    rw [Set.mem_iUnion₂] at hmem ⊢
    obtain ⟨P, hP, hxP⟩ := hmem
    exact ⟨P, hP, hxP⟩
  rw [biUnion_associatedPrimes_eq_compl_regular S M, Set.mem_compl_iff, not_not] at hx'
  exact hx'

/-- **Depth along a ring map**: `depth_{IS} M ≥ n` over `S` gives an `M`-weakly-regular
sequence of length `n` in `I`. -/
theorem exists_isWeaklyRegular_of_le_depth_map (I : Ideal R) (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
      [Module.Finite S M],
      (n : ℕ∞) ≤ (I.map (algebraMap R S)).depth (ModuleCat.of S M) →
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsWeaklyRegular M rs := by
  induction n with
  | zero =>
    intro M _ _ _ _ _ _
    exact ⟨[], rfl, by simp, IsWeaklyRegular.nil R M⟩
  | succ n ih =>
    intro M _ _ _ _ _ hM
    obtain ⟨x, hxI, hreg⟩ := exists_isSMulRegular_of_one_le_depth I M
      (le_trans (by exact_mod_cast Nat.succ_pos n) hM)
    -- the depth of `M / xM`
    have hQ : (n : ℕ∞) ≤ (I.map (algebraMap R S)).depth
        (ModuleCat.of S (QuotSMulTop (algebraMap R S x) M)) := by
      refine le_trans ?_ (depth_right_ge _ (LinearMap.exact_lsmul_mkQ_smul_top M _) hreg
        (Submodule.mkQ_surjective _))
      refine le_inf (le_trans (by exact_mod_cast Nat.le_succ n) hM) ?_
      rw [show ((n : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) - 1 by simp]
      exact tsub_le_tsub_right hM 1
    obtain ⟨rs, hlen, hmem, hrs⟩ := ih (QuotSMulTop (algebraMap R S x) M) hQ
    refine ⟨x :: rs, by rw [List.length_cons, hlen], ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hxI
      · exact hmem r hr
    · rw [isWeaklyRegular_cons_iff]
      refine ⟨?_, ((quotSMulTopEquiv M x).isWeaklyRegular_congr rs).mpr hrs⟩
      intro a b hab
      apply hreg
      simp only [algebraMap_smul]
      exact hab

/-- **Depth along a finite map** (the inequality used): if `R` is Noetherian, `M` is finite over
`R` and `IM ≠ M`, then `depth_I M ≥ depth_{IS} M` (for natural-number bounds). -/
theorem le_depth_of_le_depth_map [IsNoetherianRing R] (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] [Module.Finite S M]
    [Module.Finite R M] (hlt : I • (⊤ : Submodule R M) < ⊤) (n : ℕ)
    (hn : (n : ℕ∞) ≤ (I.map (algebraMap R S)).depth (ModuleCat.of S M)) :
    (n : ℕ∞) ≤ I.depth (ModuleCat.of R M) := by
  obtain ⟨rs, hlen, hmem, hrs⟩ := exists_isWeaklyRegular_of_le_depth_map I n M hn
  have hreg : IsRegular M rs := by
    refine ⟨hrs, fun htop => ?_⟩
    have hle : Ideal.ofList rs • (⊤ : Submodule R M) ≤ I • ⊤ :=
      Submodule.smul_mono_left (Ideal.span_le.mpr fun r hr => hmem r hr)
    rw [← htop] at hle
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  rw [Ideal.depth_eq_sSup_length_isRegular I (ModuleCat.of R M) hlt, ← hlen]
  exact le_sSup ⟨rs, hreg, hmem, rfl⟩

end KhanSL2.Depth
