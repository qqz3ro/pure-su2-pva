module

public import KhanSL2.BGG.PositiveBoundary

@[expose] public section

/-! Global coefficient adjointness follows from finite mode cutoffs. -/

noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior

namespace KhanSL2.BGG.PositiveCE

def modeOfPair : ℕ × Fin 3 ↪ Mode where
  toFun p := ⟨p.1, p.2⟩
  inj' _p _q h := Prod.ext (congrArg Mode.index h) (congrArg Mode.color h)

@[simp] theorem modeOfPair_apply (p : ℕ × Fin 3) : modeOfPair p = (⟨p.1, p.2⟩ : Mode) := rfl

/-- All three colors in positive physical modes at most `N`. -/
def modesBelow (N : ℕ) : Finset Mode :=
  ((Finset.range N).product Finset.univ).map modeOfPair

@[simp] theorem mem_modesBelow (N : ℕ) (m : Mode) : m ∈ modesBelow N ↔ m.index < N := by
  cases m
  simp [modesBelow]

theorem sum_modesBelow {V : Type*} [AddCommMonoid V] (N : ℕ) (f : Mode → V) :
    ∑ m ∈ modesBelow N, f m = ∑ i ∈ Finset.range N, ∑ a : Fin 3, f ⟨i, a⟩ := by
  rw [modesBelow, Finset.sum_map]
  change (∑ p ∈ (Finset.range N).product Finset.univ, f (⟨p.1, p.2⟩ : Mode)) = _
  exact Finset.sum_product _ _ _

/-- The finite rectangular sum over merged modes is the usual CE splitting sum. -/
theorem sum_merge_indices {V : Type*} [AddCommMonoid V] (N k : ℕ) (hk : k ≤ N)
    (f : ℕ → ℕ → V) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, if i + j + 1 = k then f i j else 0) =
      ∑ i ∈ Finset.range k, f i (k - 1 - i) := by
  calc
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, if i + j + 1 = k then f i j else 0) =
        ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range N, if i + j + 1 = k then f i j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro i _ hi
      have hik : k ≤ i := Nat.le_of_not_gt (by simpa using hi)
      apply Finset.sum_eq_zero
      intro j _
      simp only [if_neg (show i + j + 1 ≠ k by omega)]
    _ = ∑ i ∈ Finset.range k, f i (k - 1 - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have hmem : k - 1 - i ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single (k - 1 - i)]
      · rw [if_pos (by omega)]
      · intro j _ hji
        rw [if_neg (by omega)]
      · exact fun h => (h hmem).elim

/-- On any FiniteExterior.generator whose mode can split inside the cutoff, the finite transpose is the CE differential. -/
theorem finiteCoboundary_generator (N : ℕ) (k : Mode) (hk : k.index ≤ N) :
    finiteCoboundary (modesBelow N) (FiniteExterior.generator k) = d (FiniteExterior.generator k) := by
  cases k with
  | mk k z =>
    rw [finiteCoboundary_apply, d_generator]
    congr 1
    rw [sum_modesBelow]
    simp_rw [sum_modesBelow]
    have hsum :
        (∑ i ∈ Finset.range N, ∑ b : Fin 3,
          ∑ j ∈ Finset.range N, ∑ c : Fin 3, ∑ a : Fin 3,
            epsilon a b c •
              (FiniteExterior.generator (⟨i, b⟩ : Mode) *
                (FiniteExterior.generator (⟨j, c⟩ : Mode) *
                  contract (mergeMode ⟨i, b⟩ ⟨j, c⟩ a) (FiniteExterior.generator ⟨k, z⟩)))) =
          ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            if i + j + 1 = k then
              ∑ b : Fin 3, ∑ c : Fin 3,
                epsilon z b c • (FiniteExterior.generator (⟨i, b⟩ : Mode) * FiniteExterior.generator (⟨j, c⟩ : Mode))
            else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i + j + 1 = k
      · simp [contract_generator, mergeMode, hij, Mode.mk.injEq]
      · simp [contract_generator, mergeMode, hij, Mode.mk.injEq]
    rw [hsum, sum_merge_indices N k hk]

theorem finiteCoboundary_eq_d (N : ℕ) (u : Cochain)
    (hu : u ∈ generatorsIn {m : Mode | m.index ≤ N}) : finiteCoboundary (modesBelow N) u = d u := by
  have hmono (s : Finset Mode) (hs : ∀ m ∈ s, m.index ≤ N) :
      finiteCoboundary (modesBelow N) (monomial s) = d (monomial s) := by
    induction s using Finset.induction_on with
    | empty =>
      change finiteCoboundary (modesBelow N) 1 = d 1
      rw [finiteCoboundary_one, d_one]
    | @insert m s hm ih =>
      rw [monomial_insert Mode.code m s hm, map_smul, map_smul]
      congr 1
      change finiteCoboundary (modesBelow N) (FiniteExterior.generator m * monomial s) = d (FiniteExterior.generator m * monomial s)
      rw [finiteCoboundary_mul, d_mul, finiteCoboundary_generator N m (hs m (by simp)),
        ih (fun n hn => hs n (Finset.mem_insert_of_mem hn))]
  rw [eq_sum_support u]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hmono s (hu hs)]

/-- The genuine chain boundary and cochain differential are coefficient transposes. -/
theorem boundary_pairing (u v : Cochain) : coefficientPairing (boundary u) v = coefficientPairing u (d v) := by
  let S := supportModes u ∪ supportModes v
  let N := S.sup Mode.index + 1
  have hu : supportModes u ⊆ modesBelow N := by
    intro m hm
    rw [mem_modesBelow]
    have h := Finset.le_sup (f := Mode.index) (Finset.mem_union_left (supportModes v) hm)
    change m.index ≤ S.sup Mode.index at h
    change m.index < S.sup Mode.index + 1
    omega
  have hv : v ∈ generatorsIn {m : Mode | m.index ≤ N} := by
    intro s hs m hm
    have hms : m ∈ supportModes v := subset_supportModes hs hm
    have h := Finset.le_sup (f := Mode.index) (Finset.mem_union_right (supportModes u) hms)
    change m.index ≤ S.sup Mode.index at h
    change m.index ≤ S.sup Mode.index + 1
    omega
  rw [← finiteBoundary_eq (modesBelow N) u hu, finiteBoundary_pairing, finiteCoboundary_eq_d N v hv]

/-- The homology boundary squares to zero, proved by adjointness to the verified CE differential. -/
theorem boundary_square_zero (u : Cochain) : boundary (boundary u) = 0 := by
  apply coefficientPairing_left_nondegenerate
  intro v
  rw [boundary_pairing, boundary_pairing, d_square_zero, map_zero]

end KhanSL2.BGG.PositiveCE
