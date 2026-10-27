module

public import KhanSL2.BGG.FreeCEEnergy
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace KhanSL2.BGG

private theorem finite_boundedLength (α : Type*) [Finite α] (d : ℕ) :
    {l : List α | l.length ≤ d}.Finite := by
  have hEq (k : ℕ) : {l : List α | l.length = k}.Finite :=
    inferInstanceAs (Finite (List.Vector α k))
  have hLt : {l : List α | l.length < d+1}.Finite := by
    convert (Finset.range (d+1)).finite_toSet.biUnion (fun k _ => hEq k) using 1
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe, Finset.mem_range]
    constructor
    · intro h; exact ⟨l.length, h, rfl⟩
    · rintro ⟨k, hk, he⟩; simpa only [he] using hk
  simpa only [Nat.lt_succ_iff] using hLt

/-- There are exactly three compact-color generators in each positive mode below N. -/
def boundedPositiveGenerator (N : ℕ) (i : Fin N × Fin 3) : PositiveEnveloping :=
  FreeCE.ueGenerator ⟨i.1, i.2⟩

/-- Words of bounded length in a finite set of actual positive-current generators. -/
def boundedPositiveWordSpace (N d : ℕ) : Submodule ℂ PositiveEnveloping :=
  Submodule.span ℂ (WordGrading.word (boundedPositiveGenerator N) ''
    {l : List (Fin N × Fin 3) | l.length ≤ d})

instance finiteDimensional_boundedPositiveWordSpace (N d : ℕ) :
    FiniteDimensional ℂ (boundedPositiveWordSpace N d) :=
  FiniteDimensional.span_of_finite ℂ ((finite_boundedLength (Fin N × Fin 3) d).image _)

theorem boundedPositiveWordSpace_mono (N : ℕ) {d e : ℕ} (h : d ≤ e) :
    boundedPositiveWordSpace N d ≤ boundedPositiveWordSpace N e := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro l hl
  exact hl.trans h

theorem boundedPositiveWord_mem (N : ℕ) (l : List (Fin N × Fin 3)) :
    WordGrading.word (boundedPositiveGenerator N) l ∈ boundedPositiveWordSpace N l.length :=
  Submodule.subset_span ⟨l, by change l.length ≤ l.length; exact le_rfl, rfl⟩

/-- Arbitrary coefficients in sl₂ expand in the genuine three-element compact-color basis. -/
theorem positiveUEGenerator_colorExpansion (n : ℕ) (x : G) :
    positiveUEGenerator (n, x) = ∑ a : Fin 3,
      FreeCE.colorBasis.repr x a • FreeCE.ueGenerator ⟨n, a⟩ := by
  change UniversalEnvelopingAlgebra.ι ℂ (positiveMode n x) = _
  conv_lhs => rw [← FreeCE.colorBasis.sum_repr x]
  simp only [map_sum, map_smul, FreeCE.colorBasis_apply]
  rfl

/-- A bounded-mode generator increases the finite spanning word length by one. -/
theorem generator_mul_mem_boundedPositiveWordSpace (N d n : ℕ) (x : G)
    (hn : n < N) {u : PositiveEnveloping} (hu : u ∈ boundedPositiveWordSpace N d) :
    positiveUEGenerator (n, x) * u ∈ boundedPositiveWordSpace N (d+1) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    rw [positiveUEGenerator_colorExpansion, Finset.sum_mul]
    apply Submodule.sum_mem
    intro a _
    rw [smul_mul_assoc]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(⟨n, hn⟩, a) :: l,
      by change l.length + 1 ≤ d+1; exact Nat.succ_le_succ hl, rfl⟩
  | zero => simp
  | add u v hu hv iu iv =>
    simpa only [mul_add] using (boundedPositiveWordSpace N (d+1)).add_mem iu iv
  | smul r u hu ih =>
    simpa only [mul_smul_comm] using (boundedPositiveWordSpace N (d+1)).smul_mem r ih

/-- Every word whose modes lie below N is in the corresponding finite word span. -/
theorem positiveWord_mem_boundedPositiveWordSpace (N : ℕ) (l : List (ℕ × G))
    (hl : ∀ i ∈ l, i.1 < N) :
    WordGrading.word positiveUEGenerator l ∈ boundedPositiveWordSpace N l.length := by
  induction l with
  | nil => exact Submodule.subset_span ⟨[], by change (0 : ℕ) ≤ 0; exact le_rfl, rfl⟩
  | cons i l ih =>
    rw [WordGrading.word_cons]
    exact generator_mul_mem_boundedPositiveWordSpace N l.length i.1 i.2
      (hl i List.mem_cons_self) (ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)))

/-- Positive modes bound the number of factors by the physical energy. -/
theorem positiveWord_length_le_degree (l : List (ℕ × G)) :
    (l.length : ℤ) ≤ WordGrading.degree positiveEnergy l := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, WordGrading.degree_cons,
      positiveEnergy]
    omega

/-- Each mode appearing in a word has index strictly below its total positive energy. -/
theorem positiveWord_index_lt_degree (l : List (ℕ × G)) (i : ℕ × G) (hi : i ∈ l) :
    (i.1 : ℤ) < WordGrading.degree positiveEnergy l := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [WordGrading.degree_cons]
    have hnonneg := WordGrading.degree_nonneg positiveEnergy
      (fun k => by dsimp [positiveEnergy]; omega) l
    rcases List.mem_cons.mp hi with rfl | hi
    · dsimp [positiveEnergy]
      omega
    · have h := ih hi
      dsimp [positiveEnergy]
      omega

/-- The genuine homogeneous enveloping piece is contained in a finite spanning space.
This argument uses actual word generation and does not assume PBW finiteness. -/
theorem positiveUEPiece_le_boundedPositiveWordSpace (n : ℤ) :
    positiveUEPiece n ≤ boundedPositiveWordSpace n.toNat n.toNat := by
  apply Submodule.span_le.mpr
  rintro u ⟨l, hl, rfl⟩
  have hlen := positiveWord_length_le_degree l
  rw [hl] at hlen
  have hbound : l.length ≤ n.toNat := by omega
  apply boundedPositiveWordSpace_mono _ hbound
  apply positiveWord_mem_boundedPositiveWordSpace
  intro i hi
  have h := positiveWord_index_lt_degree l i hi
  rw [hl] at h
  omega

/-- Every actual energy piece of the positive-current enveloping algebra is finite-dimensional. -/
instance finiteDimensional_positiveUEPiece (n : ℤ) : FiniteDimensional ℂ (positiveUEPiece n) :=
  FiniteDimensional.of_injective
    (Submodule.inclusion (positiveUEPiece_le_boundedPositiveWordSpace n))
    (Submodule.inclusion_injective _)

end KhanSL2.BGG
