module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

/-! Labelled words and their unordered multiplicities. Equal multiplicities
are exactly permutation orbits, including repeated letters and length zero. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.SymmetricFamily

variable {α : Type*} [DecidableEq α]

/-- The exponent multiplicities of a word in labelled slots. -/
def wordExponent {k : ℕ} (u : Fin k → α) : α →₀ ℕ :=
  (Finset.univ.val.map u).toFinsupp

@[simp] theorem wordExponent_degree {k : ℕ} (u : Fin k → α) :
    (wordExponent u).degree = k := by
  change (Finset.univ.val.map u).toFinsupp.sum (fun _ => id) = k
  rw [Multiset.toFinsupp_sum_eq, Multiset.card_map]
  simp

/-- Each multiplicity counts the corresponding finite fibre. -/
theorem wordExponent_apply {k : ℕ} (u : Fin k → α) (a : α) :
    wordExponent u a = Fintype.card {i : Fin k // u i = a} := by
  simp only [wordExponent, Multiset.toFinsupp_apply, Multiset.count_map,
    Fintype.card_subtype]
  exact congrArg Multiset.card (by
    change Finset.univ.val.filter (fun i => a = u i) =
      (Finset.univ.filter (fun i => u i = a)).val
    simp only [Finset.filter_val]
    congr 1
    funext i
    exact propext eq_comm)

/-- Multiplicity is the sum of the labelled single-letter exponents. -/
theorem wordExponent_eq_sum_single {k : ℕ} (u : Fin k → α) :
    wordExponent u = ∑ i : Fin k, Finsupp.single (u i) 1 := by
  ext a
  rw [wordExponent_apply, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_apply',
    Finsupp.single_apply]

/-- Relabelling slots leaves the exponent unchanged. -/
@[simp] theorem wordExponent_comp_perm {k : ℕ} (u : Fin k → α)
    (σ : Equiv.Perm (Fin k)) : wordExponent (u ∘ σ) = wordExponent u := by
  unfold wordExponent
  congr 1
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- Equal multiplicities admit a permutation matching the individual slots. -/
theorem exists_perm_of_wordExponent_eq {k : ℕ} {u v : Fin k → α}
    (h : wordExponent u = wordExponent v) :
    ∃ σ : Equiv.Perm (Fin k), v ∘ σ = u := by
  let e (a : α) : {i : Fin k // u i = a} ≃ {i : Fin k // v i = a} :=
    Fintype.equivOfCardEq (by
      rw [← wordExponent_apply, ← wordExponent_apply, h])
  exact ⟨Equiv.ofFiberEquiv e, funext (Equiv.ofFiberEquiv_map e)⟩

/-- Every exponent of degree k has a labelled word of length k. -/
theorem exists_word_of_degree {k : ℕ} (d : α →₀ ℕ) (hd : d.degree = k) :
    ∃ u : Fin k → α, wordExponent u = d := by
  have hex : ∃ (n : ℕ) (u : Fin n → α), wordExponent u = d := by
    let l := d.toMultiset.toList
    refine ⟨l.length, l.get, ?_⟩
    simp only [wordExponent, Fin.univ_val_map, List.ofFn_get, l,
      Multiset.coe_toList, Finsupp.toMultiset_toFinsupp]
  obtain ⟨n,u,hu⟩ := hex
  have hn : n = k := (wordExponent_degree u).symm.trans ((congrArg Finsupp.degree hu).trans hd)
  subst n
  exact ⟨u,hu⟩

/-- Multiplicity equality is precisely the finite symmetric-group orbit relation. -/
theorem wordExponent_eq_iff {k : ℕ} (u v : Fin k → α) :
    wordExponent u = wordExponent v ↔ ∃ σ : Equiv.Perm (Fin k), v ∘ σ = u := by
  constructor
  · exact exists_perm_of_wordExponent_eq
  · rintro ⟨σ,rfl⟩
    exact wordExponent_comp_perm v σ

end KhanSL2.SymmetricFamily
