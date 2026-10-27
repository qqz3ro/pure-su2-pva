module

public import KhanSL2.SymmetricFamily.WordCounts
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Perm

@[expose] public section

/-! Normalized symmetrization identifies unordered degree-k monomials with
permutation-invariant labelled words. All normalization factors are explicit. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.SymmetricFamily

variable {α : Type*} [DecidableEq α]

abbrev DegreeExponent (α : Type*) (k : ℕ) := {d : α →₀ ℕ // d.degree = k}
abbrev WordSpace (α : Type*) (k : ℕ) := (Fin k → α) →₀ ℂ
abbrev ExponentSpace (α : Type*) (k : ℕ) := DegreeExponent α k →₀ ℂ

def exponentIndex {k : ℕ} (u : Fin k → α) : DegreeExponent α k :=
  ⟨wordExponent u, wordExponent_degree u⟩

@[simp] theorem exponentIndex_comp_perm {k : ℕ} (u : Fin k → α)
    (σ : Equiv.Perm (Fin k)) : exponentIndex (u ∘ σ) = exponentIndex u := by
  apply Subtype.ext
  exact wordExponent_comp_perm u σ

/-- Forget the ordering of a labelled word. -/
def unlabel (k : ℕ) : WordSpace α k →ₗ[ℂ] ExponentSpace α k :=
  Finsupp.lmapDomain ℂ ℂ exponentIndex

/-- Permute the labelled slots. -/
def wordPermute {k : ℕ} (σ : Equiv.Perm (Fin k)) : Module.End ℂ (WordSpace α k) :=
  Finsupp.lmapDomain ℂ ℂ (fun u => u ∘ σ)

omit [DecidableEq α] in
@[simp] theorem wordPermute_single {k : ℕ} (σ : Equiv.Perm (Fin k))
    (u : Fin k → α) (c : ℂ) :
    wordPermute σ (Finsupp.single u c) = Finsupp.single (u ∘ σ) c := by
  simp [wordPermute]

@[simp] theorem unlabel_single {k : ℕ} (u : Fin k → α) (c : ℂ) :
    unlabel k (Finsupp.single u c) = Finsupp.single (exponentIndex u) c := by
  simp [unlabel]

omit [DecidableEq α] in
theorem wordPermute_wordPermute {k : ℕ} (σ τ : Equiv.Perm (Fin k))
    (x : WordSpace α k) : wordPermute τ (wordPermute σ x) = wordPermute (σ * τ) x := by
  have h : (wordPermute τ).comp (wordPermute σ) = (wordPermute (σ * τ) :
      Module.End ℂ (WordSpace α k)) := by
    apply Finsupp.lhom_ext
    intro u c
    simp [Function.comp_def, Equiv.Perm.coe_mul]
  exact LinearMap.congr_fun h x

theorem unlabel_wordPermute {k : ℕ} (σ : Equiv.Perm (Fin k)) (x : WordSpace α k) :
    unlabel k (wordPermute σ x) = unlabel k x := by
  have h : (unlabel k).comp (wordPermute σ) = (unlabel k :
      WordSpace α k →ₗ[ℂ] ExponentSpace α k) := by
    apply Finsupp.lhom_ext
    intro u c
    simp
  exact LinearMap.congr_fun h x

/-- Invariant labelled words, using the actual permutation of slots. -/
def invariantWords (k : ℕ) : Submodule ℂ (WordSpace α k) where
  carrier := {x | ∀ σ : Equiv.Perm (Fin k), wordPermute σ x = x}
  zero_mem' := by simp
  add_mem' hx hy σ := by rw [map_add, hx σ, hy σ]
  smul_mem' c _ hx σ := by rw [map_smul, hx σ]

/-- Average over all k! slot permutations. -/
def wordAverage (k : ℕ) : Module.End ℂ (WordSpace α k) :=
  (Fintype.card (Equiv.Perm (Fin k)) : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin k), wordPermute σ

theorem permutationCard_ne_zero (k : ℕ) :
    (Fintype.card (Equiv.Perm (Fin k)) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

omit [DecidableEq α] in
/-- The average is fixed by all slot permutations. -/
theorem wordAverage_mem (k : ℕ) (x : WordSpace α k) : wordAverage k x ∈ invariantWords k := by
  intro τ
  simp only [wordAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    wordPermute_wordPermute]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ => wordPermute σ x)

omit [DecidableEq α] in
/-- The average acts identically on invariant tensors. -/
theorem wordAverage_eq_self {k : ℕ} {x : WordSpace α k} (hx : x ∈ invariantWords k) :
    wordAverage k x = x := by
  change ∀ σ, wordPermute σ x = x at hx
  simp only [wordAverage, LinearMap.smul_apply, LinearMap.sum_apply, hx,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (permutationCard_ne_zero k), one_smul]

/-- Forgetting labels is unchanged by averaging. -/
theorem unlabel_wordAverage (k : ℕ) (x : WordSpace α k) :
    unlabel k (wordAverage k x) = unlabel k x := by
  simp only [wordAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
    map_sum, unlabel_wordPermute, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (permutationCard_ne_zero k), one_smul]

omit [DecidableEq α] in
/-- Averaging is unchanged if the input slots are permuted first. -/
theorem wordAverage_wordPermute {k : ℕ} (τ : Equiv.Perm (Fin k)) (x : WordSpace α k) :
    wordAverage k (wordPermute τ x) = wordAverage k x := by
  simp only [wordAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    wordPermute_wordPermute]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => wordPermute σ x)

/-- Choose one labelled representative; averaging removes all dependence on the choice. -/
def representative {k : ℕ} (d : DegreeExponent α k) : Fin k → α :=
  (exists_word_of_degree d.val d.property).choose

@[simp] theorem representative_exponent {k : ℕ} (d : DegreeExponent α k) :
    exponentIndex (representative d) = d := by
  apply Subtype.ext
  exact (exists_word_of_degree d.val d.property).choose_spec

/-- Normalized symmetrization of unordered monomials. -/
def relabel (k : ℕ) : ExponentSpace α k →ₗ[ℂ] WordSpace α k :=
  Finsupp.linearCombination ℂ (fun d => wordAverage k (Finsupp.single (representative d) 1))

theorem unlabel_relabel (k : ℕ) (x : ExponentSpace α k) : unlabel k (relabel k x) = x := by
  have h : (unlabel k).comp (relabel k) = LinearMap.id (R := ℂ) (M := ExponentSpace α k) := by
    apply Finsupp.lhom_ext
    intro d c
    simp [relabel, unlabel_wordAverage, Finsupp.smul_single]
  exact LinearMap.congr_fun h x

theorem relabel_unlabel (k : ℕ) (x : WordSpace α k) : relabel k (unlabel k x) = wordAverage k x := by
  have h : (relabel k).comp (unlabel k) = (wordAverage k : Module.End ℂ (WordSpace α k)) := by
    apply Finsupp.lhom_ext
    intro u c
    have he : wordExponent (representative (exponentIndex u)) = wordExponent u :=
      congrArg Subtype.val (representative_exponent (exponentIndex u))
    obtain ⟨σ,hσ⟩ := exists_perm_of_wordExponent_eq he
    simp only [LinearMap.comp_apply, unlabel_single, relabel,
      Finsupp.linearCombination_single]
    rw [← hσ, ← wordPermute_single σ u 1, wordAverage_wordPermute,
      ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact LinearMap.congr_fun h x

theorem relabel_mem (k : ℕ) (x : ExponentSpace α k) : relabel k x ∈ invariantWords k := by
  have h := relabel_unlabel k (relabel k x)
  rw [unlabel_relabel] at h
  rw [h]
  exact wordAverage_mem k _

/-- Genuine normalized equivalence between symmetric monomials and invariant labelled words. -/
def exponentInvariantEquiv (k : ℕ) : ExponentSpace α k ≃ₗ[ℂ] invariantWords (α := α) k where
  toFun x := ⟨relabel k x, relabel_mem k x⟩
  invFun x := unlabel k x.val
  left_inv x := unlabel_relabel k x
  right_inv x := by
    apply Subtype.ext
    exact (relabel_unlabel k x.val).trans (wordAverage_eq_self x.property)
  map_add' x y := by apply Subtype.ext; exact map_add (relabel k) x y
  map_smul' c x := by apply Subtype.ext; exact map_smul (relabel k) c x

end KhanSL2.SymmetricFamily
