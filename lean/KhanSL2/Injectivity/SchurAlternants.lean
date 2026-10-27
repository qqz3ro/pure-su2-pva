module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basis
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
public import Mathlib.Data.Fin.Rev

/-! # The Schur-basis step in the cycle-pairing argument -/

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity

open Finset MvPolynomial

variable (σ R : Type*) [Fintype σ] [CommRing R]

/-- The descending staircase alternant, using Tau Ceti's alphabet ordering. -/
def staircaseAlternant : MvPolynomial σ R :=
  rename (Fintype.equivFin σ).symm
    (TauCeti.alternant (Fin (Fintype.card σ)) R (fun j => Fintype.card σ - 1 - j))

/-- A partition alternant with the staircase already added to its exponents. -/
def partitionAlternant {d : ℕ} (μ : d.Partition) : MvPolynomial σ R :=
  rename (Fintype.equivFin σ).symm
    (TauCeti.alternant (Fin (Fintype.card σ)) R
      (fun j => (YoungDiagram.ofPartition μ).betaNumber (Fintype.card σ) j))

variable {σ R}

/-- Reversing the columns changes the descending staircase convention to the
ascending Vandermonde convention. The multiplier is the explicit permutation sign. -/
theorem descendingAlternant_eq_signed_vandermonde (n : ℕ) :
    TauCeti.alternant (Fin n) R (fun j => n - 1 - (j : ℕ)) =
      Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) •
        (∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i : MvPolynomial (Fin n) R)) := by
  rw [← TauCeti.alternant_fin_val_eq_vandermonde]
  simpa only [Function.comp_def, Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm]
    using TauCeti.alternant_comp_perm (R := R) Fin.revPerm (fun j : Fin n => (j : ℕ))

theorem schur_mul_staircase {d : ℕ} (μ : d.Partition)
    (hμ : μ.parts.card ≤ Fintype.card σ) :
    TauCeti.schurPoly σ R μ * staircaseAlternant σ R = partitionAlternant σ R μ := by
  exact TauCeti.schurPoly_mul_alternant μ (by simpa using hμ)

/-- A symmetric homogeneous polynomial has an explicit finite Schur expansion. -/
theorem symmetricHomogeneous_schur_expansion {d : ℕ}
    (p : TauCeti.symmetricHomogeneousSubmodule σ R d) :
    (p : MvPolynomial σ R) =
      ∑ μ : {ν : d.Partition // ν.parts.card ≤ Fintype.card σ},
        (TauCeti.schurPolyBasis σ R d).repr p μ • TauCeti.schurPoly σ R μ.1 := by
  classical
  have h := congrArg (fun q : TauCeti.symmetricHomogeneousSubmodule σ R d =>
    (q : MvPolynomial σ R)) ((TauCeti.schurPolyBasis σ R d).sum_repr p)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, TauCeti.coe_schurPolyBasis] using h.symm

/-- Multiplication by the Vandermonde turns the Schur expansion into a finite
linear combination of exactly the exponent determinants supplied by the cycles. -/
theorem symmetricHomogeneous_mul_staircase {d : ℕ}
    (p : TauCeti.symmetricHomogeneousSubmodule σ R d) :
    (p : MvPolynomial σ R) * staircaseAlternant σ R =
      ∑ μ : {ν : d.Partition // ν.parts.card ≤ Fintype.card σ},
        (TauCeti.schurPolyBasis σ R d).repr p μ • partitionAlternant σ R μ.1 := by
  classical
  rw [symmetricHomogeneous_schur_expansion p, sum_mul]
  apply sum_congr rfl
  intro μ _hμ
  rw [smul_mul_assoc, schur_mul_staircase μ.1 μ.2]

/-- The module spanned by all exponent alternants. -/
def exponentAlternantSpan : Submodule R (MvPolynomial σ R) :=
  Submodule.span R (Set.range fun e : Fin (Fintype.card σ) → ℕ =>
    rename (Fintype.equivFin σ).symm (TauCeti.alternant (Fin (Fintype.card σ)) R e))

theorem partitionAlternant_mem_span {d : ℕ} (μ : d.Partition) :
    partitionAlternant σ R μ ∈ exponentAlternantSpan (σ := σ) (R := R) :=
  Submodule.subset_span ⟨_, rfl⟩

theorem symmetricHomogeneous_mul_staircase_mem_span {d : ℕ}
    (p : TauCeti.symmetricHomogeneousSubmodule σ R d) :
    (p : MvPolynomial σ R) * staircaseAlternant σ R ∈
      exponentAlternantSpan (σ := σ) (R := R) := by
  classical
  rw [symmetricHomogeneous_mul_staircase p]
  exact Submodule.sum_mem _ fun μ _hμ =>
    Submodule.smul_mem _ _ (partitionAlternant_mem_span μ.1)

/-- The cycle determinants span the Vandermonde times every symmetric polynomial,
without a homogeneity assumption or any bound on its degree. -/
theorem symmetric_mul_staircase_mem_span (p : MvPolynomial σ R) (hp : p.IsSymmetric) :
    p * staircaseAlternant σ R ∈ exponentAlternantSpan (σ := σ) (R := R) := by
  classical
  rw [← sum_homogeneousComponent p, sum_mul]
  apply Submodule.sum_mem
  intro d _hd
  let pd : TauCeti.symmetricHomogeneousSubmodule σ R d :=
    ⟨homogeneousComponent d p, TauCeti.mem_symmetricHomogeneousSubmodule.mpr
      ⟨fun e => by rw [rename_homogeneousComponent, hp e],
        homogeneousComponent_isHomogeneous d p⟩⟩
  exact symmetricHomogeneous_mul_staircase_mem_span pd

/-- The same span in the explicitly ordered alphabet `Fin n`. -/
def orderedAlternantSpan (n : ℕ) (R : Type*) [CommRing R] :
    Submodule R (MvPolynomial (Fin n) R) :=
  Submodule.span R (Set.range (TauCeti.alternant (Fin n) R))

theorem rename_mem_orderedAlternantSpan (p : MvPolynomial σ R)
    (hp : p ∈ exponentAlternantSpan (σ := σ) (R := R)) :
    rename (Fintype.equivFin σ) p ∈ orderedAlternantSpan (Fintype.card σ) R := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨e, rfl⟩ := hp
    have he : rename (Fintype.equivFin σ)
        (rename (Fintype.equivFin σ).symm (TauCeti.alternant (Fin (Fintype.card σ)) R e)) =
        TauCeti.alternant (Fin (Fintype.card σ)) R e := by
      simp [rename_rename, Function.comp_def, show (fun x : Fin (Fintype.card σ) => x) = id from rfl,
        rename_id]
    rw [he]
    exact Submodule.subset_span ⟨e, rfl⟩
  | zero => simp
  | add p q _hp _hq hp hq =>
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  | smul r p _hp hp =>
    rw [map_smul]
    exact Submodule.smul_mem _ r hp

theorem symmetric_mul_descending_card_mem_orderedSpan :
    ∀ (p : MvPolynomial (Fin (Fintype.card σ)) R), p.IsSymmetric →
      p * TauCeti.alternant (Fin (Fintype.card σ)) R
        (fun j => Fintype.card σ - 1 - (j : ℕ)) ∈ orderedAlternantSpan (Fintype.card σ) R := by
  intro p hp
  have h := rename_mem_orderedAlternantSpan
    (rename (Fintype.equivFin σ).symm p * staircaseAlternant σ R)
    (symmetric_mul_staircase_mem_span _ (hp.rename (Fintype.equivFin σ).symm))
  simpa [staircaseAlternant, map_mul, rename_rename, Function.comp_def,
    show (fun x : Fin (Fintype.card σ) => x) = id from rfl, rename_id] using h

theorem symmetric_mul_descending_mem_orderedSpan (n : ℕ) :
    ∀ (p : MvPolynomial (Fin n) R), p.IsSymmetric →
      p * TauCeti.alternant (Fin n) R (fun j => n - 1 - (j : ℕ)) ∈
        orderedAlternantSpan n R := by
  let T (m : ℕ) := ∀ (p : MvPolynomial (Fin m) R), p.IsSymmetric →
    p * TauCeti.alternant (Fin m) R (fun j => m - 1 - (j : ℕ)) ∈ orderedAlternantSpan m R
  have h : T (Fintype.card (Fin n)) :=
    symmetric_mul_descending_card_mem_orderedSpan (σ := Fin n) (R := R)
  change T n
  simpa only [Fintype.card_fin] using h

/-- Exact spanning in the ascending Vandermonde convention used by the source
coefficient polynomial. The reversed-order sign is removed using its unit action. -/
theorem symmetric_mul_vandermonde_mem_orderedSpan (n : ℕ)
    (p : MvPolynomial (Fin n) R) (hp : p.IsSymmetric) :
    p * (∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i)) ∈ orderedAlternantSpan n R := by
  have h := symmetric_mul_descending_mem_orderedSpan n p hp
  rw [descendingAlternant_eq_signed_vandermonde, mul_smul_comm] at h
  exact ((orderedAlternantSpan n R).smul_mem_iff'
    (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)))).mp h

end KhanSL2.Injectivity
