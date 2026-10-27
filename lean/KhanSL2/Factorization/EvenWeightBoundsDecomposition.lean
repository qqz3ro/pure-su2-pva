module

public import KhanSL2.Factorization.EvenWeightBounds
public import KhanSL2.BGG.Terms
public import KhanSL2.BGG.FiniteSl2Splitting
public import TauCeti.Algebra.Lie.Sl2.Decomposition
public import TauCeti.Algebra.Lie.Submodule.DirectSum

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped DirectSum
namespace KhanSL2.Factorization.EvenWeightBounds
open BGG

/-- The concrete matrix Cartan element is Tau Ceti's standard Cartan element. -/
theorem matrix_h_eq_standard : MatrixSL2.h = TauCeti.slFinTwoBasis ℂ 2 := by
  apply Subtype.ext
  rw [TauCeti.slFinTwoBasis_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [MatrixSL2.h]

theorem standard_highest_eigenvector (n : ℕ) :
    cartan (TauCeti.Sl2Std ℂ n) (TauCeti.Sl2Std.basis ℂ n 0) =
      (n : ℂ) • TauCeti.Sl2Std.basis ℂ n 0 := by
  change ⁅MatrixSL2.h,TauCeti.Sl2Std.basis ℂ n 0⁆ = _
  rw [matrix_h_eq_standard,TauCeti.Sl2Std.lie_slFinTwoBasis_two,TauCeti.Sl2Std.diag_basis]
  simp

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule G V] [LieModule ℂ G V]

/-- Any embedded standard irreducible has the bounded even highest weight. -/
theorem highestWeight_bound_of_embedding (m n : ℕ)
    (hp : aeval (cartan V) (evenBoundPolynomial m) = 0)
    (f : TauCeti.Sl2Std ℂ n →ₗ⁅ℂ,G⁆ V) (hf : Function.Injective f) :
    ∃ q : ℕ, q ≤ m ∧ n = 2*q := by
  let b := TauCeti.Sl2Std.basis ℂ n 0
  have hb : f b ≠ 0 := fun h => (TauCeti.Sl2Std.basis ℂ n).ne_zero 0 (hf (h.trans (map_zero f).symm))
  apply naturalEigenvalue_even_bound (cartan V) m n hp (f b) hb
  change ⁅MatrixSL2.h,f b⁆ = (n : ℂ) • f b
  rw [← f.map_lie,show ⁅MatrixSL2.h,b⁆ = (n : ℂ) • b from standard_highest_eigenvector n,map_smul]

theorem highestWeight_strict_bound_of_embedding (m n : ℕ)
    (hp : aeval (cartan V) (evenBoundPolynomial m) = 0)
    (htop : (cartan V).eigenspace (2*(m : ℂ)) = ⊥)
    (f : TauCeti.Sl2Std ℂ n →ₗ⁅ℂ,G⁆ V) (hf : Function.Injective f) :
    ∃ q : ℕ, q < m ∧ n = 2*q := by
  let b := TauCeti.Sl2Std.basis ℂ n 0
  have hb : f b ≠ 0 := fun h => (TauCeti.Sl2Std.basis ℂ n).ne_zero 0 (hf (h.trans (map_zero f).symm))
  apply naturalEigenvalue_even_strict_bound (cartan V) m n hp htop (f b) hb
  change ⁅MatrixSL2.h,f b⁆ = (n : ℂ) • f b
  rw [← f.map_lie,show ⁅MatrixSL2.h,b⁆ = (n : ℂ) • b from standard_highest_eigenvector n,map_smul]

variable [FiniteDimensional ℂ V]

/-- The concrete finite-dimensional module is an internal direct sum of actual
standard even irreducibles with ranks at most m. -/
theorem exists_bounded_internal_decomposition (m : ℕ)
    (hp : aeval (cartan V) (evenBoundPolynomial m) = 0) :
    ∃ (k : ℕ) (N : Fin k → LieSubmodule ℂ G V) (q : Fin k → ℕ),
      DirectSum.IsInternal (fun i => (N i).toSubmodule) ∧
      (∀ i, q i ≤ m) ∧ ∀ i, Nonempty (N i ≃ₗ⁅ℂ,G⁆ Coefficient (q i)) := by
  obtain ⟨k,N,n,hN,hn⟩ := TauCeti.Sl2Std.exists_isInternal_lieModuleEquiv ℂ V
  let e := fun i => (hn i).some
  have hq (i : Fin k) : ∃ q : ℕ, q ≤ m ∧ n i = 2*q :=
    highestWeight_bound_of_embedding m (n i) hp
      ((N i).incl.comp (e i).symm.toLieModuleHom)
      (Subtype.val_injective.comp (e i).symm.injective)
  choose q hqm hqn using hq
  refine ⟨k,N,q,hN,hqm,fun i => ?_⟩
  change Nonempty (N i ≃ₗ⁅ℂ,G⁆ TauCeti.Sl2Std ℂ (2*q i))
  rw [← hqn i]
  exact ⟨e i⟩

/-- If the top eigenspace is zero, every actual irreducible constituent has
strictly smaller rank; this is the strict decrease required by local dévissage. -/
theorem exists_strict_internal_decomposition (m : ℕ)
    (hp : aeval (cartan V) (evenBoundPolynomial m) = 0)
    (htop : (cartan V).eigenspace (2*(m : ℂ)) = ⊥) :
    ∃ (k : ℕ) (N : Fin k → LieSubmodule ℂ G V) (q : Fin k → ℕ),
      DirectSum.IsInternal (fun i => (N i).toSubmodule) ∧
      (∀ i, q i < m) ∧ ∀ i, Nonempty (N i ≃ₗ⁅ℂ,G⁆ Coefficient (q i)) := by
  obtain ⟨k,N,n,hN,hn⟩ := TauCeti.Sl2Std.exists_isInternal_lieModuleEquiv ℂ V
  let e := fun i => (hn i).some
  have hq (i : Fin k) : ∃ q : ℕ, q < m ∧ n i = 2*q :=
    highestWeight_strict_bound_of_embedding m (n i) hp htop
      ((N i).incl.comp (e i).symm.toLieModuleHom)
      (Subtype.val_injective.comp (e i).symm.injective)
  choose q hqm hqn using hq
  refine ⟨k,N,q,hN,hqm,fun i => ?_⟩
  change Nonempty (N i ≃ₗ⁅ℂ,G⁆ TauCeti.Sl2Std ℂ (2*q i))
  rw [← hqn i]
  exact ⟨e i⟩

/-- The bounded internal decomposition as a concrete finite direct-sum equivalence. -/
theorem exists_bounded_lieModuleEquiv (m : ℕ)
    (hp : aeval (cartan V) (evenBoundPolynomial m) = 0) :
    ∃ (k : ℕ) (q : Fin k → ℕ), (∀ i, q i ≤ m) ∧
      Nonempty (V ≃ₗ⁅ℂ,G⁆ ⨁ i : Fin k, Coefficient (q i)) := by
  obtain ⟨k,N,q,hN,hq,he⟩ := exists_bounded_internal_decomposition m hp
  refine ⟨k,q,hq,?_⟩
  exact ⟨(DirectSum.lieModuleEquivOfIsInternal N hN).symm.trans
    (DirectSum.lieModuleEquivCongrRight fun i => (he i).some)⟩

/-- Absence of the top eigenvalue gives a concrete sum of strictly lower even
irreducibles, including the zero module as the empty sum. -/
theorem exists_strict_lieModuleEquiv (m : ℕ)
    (hp : aeval (cartan V) (evenBoundPolynomial m) = 0)
    (htop : (cartan V).eigenspace (2*(m : ℂ)) = ⊥) :
    ∃ (k : ℕ) (q : Fin k → ℕ), (∀ i, q i < m) ∧
      Nonempty (V ≃ₗ⁅ℂ,G⁆ ⨁ i : Fin k, Coefficient (q i)) := by
  obtain ⟨k,N,q,hN,hq,he⟩ := exists_strict_internal_decomposition m hp htop
  refine ⟨k,q,hq,?_⟩
  exact ⟨(DirectSum.lieModuleEquivOfIsInternal N hN).symm.trans
    (DirectSum.lieModuleEquivCongrRight fun i => (he i).some)⟩

end KhanSL2.Factorization.EvenWeightBounds

