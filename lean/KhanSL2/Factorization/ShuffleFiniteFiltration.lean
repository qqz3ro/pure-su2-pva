module

public import KhanSL2.Factorization.ShuffleZero

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Finite descending dévissage for the specified shuffle, in either variable,
using the already proved constant-split exact-sequence comparison. -/
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
open BGG

variable (F Q : ℕ → Type)
  [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)]
  [∀ j, LieRingModule Current (F j)] [∀ j, LieModule ℂ Current (F j)]
  [∀ j, AddCommGroup (Q j)] [∀ j, Module ℂ (Q j)]
  [∀ j, LieRingModule Current (Q j)] [∀ j, LieModule ℂ Current (Q j)]
variable (T : Type) [AddCommGroup T] [Module ℂ T]
  [LieRingModule Current T] [LieModule ℂ Current T]
variable (i : ∀ j, F (j+1) →ₗ⁅ℂ,Current⁆ F j) (p : ∀ j, F j →ₗ⁅ℂ,Current⁆ Q j)

/-- Successively extend the genuine shuffle quasi-isomorphism through a finite filtration. -/
theorem shuffle_quasiIso_finiteFiltration_first (n : ℕ)
    (hsplit : ∀ j, j<n → ConstantSplitExact (i j) (p j))
    (hq : ∀ j, j<n → QuasiIso (shuffleComplex (Q j) T))
    (hend : QuasiIso (shuffleComplex (F n) T)) : QuasiIso (shuffleComplex (F 0) T) := by
  have haux : ∀ k j, j+k=n → QuasiIso (shuffleComplex (F j) T) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      have hj' : j=n := by omega
      subst j
      exact hend
    | succ k ih =>
      intro j hj
      have : QuasiIso (shuffleComplex (F (j+1)) T) := ih (j+1) (by omega)
      have : QuasiIso (shuffleComplex (Q j) T) := hq j (by omega)
      exact shuffle_quasiIso_of_constantSplitExact T (hsplit j (by omega))
  exact haux n 0 (by omega)

/-- The same finite descending argument in the second coefficient variable. -/
theorem shuffle_quasiIso_finiteFiltration_second (n : ℕ)
    (hsplit : ∀ j, j<n → ConstantSplitExact (i j) (p j))
    (hq : ∀ j, j<n → QuasiIso (shuffleComplex T (Q j)))
    (hend : QuasiIso (shuffleComplex T (F n))) : QuasiIso (shuffleComplex T (F 0)) := by
  have haux : ∀ k j, j+k=n → QuasiIso (shuffleComplex T (F j)) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      have hj' : j=n := by omega
      subst j
      exact hend
    | succ k ih =>
      intro j hj
      have : QuasiIso (shuffleComplex T (F (j+1))) := ih (j+1) (by omega)
      have : QuasiIso (shuffleComplex T (Q j)) := hq j (by omega)
      exact shuffle_quasiIso_second_of_constantSplitExact T (hsplit j (by omega))
  exact haux n 0 (by omega)

/-- A terminating actual filtration needs no extra terminal quasi-isomorphism hypothesis. -/
theorem shuffle_quasiIso_finiteFiltration_zero_first (n : ℕ) [Subsingleton (F n)]
    (hsplit : ∀ j, j<n → ConstantSplitExact (i j) (p j))
    (hq : ∀ j, j<n → QuasiIso (shuffleComplex (Q j) T)) : QuasiIso (shuffleComplex (F 0) T) :=
  shuffle_quasiIso_finiteFiltration_first F Q T i p n hsplit hq
    (shuffle_quasiIso_subsingleton_first (F n) T)

theorem shuffle_quasiIso_finiteFiltration_zero_second (n : ℕ) [Subsingleton (F n)]
    (hsplit : ∀ j, j<n → ConstantSplitExact (i j) (p j))
    (hq : ∀ j, j<n → QuasiIso (shuffleComplex T (Q j))) : QuasiIso (shuffleComplex T (F 0)) :=
  shuffle_quasiIso_finiteFiltration_second F Q T i p n hsplit hq
    (shuffle_quasiIso_subsingleton_second T (F n))

end KhanSL2.Factorization
