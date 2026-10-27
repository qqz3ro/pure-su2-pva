module

public import KhanSL2.Factorization.ShuffleZero
public import TauCeti.Algebra.Lie.DirectSum

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual shuffle preserves finite direct sums of coefficient modules.
The proof uses explicit split exact sequences of the original Lie modules. -/
noncomputable section
open scoped DirectSum
open CategoryTheory
namespace KhanSL2.Factorization
open BGG

variable {n : ℕ} (V : Fin (n+1) → Type)
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, LieRingModule Current (V i)] [∀ i, LieModule ℂ Current (V i)]

/-- Extend a tail word by zero at its original first coordinate. -/
def finiteSumTailInclusion : (⨁ i : Fin n, V i.succ) →ₗ⁅ℂ,Current⁆ ⨁ i : Fin (n+1), V i where
  toFun x := DFinsupp.equivFunOnFintype.symm (Fin.cons (0 : V 0) (fun i => x i))
  map_add' x y := by
    apply DFinsupp.ext
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · change (0 : V 0) = 0+0; simp
    · rfl
  map_smul' c x := by
    apply DFinsupp.ext
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · change (0 : V 0) = c • 0; simp
    · rfl
  map_lie' {x m} := by
    apply DFinsupp.ext
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · change (0 : V 0) = ⁅x,(0 : V 0)⁆; simp
    · rfl

/-- The actual tail coordinate projection. -/
def finiteSumTailProjection : (⨁ i : Fin (n+1), V i) →ₗ⁅ℂ,Current⁆ ⨁ i : Fin n, V i.succ where
  toFun x := DFinsupp.equivFunOnFintype.symm (fun i : Fin n => x i.succ)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  map_lie' {x m} := by ext; rfl

/-- The original first coordinate and its tail give a concrete constant-split short exact sequence. -/
def finiteSumTailExact : ConstantSplitExact (finiteSumTailInclusion V)
    (DirectSum.lieModuleComponent ℂ (Fin (n+1)) Current V 0) where
  retraction := (finiteSumTailProjection V).toLinearMap
  sectionMap := (DirectSum.lieModuleOf ℂ (Fin (n+1)) Current V 0).toLinearMap
  retraction_constant := constantEquivariant_of_lieHom (finiteSumTailProjection V)
  section_constant := constantEquivariant_of_lieHom (DirectSum.lieModuleOf ℂ (Fin (n+1)) Current V 0)
  zero_comp := by
    apply LinearMap.ext
    intro x
    rfl
  left_inverse := by
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro j
    rfl
  right_inverse := by
    apply LinearMap.ext
    intro x
    exact DirectSum.of_eq_same 0 x
  decomposition := by
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · change (0 : V 0) + (DirectSum.of V 0 (x 0)) 0 = x 0
      rw [DirectSum.of_eq_same,zero_add]
    · change x j.succ + (DirectSum.of V 0 (x 0)) j.succ = x j.succ
      rw [DirectSum.of_eq_of_ne _ _ _ (Fin.succ_ne_zero j),add_zero]

variable (T : Type) [AddCommGroup T] [Module ℂ T]
  [LieRingModule Current T] [LieModule ℂ Current T]

/-- Finite direct sums in the first coefficient variable preserve the specified quasi-isomorphism. -/
theorem shuffle_quasiIso_finiteSum_first (k : ℕ) (M : Fin k → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, LieRingModule Current (M i)] [∀ i, LieModule ℂ Current (M i)]
    (h : ∀ i, QuasiIso (shuffleComplex (M i) T)) :
    QuasiIso (shuffleComplex (⨁ i : Fin k, M i) T) := by
  induction k with
  | zero => exact shuffle_quasiIso_subsingleton_first _ T
  | succ k ih =>
    have : QuasiIso (shuffleComplex (⨁ i : Fin k, M i.succ) T) := ih (fun i => M i.succ) (fun i => h i.succ)
    have : QuasiIso (shuffleComplex (M 0) T) := h 0
    exact shuffle_quasiIso_of_constantSplitExact T (finiteSumTailExact M)

/-- Finite direct sums in the second coefficient variable preserve the same specified map. -/
theorem shuffle_quasiIso_finiteSum_second (k : ℕ) (M : Fin k → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, LieRingModule Current (M i)] [∀ i, LieModule ℂ Current (M i)]
    (h : ∀ i, QuasiIso (shuffleComplex T (M i))) :
    QuasiIso (shuffleComplex T (⨁ i : Fin k, M i)) := by
  induction k with
  | zero => exact shuffle_quasiIso_subsingleton_second T _
  | succ k ih =>
    have : QuasiIso (shuffleComplex T (⨁ i : Fin k, M i.succ)) := ih (fun i => M i.succ) (fun i => h i.succ)
    have : QuasiIso (shuffleComplex T (M 0)) := h 0
    exact shuffle_quasiIso_second_of_constantSplitExact T (finiteSumTailExact M)

end KhanSL2.Factorization
