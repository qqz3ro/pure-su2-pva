module

public import KhanSL2.Factorization.ShuffleFiniteSum
public import KhanSL2.Factorization.ShuffleEquivalences
public import KhanSL2.Factorization.CoefficientSplitExactLeft
public import KhanSL2.Factorization.CoefficientSplitFinite
public import Mathlib.LinearAlgebra.DirectSum.Finite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Bundled finite-dimensional current modules for finite extension arguments.
The bundle stores the original action and finite-dimensionality proofs. -/
noncomputable section
open scoped TensorProduct DirectSum
open CategoryTheory
namespace KhanSL2.Factorization
open BGG

/-- A finite-dimensional representation of the actual polynomial current algebra. -/
structure FiniteCurrent where
  Carrier : Type
  [addCommGroup : AddCommGroup Carrier]
  [module : Module ℂ Carrier]
  [lieRingModule : LieRingModule Current Carrier]
  [lieModule : LieModule ℂ Current Carrier]
  [finite : FiniteDimensional ℂ Carrier]

attribute [instance] FiniteCurrent.addCommGroup FiniteCurrent.module
  FiniteCurrent.lieRingModule FiniteCurrent.lieModule FiniteCurrent.finite
instance : CoeSort FiniteCurrent Type := ⟨FiniteCurrent.Carrier⟩

namespace FiniteCurrent
/-- Bundle an existing current action without changing it. -/
def of (M : Type) [AddCommGroup M] [Module ℂ M]
    [LieRingModule Current M] [LieModule ℂ Current M] [FiniteDimensional ℂ M] : FiniteCurrent := ⟨M⟩

/-- The diagonal current action on the ordinary tensor product. -/
def tensor (M N : FiniteCurrent) : FiniteCurrent := of (M ⊗[ℂ] N)

/-- The componentwise current action on the actual finite direct sum. -/
def sum {n : ℕ} (M : Fin n → FiniteCurrent) : FiniteCurrent := of (⨁ i, M i)

/-- A specified equivalence on each factor induces the specified tensor equivalence. -/
def tensorEquiv {M N P Q : FiniteCurrent}
    (e : M ≃ₗ⁅ℂ,Current⁆ N) (f : P ≃ₗ⁅ℂ,Current⁆ Q) :
    tensor M P ≃ₗ⁅ℂ,Current⁆ tensor N Q where
  __ := TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
  map_lie' {x m} := by
    change TensorProduct.map e.toLinearMap f.toLinearMap ⁅x,m⁆ =
      ⁅x,TensorProduct.map e.toLinearMap f.toLinearMap m⁆
    exact (TensorProduct.LieModule.map e.toLieModuleHom f.toLieModuleHom).map_lie x m

end FiniteCurrent

/-- The finite extension closure of a specified family of actual current modules.
It is a proposition with proof constructors, not an extra representation-theoretic assumption. -/
inductive FiniteExtensionClosure (G : FiniteCurrent → Prop) : FiniteCurrent → Prop
  | base {M : FiniteCurrent} (h : G M) : FiniteExtensionClosure G M
  | zero {M : FiniteCurrent} (h : Subsingleton M) : FiniteExtensionClosure G M
  | equiv {M N : FiniteCurrent} (e : M ≃ₗ⁅ℂ,Current⁆ N) (h : FiniteExtensionClosure G N) : FiniteExtensionClosure G M
  | extension {N M P : FiniteCurrent} (i : N →ₗ⁅ℂ,Current⁆ M) (p : M →ₗ⁅ℂ,Current⁆ P)
      (h : ConstantSplitExact i p) (hN : FiniteExtensionClosure G N) (hP : FiniteExtensionClosure G P) :
      FiniteExtensionClosure G M

namespace FiniteExtensionClosure
variable {G H : FiniteCurrent → Prop} {M N : FiniteCurrent}

/-- Any inclusion of generating families extends to their proved finite extension closures. -/
theorem mono (h : ∀ X, G X → FiniteExtensionClosure H X)
    (hM : FiniteExtensionClosure G M) : FiniteExtensionClosure H M := by
  induction hM with
  | base hg => exact h _ hg
  | zero hz => exact .zero hz
  | equiv e _ ih => exact .equiv e ih
  | extension i p hs _ _ ihn ihp => exact .extension i p hs ihn ihp

/-- The specified shuffle is stable under finite extensions in its first variable. -/
theorem shuffle_first (T : FiniteCurrent)
    (hG : ∀ X, G X → QuasiIso (shuffleComplex X T))
    (hM : FiniteExtensionClosure G M) : QuasiIso (shuffleComplex M T) := by
  induction hM with
  | base hg => exact hG _ hg
  | zero hz => let := hz; exact shuffle_quasiIso_subsingleton_first _ T
  | equiv e _ ih => have := ih; exact shuffle_quasiIso_of_equiv_first T e
  | extension i p hs _ _ ihn ihp =>
    have := ihn
    have := ihp
    exact shuffle_quasiIso_of_constantSplitExact T hs

/-- The specified shuffle is stable under finite extensions in its second variable. -/
theorem shuffle_second (T : FiniteCurrent)
    (hG : ∀ X, G X → QuasiIso (shuffleComplex T X))
    (hM : FiniteExtensionClosure G M) : QuasiIso (shuffleComplex T M) := by
  induction hM with
  | base hg => exact hG _ hg
  | zero hz => let := hz; exact shuffle_quasiIso_subsingleton_second T _
  | equiv e _ ih => have := ih; exact shuffle_quasiIso_of_equiv_second T e
  | extension i p hs _ _ ihn ihp =>
    have := ihn
    have := ihp
    exact shuffle_quasiIso_second_of_constantSplitExact T hs

/-- Finite sums require no additional closure assumption. -/
theorem finiteSum {n : ℕ} (V : Fin n → FiniteCurrent)
    (hV : ∀ i, FiniteExtensionClosure G (V i)) : FiniteExtensionClosure G (FiniteCurrent.sum V) := by
  induction n with
  | zero => exact .zero (inferInstanceAs (Subsingleton (⨁ i : Fin 0, V i)))
  | succ n ih =>
    exact .extension (finiteSumTailInclusion (fun i => V i))
      (DirectSum.lieModuleComponent ℂ (Fin (n+1)) Current (fun i => V i) 0)
      (finiteSumTailExact (fun i => V i)) (ih (fun i => V i.succ) (fun i => hV i.succ)) (hV 0)

/-- Tensor a finite extension in the first slot, retaining its proved constant splitting. -/
theorem tensorRight (T : FiniteCurrent)
    (hG : ∀ X, G X → FiniteExtensionClosure H (X.tensor T))
    (hM : FiniteExtensionClosure G M) : FiniteExtensionClosure H (M.tensor T) := by
  induction hM with
  | base hg => exact hG _ hg
  | @zero X hz => let := hz; exact .zero (inferInstanceAs (Subsingleton (X ⊗[ℂ] T)))
  | equiv e _ ih => exact .equiv (FiniteCurrent.tensorEquiv e (1 : T ≃ₗ⁅ℂ,Current⁆ T)) ih
  | extension i p hs _ _ ihn ihp => exact .extension _ _ (hs.tensorRight T) ihn ihp

/-- Tensor a finite extension in the second slot. -/
theorem tensorLeft (T : FiniteCurrent)
    (hG : ∀ X, G X → FiniteExtensionClosure H (T.tensor X))
    (hM : FiniteExtensionClosure G M) : FiniteExtensionClosure H (T.tensor M) := by
  induction hM with
  | base hg => exact hG _ hg
  | @zero X hz => let := hz; exact .zero (inferInstanceAs (Subsingleton (T ⊗[ℂ] X)))
  | equiv e _ ih => exact .equiv (FiniteCurrent.tensorEquiv (1 : T ≃ₗ⁅ℂ,Current⁆ T) e) ih
  | extension i p hs _ _ ihn ihp => exact .extension _ _ (hs.tensorLeft T) ihn ihp

/-- Tensor stability reduces entirely to the tensor products of the generating modules. -/
theorem tensor {K : FiniteCurrent → Prop}
    (h : ∀ X Y, G X → H Y → FiniteExtensionClosure K (X.tensor Y))
    (hM : FiniteExtensionClosure G M) (hN : FiniteExtensionClosure H N) :
    FiniteExtensionClosure K (M.tensor N) :=
  tensorRight N (fun X hX => tensorLeft X (fun Y hY => h X Y hX hY) hN) hM

end FiniteExtensionClosure
end KhanSL2.Factorization
