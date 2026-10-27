module

public import KhanSL2.SymmetricFamily.LocalKernelBounds
public import KhanSL2.SymmetricFamily.LocalExteriorBounds
public import KhanSL2.Factorization.ShuffleSubmoduleFiltration
public import KhanSL2.Factorization.ShuffleFiniteSum
public import KhanSL2.Macdonald.EvaluationDirectSum

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-! Actual local coefficient modules inherit the specified shuffle comparison
from their proved finite even evaluation filtrations. The top kernel requires
only strictly smaller highest weights. -/
noncomputable section
open CategoryTheory
open scoped DirectSum
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization
variable (T : Type) [AddCommGroup T] [Module ℂ T]
  [LieRingModule BGG.Current T] [LieModule ℂ BGG.Current T]

/-- The actual localTopKernel comparison follows from its proved strict evaluation quotients. -/
theorem localTopKernel_shuffle_quasiIso_first (k : ℕ) (a : ℂ)
    (he : ∀ q, q < k → QuasiIso (shuffleComplex (EvenEvaluation a q) T)) :
    QuasiIso (shuffleComplex (LocalTopKernel k a) T) := by
  obtain ⟨n,hn⟩ := localTopKernelFiltration_terminates k a
  apply shuffle_quasiIso_submoduleFiltration_first T (localTopKernelFiltration k a)
    (localTopKernelFiltration_antitone k a) (localTopKernelFiltration_zero k a) n hn
  intro j _
  obtain ⟨l,q,hq,⟨e⟩⟩ := localTopKernelGraded_strict k a j
  have : QuasiIso (shuffleComplex (⨁ i : Fin l, EvenEvaluation a (q i)) T) :=
    shuffle_quasiIso_finiteSum_first T l (fun i => EvenEvaluation a (q i)) (fun i => he (q i) (hq i))
  exact shuffle_quasiIso_of_equiv_first T (e.trans (evaluationDirectSumEquiv a _))

/-- The actual localTopKernel comparison follows from its proved strict evaluation quotients. -/
theorem localTopKernel_shuffle_quasiIso_second (k : ℕ) (a : ℂ)
    (he : ∀ q, q < k → QuasiIso (shuffleComplex T (EvenEvaluation a q))) :
    QuasiIso (shuffleComplex T (LocalTopKernel k a)) := by
  obtain ⟨n,hn⟩ := localTopKernelFiltration_terminates k a
  apply shuffle_quasiIso_submoduleFiltration_second T (localTopKernelFiltration k a)
    (localTopKernelFiltration_antitone k a) (localTopKernelFiltration_zero k a) n hn
  intro j _
  obtain ⟨l,q,hq,⟨e⟩⟩ := localTopKernelGraded_strict k a j
  have : QuasiIso (shuffleComplex T (⨁ i : Fin l, EvenEvaluation a (q i))) :=
    shuffle_quasiIso_finiteSum_second T l (fun i => EvenEvaluation a (q i)) (fun i => he (q i) (hq i))
  exact shuffle_quasiIso_of_equiv_second T (e.trans (evaluationDirectSumEquiv a _))

/-- The actual localSymmetric comparison follows from its proved even evaluation quotients. -/
theorem localSymmetric_shuffle_quasiIso_first (k : ℕ) (a : ℂ)
    (he : ∀ q, q ≤ k → QuasiIso (shuffleComplex (EvenEvaluation a q) T)) :
    QuasiIso (shuffleComplex (LocalSymmetricFibre k a) T) := by
  obtain ⟨n,hn⟩ := localSymmetricFiltration_terminates k a
  apply shuffle_quasiIso_submoduleFiltration_first T (localSymmetricFiltration k a)
    (localSymmetricFiltration_antitone k a) (localSymmetricFiltration_zero k a) n hn
  intro j _
  obtain ⟨l,q,hq,⟨e⟩⟩ := localSymmetricGraded_even k a j
  have : QuasiIso (shuffleComplex (⨁ i : Fin l, EvenEvaluation a (q i)) T) :=
    shuffle_quasiIso_finiteSum_first T l (fun i => EvenEvaluation a (q i)) (fun i => he (q i) (hq i))
  exact shuffle_quasiIso_of_equiv_first T (e.trans (evaluationDirectSumEquiv a _))

/-- The actual localSymmetric comparison follows from its proved even evaluation quotients. -/
theorem localSymmetric_shuffle_quasiIso_second (k : ℕ) (a : ℂ)
    (he : ∀ q, q ≤ k → QuasiIso (shuffleComplex T (EvenEvaluation a q))) :
    QuasiIso (shuffleComplex T (LocalSymmetricFibre k a)) := by
  obtain ⟨n,hn⟩ := localSymmetricFiltration_terminates k a
  apply shuffle_quasiIso_submoduleFiltration_second T (localSymmetricFiltration k a)
    (localSymmetricFiltration_antitone k a) (localSymmetricFiltration_zero k a) n hn
  intro j _
  obtain ⟨l,q,hq,⟨e⟩⟩ := localSymmetricGraded_even k a j
  have : QuasiIso (shuffleComplex T (⨁ i : Fin l, EvenEvaluation a (q i))) :=
    shuffle_quasiIso_finiteSum_second T l (fun i => EvenEvaluation a (q i)) (fun i => he (q i) (hq i))
  exact shuffle_quasiIso_of_equiv_second T (e.trans (evaluationDirectSumEquiv a _))

/-- The actual localExterior comparison follows from its proved even evaluation quotients. -/
theorem localExterior_shuffle_quasiIso_first (k : ℕ) (a : ℂ)
    (he : ∀ q, q ≤ k → QuasiIso (shuffleComplex (EvenEvaluation a q) T)) :
    QuasiIso (shuffleComplex (LocalExteriorFibre k a) T) := by
  obtain ⟨n,hn⟩ := localExteriorFiltration_terminates k a
  apply shuffle_quasiIso_submoduleFiltration_first T (localExteriorFiltration k a)
    (localExteriorFiltration_antitone k a) (localExteriorFiltration_zero k a) n hn
  intro j _
  obtain ⟨l,q,hq,⟨e⟩⟩ := localExteriorGraded_even k a j
  have : QuasiIso (shuffleComplex (⨁ i : Fin l, EvenEvaluation a (q i)) T) :=
    shuffle_quasiIso_finiteSum_first T l (fun i => EvenEvaluation a (q i)) (fun i => he (q i) (hq i))
  exact shuffle_quasiIso_of_equiv_first T (e.trans (evaluationDirectSumEquiv a _))

/-- The actual localExterior comparison follows from its proved even evaluation quotients. -/
theorem localExterior_shuffle_quasiIso_second (k : ℕ) (a : ℂ)
    (he : ∀ q, q ≤ k → QuasiIso (shuffleComplex T (EvenEvaluation a q))) :
    QuasiIso (shuffleComplex T (LocalExteriorFibre k a)) := by
  obtain ⟨n,hn⟩ := localExteriorFiltration_terminates k a
  apply shuffle_quasiIso_submoduleFiltration_second T (localExteriorFiltration k a)
    (localExteriorFiltration_antitone k a) (localExteriorFiltration_zero k a) n hn
  intro j _
  obtain ⟨l,q,hq,⟨e⟩⟩ := localExteriorGraded_even k a j
  have : QuasiIso (shuffleComplex T (⨁ i : Fin l, EvenEvaluation a (q i))) :=
    shuffle_quasiIso_finiteSum_second T l (fun i => EvenEvaluation a (q i)) (fun i => he (q i) (hq i))
  exact shuffle_quasiIso_of_equiv_second T (e.trans (evaluationDirectSumEquiv a _))

end KhanSL2.SymmetricFamily
