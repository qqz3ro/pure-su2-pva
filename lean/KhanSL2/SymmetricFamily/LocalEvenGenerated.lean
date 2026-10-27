module

public import KhanSL2.Factorization.FiniteExtensionFiltration
public import KhanSL2.Factorization.EvenTensorWords
public import KhanSL2.SymmetricFamily.LocalShuffleClosure

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-! The local symmetric, exterior, and top-kernel families belong to the
proved finite extension classes of actual evaluation tensor words. -/
noncomputable section
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization

/-- The actual localTopKernel has the asserted finite evaluation filtration. -/
theorem localTopKernel_evenGenerated (k : ℕ) (a : ℂ) (S : Set ℂ) (ha : a ∈ S) :
    EvenGenerated S (fun q => q < k) (FiniteCurrent.of (LocalTopKernel k a)) := by
  obtain ⟨n,hn⟩ := localTopKernelFiltration_terminates k a
  apply FiniteExtensionClosure.of_filtration (localTopKernelFiltration k a)
    (localTopKernelFiltration_antitone k a) (localTopKernelFiltration_zero k a) n hn
  intro j _
  obtain ⟨l,q,hq,⟨e⟩⟩ := localTopKernelGraded_strict k a j
  apply FiniteExtensionClosure.equiv (N:=FiniteCurrent.sum (fun i => FiniteCurrent.of (EvenEvaluation a (q i))))
    (e.trans (evaluationDirectSumEquiv a _))
  exact FiniteExtensionClosure.finiteSum (fun i => FiniteCurrent.of (EvenEvaluation a (q i)))
    (fun i => EvenGenerated.evaluation a (q i) ha (hq i))

/-- The actual localSymmetric has the asserted finite evaluation filtration. -/
theorem localSymmetric_evenGenerated (k : ℕ) (a : ℂ) (S : Set ℂ) (ha : a ∈ S) :
    EvenGenerated S (fun q => q ≤ k) (FiniteCurrent.of (LocalSymmetricFibre k a)) := by
  obtain ⟨n,hn⟩ := localSymmetricFiltration_terminates k a
  apply FiniteExtensionClosure.of_filtration (localSymmetricFiltration k a)
    (localSymmetricFiltration_antitone k a) (localSymmetricFiltration_zero k a) n hn
  intro j _
  obtain ⟨l,q,hq,⟨e⟩⟩ := localSymmetricGraded_even k a j
  apply FiniteExtensionClosure.equiv (N:=FiniteCurrent.sum (fun i => FiniteCurrent.of (EvenEvaluation a (q i))))
    (e.trans (evaluationDirectSumEquiv a _))
  exact FiniteExtensionClosure.finiteSum (fun i => FiniteCurrent.of (EvenEvaluation a (q i)))
    (fun i => EvenGenerated.evaluation a (q i) ha (hq i))

/-- The actual localExterior has the asserted finite evaluation filtration. -/
theorem localExterior_evenGenerated (k : ℕ) (a : ℂ) (S : Set ℂ) (ha : a ∈ S) :
    EvenGenerated S (fun q => q ≤ k) (FiniteCurrent.of (LocalExteriorFibre k a)) := by
  obtain ⟨n,hn⟩ := localExteriorFiltration_terminates k a
  apply FiniteExtensionClosure.of_filtration (localExteriorFiltration k a)
    (localExteriorFiltration_antitone k a) (localExteriorFiltration_zero k a) n hn
  intro j _
  obtain ⟨l,q,hq,⟨e⟩⟩ := localExteriorGraded_even k a j
  apply FiniteExtensionClosure.equiv (N:=FiniteCurrent.sum (fun i => FiniteCurrent.of (EvenEvaluation a (q i))))
    (e.trans (evaluationDirectSumEquiv a _))
  exact FiniteExtensionClosure.finiteSum (fun i => FiniteCurrent.of (EvenEvaluation a (q i)))
    (fun i => EvenGenerated.evaluation a (q i) ha (hq i))

end KhanSL2.SymmetricFamily
