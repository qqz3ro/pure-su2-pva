module

public import KhanSL2.SymmetricFamily.LocalEvenGenerated
public import KhanSL2.Factorization.QuotientPath
public import KhanSL2.Factorization.ShuffleSurjectiveQuotient

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-! Actual local symmetric and exterior tensor families, and successive
quotients from the symmetric family to its even evaluation tensor word.
Every quotient kernel has strictly smaller total highest weight. -/
noncomputable section
namespace KhanSL2.Factorization.EvenTensorWord
open BGG Macdonald SymmetricFamily

/-- The original local symmetric coefficient fibres, with the word's parenthesization. -/
def symmetricModule : EvenTensorWord → FiniteCurrent
  | leaf a q => FiniteCurrent.of (LocalSymmetricFibre q a)
  | tensor u v => (symmetricModule u).tensor (symmetricModule v)

/-- The corresponding actual local exterior coefficient fibres. -/
def exteriorModule : EvenTensorWord → FiniteCurrent
  | leaf a q => FiniteCurrent.of (LocalExteriorFibre q a)
  | tensor u v => (exteriorModule u).tensor (exteriorModule v)

/-- A distinct-support evaluation tensor word belongs to its precise bounded class. -/
theorem module_evenGenerated (t : EvenTensorWord) (ht : t.Distinct) :
    EvenGenerated t.support (fun q => q≤t.weight) t.module :=
  .base ⟨t,ht,(fun _ h => h),le_rfl,⟨(1 : t.module ≃ₗ⁅ℂ,Current⁆ t.module)⟩⟩

/-- The actual symmetric tensor family has a bounded even evaluation filtration. -/
theorem symmetricModule_evenGenerated (t : EvenTensorWord) (ht : t.Distinct) :
    EvenGenerated t.support (fun q => q≤t.weight) t.symmetricModule := by
  induction t with
  | leaf a q => exact localSymmetric_evenGenerated q a {a} rfl
  | tensor u v ihu ihv => exact EvenGenerated.tensor_le ht.2.2 (ihu ht.1) (ihv ht.2.1)

/-- The actual exterior tensor family has the same bounded even evaluation property. -/
theorem exteriorModule_evenGenerated (t : EvenTensorWord) (ht : t.Distinct) :
    EvenGenerated t.support (fun q => q≤t.weight) t.exteriorModule := by
  induction t with
  | leaf a q => exact localExterior_evenGenerated q a {a} rfl
  | tensor u v ihu ihv => exact EvenGenerated.tensor_le ht.2.2 (ihu ht.1) (ihv ht.2.1)

/-- Tensorized actual local top quotients reach the prescribed even evaluation tensor.
Each intermediate kernel is a proved finite extension of strictly lower-weight words. -/
theorem topQuotientPath (t : EvenTensorWord) (ht : t.Distinct) :
    QuotientPath (EvenTensorGenerator t.support (fun q => q<t.weight)) t.symmetricModule t.module := by
  induction t with
  | leaf a q =>
    exact .step (LocalTopKernel q a).incl (localSymmetricTopQuotient q a)
      (kernelSplitOfSurjective _ (localSymmetricTopQuotient_surjective q a))
      (localTopKernel_evenGenerated q a {a} rfl)
  | tensor u v ihu ihv =>
    have hleft : QuotientPath (EvenTensorGenerator (u.support ∪ v.support) (fun q => q<u.weight+v.weight))
        (u.symmetricModule.tensor v.symmetricModule) (u.module.tensor v.symmetricModule) :=
      (ihu ht.1).tensorRight v.symmetricModule (fun X hX =>
        EvenGenerated.tensor_lt_le ht.2.2 (.base hX) (v.symmetricModule_evenGenerated ht.2.1))
    have hright : QuotientPath (EvenTensorGenerator (u.support ∪ v.support) (fun q => q<u.weight+v.weight))
        (u.module.tensor v.symmetricModule) (u.module.tensor v.module) :=
      (ihv ht.2.1).tensorLeft u.module (fun X hX =>
        EvenGenerated.tensor_le_lt ht.2.2 (u.module_evenGenerated ht.1) (.base hX))
    exact hleft.trans hright

end KhanSL2.Factorization.EvenTensorWord
