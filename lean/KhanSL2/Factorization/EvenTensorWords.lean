module

public import KhanSL2.Factorization.FiniteCurrent
public import KhanSL2.Macdonald.EvaluationIrreducible

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Finite tensor words of even evaluation representations, with their actual
support and total half-highest-weight. Zero weights are allowed. -/
noncomputable section
namespace KhanSL2.Factorization
open BGG Macdonald

/-- A nonempty tensor expression; no choice of associator is suppressed. -/
inductive EvenTensorWord
  | leaf (point : ℂ) (weight : ℕ)
  | tensor (left right : EvenTensorWord)

namespace EvenTensorWord
/-- The prescribed parenthesized tensor product of evaluation modules. -/
def module : EvenTensorWord → FiniteCurrent
  | leaf a q => FiniteCurrent.of (EvenEvaluation a q)
  | tensor u v => (module u).tensor (module v)

/-- Total half-highest-weight, used for the descending induction. -/
def weight : EvenTensorWord → ℕ
  | leaf _ q => q
  | tensor u v => weight u + weight v

/-- The specified support set; a zero-weight leaf retains its harmless support label. -/
def support : EvenTensorWord → Set ℂ
  | leaf a _ => {a}
  | tensor u v => support u ∪ support v
/-- Every binary factorization separates distinct support points. -/
def Distinct : EvenTensorWord → Prop
  | leaf _ _ => True
  | tensor u v => u.Distinct ∧ v.Distinct ∧ Disjoint u.support v.support
end EvenTensorWord

/-- The actual finite tensor generators having the asserted support and weight. -/
def EvenTensorGenerator (S : Set ℂ) (w : ℕ → Prop) (M : FiniteCurrent) : Prop :=
  ∃ t : EvenTensorWord, t.Distinct ∧ t.support ⊆ S ∧ w t.weight ∧ Nonempty (M ≃ₗ⁅ℂ,Current⁆ t.module)

/-- Finite extensions of those concrete tensor generators. -/
abbrev EvenGenerated (S : Set ℂ) (w : ℕ → Prop) (M : FiniteCurrent) : Prop :=
  FiniteExtensionClosure (EvenTensorGenerator S w) M

namespace EvenGenerated
/-- Every specified even evaluation module is a generator with its stated point and weight. -/
theorem evaluation {S : Set ℂ} {w : ℕ → Prop} (a : ℂ) (q : ℕ)
    (ha : a ∈ S) (hq : w q) : EvenGenerated S w (FiniteCurrent.of (EvenEvaluation a q)) := by
  apply FiniteExtensionClosure.base
  refine ⟨.leaf a q,True.intro,?_,hq,⟨(1 : EvenEvaluation a q ≃ₗ⁅ℂ,Current⁆ EvenEvaluation a q)⟩⟩
  intro b hb
  have hb' : b=a := hb
  simpa only [hb'] using ha

/-- Enlarging a support or weight range retains the proved finite extension structure. -/
theorem mono {S T : Set ℂ} {w v : ℕ → Prop} {M : FiniteCurrent}
    (hst : S ⊆ T) (hwv : ∀ n, w n → v n) (h : EvenGenerated S w M) : EvenGenerated T v M :=
  FiniteExtensionClosure.mono (fun _ ⟨t,hd,ht,hq,e⟩ =>
    .base ⟨t,hd,ht.trans hst,hwv _ hq,e⟩) h

/-- Tensor products at disjoint supports preserve actual supports and add weight bounds. -/
theorem tensor {S T : Set ℂ} {w v u : ℕ → Prop} {M N : FiniteCurrent}
    (hST : Disjoint S T) (hadd : ∀ i j, w i → v j → u (i+j))
    (hM : EvenGenerated S w M) (hN : EvenGenerated T v N) : EvenGenerated (S ∪ T) u (M.tensor N) := by
  apply FiniteExtensionClosure.tensor (hM:=hM) (hN:=hN)
  rintro X Y ⟨x,hdx,hx,hw,⟨ex⟩⟩ ⟨y,hdy,hy,hv,⟨ey⟩⟩
  apply FiniteExtensionClosure.base
  refine ⟨.tensor x y,⟨hdx,hdy,hST.mono hx hy⟩,?_,hadd _ _ hw hv,⟨FiniteCurrent.tensorEquiv ex ey⟩⟩
  intro a ha
  exact ha.elim (fun h => Or.inl (hx h)) (fun h => Or.inr (hy h))

/-- Bounded weights add under the original diagonal tensor action. -/
theorem tensor_le {S T : Set ℂ} {m n : ℕ} {M N : FiniteCurrent} (hST : Disjoint S T)
    (hM : EvenGenerated S (fun q => q≤m) M) (hN : EvenGenerated T (fun q => q≤n) N) :
    EvenGenerated (S ∪ T) (fun q => q≤m+n) (M.tensor N) :=
  tensor hST (fun _ _ hi hj => by omega) hM hN

/-- A strict drop in one factor remains strict in the total weight. -/
theorem tensor_lt_le {S T : Set ℂ} {m n : ℕ} {M N : FiniteCurrent} (hST : Disjoint S T)
    (hM : EvenGenerated S (fun q => q<m) M) (hN : EvenGenerated T (fun q => q≤n) N) :
    EvenGenerated (S ∪ T) (fun q => q<m+n) (M.tensor N) :=
  tensor hST (fun _ _ hi hj => by omega) hM hN

/-- The strict-drop statement in the other tensor factor. -/
theorem tensor_le_lt {S T : Set ℂ} {m n : ℕ} {M N : FiniteCurrent} (hST : Disjoint S T)
    (hM : EvenGenerated S (fun q => q≤m) M) (hN : EvenGenerated T (fun q => q<n) N) :
    EvenGenerated (S ∪ T) (fun q => q<m+n) (M.tensor N) :=
  tensor hST (fun _ _ hi hj => by omega) hM hN
end EvenGenerated
end KhanSL2.Factorization
