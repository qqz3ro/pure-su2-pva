module

public import KhanSL2.SymmetricFamily.SymmetricTensorWords

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-! Descending total-highest-weight induction for the specified shuffle.
The sole symmetric-family input is its actual comparison on disjoint supports;
all passage to evaluation tensors and their finite extensions is proved here. -/
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
open BGG

/-- Comparing the actual tensor generators suffices for their finite extension classes. -/
theorem evenGenerated_shuffle_of_words {S T : Set ℂ} {w v : ℕ → Prop}
    {M N : FiniteCurrent} (hM : EvenGenerated S w M) (hN : EvenGenerated T v N)
    (hword : ∀ u t : EvenTensorWord, u.Distinct → t.Distinct →
      u.support ⊆ S → t.support ⊆ T → w u.weight → v t.weight →
      QuasiIso (shuffleComplex u.module t.module)) : QuasiIso (shuffleComplex M N) := by
  apply hM.shuffle_first N
  rintro X ⟨u,hu,hsu,hwu,⟨eu⟩⟩
  apply hN.shuffle_second X
  rintro Y ⟨t,ht,hst,hvt,⟨et⟩⟩
  have : QuasiIso (shuffleComplex u.module t.module) := hword u t hu ht hsu hst hwu hvt
  have : QuasiIso (shuffleComplex X t.module) := shuffle_quasiIso_of_equiv_first t.module eu
  exact shuffle_quasiIso_of_equiv_second X et

/-- The only symmetric-family input used in the weight induction, expressed for
its actual local fibre tensors and the original shuffle. -/
def SymmetricTensorShuffle : Prop :=
  ∀ u v : EvenTensorWord, u.Distinct → v.Distinct → Disjoint u.support v.support →
    QuasiIso (shuffleComplex u.symmetricModule v.symmetricModule)

/-- The actual even evaluation tensor shuffle follows by strict total-weight induction. -/
theorem evenTensorWord_shuffle (hSym : SymmetricTensorShuffle)
    (u v : EvenTensorWord) (hu : u.Distinct) (hv : v.Distinct)
    (huv : Disjoint u.support v.support) : QuasiIso (shuffleComplex u.module v.module) := by
  have hall : ∀ n (u v : EvenTensorWord), u.weight+v.weight=n →
      u.Distinct → v.Distinct → Disjoint u.support v.support →
      QuasiIso (shuffleComplex u.module v.module) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u v hn hu hv huv
      have hfirst : QuasiIso (shuffleComplex u.module v.symmetricModule) := by
        apply (u.topQuotientPath hu).shuffle_first v.symmetricModule ?_ (hSym u v hu hv huv)
        intro X hX
        apply evenGenerated_shuffle_of_words (FiniteExtensionClosure.base hX)
          (v.symmetricModule_evenGenerated hv)
        intro x y hx hy hsx hsy hwx hwy
        exact ih (x.weight+y.weight) (by omega) x y rfl hx hy (huv.mono hsx hsy)
      apply (v.topQuotientPath hv).shuffle_second u.module ?_ hfirst
      intro Y hY
      apply evenGenerated_shuffle_of_words (u.module_evenGenerated hu) (FiniteExtensionClosure.base hY)
      intro x y hx hy hsx hsy hwx hwy
      exact ih (x.weight+y.weight) (by omega) x y rfl hx hy (huv.mono hsx hsy)
  exact hall (u.weight+v.weight) u v rfl hu hv huv

/-- Arbitrary finite extensions of the actual even tensor words factor at disjoint supports. -/
theorem evenGenerated_shuffle (hSym : SymmetricTensorShuffle)
    {S T : Set ℂ} {w v : ℕ → Prop} {M N : FiniteCurrent}
    (hST : Disjoint S T) (hM : EvenGenerated S w M) (hN : EvenGenerated T v N) :
    QuasiIso (shuffleComplex M N) := by
  apply evenGenerated_shuffle_of_words hM hN
  intro u t hu ht hsu hst _ _
  exact evenTensorWord_shuffle hSym u t hu ht (hST.mono hsu hst)

/-- In particular this proves the original exterior-family shuffle, including collisions
within either support group, from the symmetric-family comparison. -/
theorem exteriorTensorWord_shuffle (hSym : SymmetricTensorShuffle)
    (u v : EvenTensorWord) (hu : u.Distinct) (hv : v.Distinct)
    (huv : Disjoint u.support v.support) : QuasiIso (shuffleComplex u.exteriorModule v.exteriorModule) :=
  evenGenerated_shuffle hSym huv (u.exteriorModule_evenGenerated hu) (v.exteriorModule_evenGenerated hv)

end KhanSL2.Factorization
