module

public import KhanSL2.Factorization.FiniteCurrent

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Consecutive actual quotient maps whose kernels belong to a proved finite
extension class. Tensor products keep the original constant splittings. -/
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
open BGG

/-- A finite chain of actual quotient steps and specified current equivalences. -/
inductive QuotientPath (G : FiniteCurrent → Prop) : FiniteCurrent → FiniteCurrent → Prop
  | refl (M : FiniteCurrent) : QuotientPath G M M
  | equiv {M N : FiniteCurrent} (e : M ≃ₗ⁅ℂ,Current⁆ N) : QuotientPath G M N
  | step {K M N : FiniteCurrent} (i : K →ₗ⁅ℂ,Current⁆ M) (p : M →ₗ⁅ℂ,Current⁆ N)
      (hs : ConstantSplitExact i p) (hK : FiniteExtensionClosure G K) : QuotientPath G M N
  | trans {M N P : FiniteCurrent} (hMN : QuotientPath G M N) (hNP : QuotientPath G N P) :
      QuotientPath G M P

namespace QuotientPath
variable {G H : FiniteCurrent → Prop} {M N : FiniteCurrent}

/-- Actual shuffle quasi-isomorphisms descend through these first-variable quotients. -/
theorem shuffle_first (T : FiniteCurrent)
    (hG : ∀ X, G X → QuasiIso (shuffleComplex X T))
    (h : QuotientPath G M N) (hM : QuasiIso (shuffleComplex M T)) : QuasiIso (shuffleComplex N T) := by
  revert hM
  induction h with
  | refl _ => exact id
  | equiv e =>
    intro hM
    have := hM
    exact shuffle_quasiIso_of_equiv_first T e.symm
  | step i p hs hK =>
    intro hM
    have := hM
    have := hK.shuffle_first T hG
    exact shuffle_quasiIso_quotient_of_constantSplitExact T hs
  | trans _ _ ihMN ihNP => exact fun hM => ihNP (ihMN hM)

/-- The corresponding descent in the second coefficient variable. -/
theorem shuffle_second (T : FiniteCurrent)
    (hG : ∀ X, G X → QuasiIso (shuffleComplex T X))
    (h : QuotientPath G M N) (hM : QuasiIso (shuffleComplex T M)) : QuasiIso (shuffleComplex T N) := by
  revert hM
  induction h with
  | refl _ => exact id
  | equiv e =>
    intro hM
    have := hM
    exact shuffle_quasiIso_of_equiv_second T e.symm
  | step i p hs hK =>
    intro hM
    have := hM
    have := hK.shuffle_second T hG
    exact shuffle_quasiIso_quotient_second_of_constantSplitExact T hs
  | trans _ _ ihMN ihNP => exact fun hM => ihNP (ihMN hM)

/-- Tensor every actual quotient step on the right. -/
theorem tensorRight (T : FiniteCurrent)
    (hG : ∀ X, G X → FiniteExtensionClosure H (X.tensor T))
    (h : QuotientPath G M N) : QuotientPath H (M.tensor T) (N.tensor T) := by
  induction h with
  | refl _ => exact .refl _
  | equiv e => exact .equiv (FiniteCurrent.tensorEquiv e (1 : T ≃ₗ⁅ℂ,Current⁆ T))
  | step i p hs hK => exact .step _ _ (hs.tensorRight T) (hK.tensorRight T hG)
  | trans _ _ ihMN ihNP => exact .trans ihMN ihNP

/-- Tensor every actual quotient step on the left. -/
theorem tensorLeft (T : FiniteCurrent)
    (hG : ∀ X, G X → FiniteExtensionClosure H (T.tensor X))
    (h : QuotientPath G M N) : QuotientPath H (T.tensor M) (T.tensor N) := by
  induction h with
  | refl _ => exact .refl _
  | equiv e => exact .equiv (FiniteCurrent.tensorEquiv (1 : T ≃ₗ⁅ℂ,Current⁆ T) e)
  | step i p hs hK => exact .step _ _ (hs.tensorLeft T) (hK.tensorLeft T hG)
  | trans _ _ ihMN ihNP => exact .trans ihMN ihNP

end QuotientPath
end KhanSL2.Factorization
