module

public import KhanSL2.Factorization.RelativeChainsWeightTotalHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! A specified split coefficient-degree summand of an algebraic bigraded direct
sum is canonically the direct sum of its matching weight blocks. -/

noncomputable section
open scoped DirectSum
namespace KhanSL2.Factorization.DirectSumSlice

variable (B : ℕ × ℕ → Type*) [∀ d, AddCommGroup (B d)] [∀ d, Module ℂ (B d)]

/-- Embed one fixed second degree in the original algebraic direct sum. -/
def embed (s : ℕ) : (⨁ w, B (w,s)) →ₗ[ℂ] (⨁ d, B d) :=
  DirectSum.toModule ℂ ℕ (⨁ d, B d) (fun w => DirectSum.lof ℂ (ℕ × ℕ) B (w,s))

@[simp] theorem embed_of (s w : ℕ) (u : B (w,s)) :
    embed B s (DirectSum.of (fun w => B (w,s)) w u) = DirectSum.of B (w,s) u :=
  DirectSum.toModule_lof ℂ (φ := fun w => DirectSum.lof ℂ (ℕ × ℕ) B (w,s)) w u

/-- Extract the same degree without introducing any infinite support. -/
def restrict (s : ℕ) : (⨁ d, B d) →ₗ[ℂ] (⨁ w, B (w,s)) where
  toFun := DFinsupp.comapDomain (fun w => (w,s)) (fun _ _ h => congrArg Prod.fst h)
  map_add' := DFinsupp.comapDomain_add _ _
  map_smul' := DFinsupp.comapDomain_smul _ _

@[simp] theorem restrict_apply (s : ℕ) (u : ⨁ d, B d) (w : ℕ) :
    restrict B s u w = u (w,s) := rfl

@[simp] theorem restrict_of_same (s w : ℕ) (u : B (w,s)) :
    restrict B s (DirectSum.of B (w,s) u) = DirectSum.of (fun w => B (w,s)) w u := by
  exact DFinsupp.comapDomain_single (fun w => (w,s))
    (fun _ _ h => congrArg Prod.fst h) w u

theorem restrict_of_ne (s w t : ℕ) (h : t ≠ s) (u : B (w,t)) :
    restrict B s (DirectSum.of B (w,t) u) = 0 := by
  apply DFinsupp.ext
  intro r
  change DirectSum.of B (w,t) u (r,s) = 0
  exact DirectSum.of_eq_of_ne (β := B) (w,t) (r,s) u
    (fun he => h (congrArg Prod.snd he).symm)

@[simp] theorem restrict_embed (s : ℕ) (u : ⨁ w, B (w,s)) :
    restrict B s (embed B s u) = u := by
  induction u using DirectSum.induction_on with
  | zero => simp
  | of w u => rw [embed_of,restrict_of_same]
  | add u v hu hv => simp only [map_add,hu,hv]

variable {A V : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V]
  (e : (⨁ d, B d) ≃ₗ[ℂ] A) (I : V →ₗ[ℂ] A) (P : A →ₗ[ℂ] V) (s : ℕ)
  (hPI : ∀ v, P (I v) = v)
  (hdiag : ∀ (w t : ℕ) (u : B (w,t)),
    I (P (e (DirectSum.of B (w,t) u))) =
      if t=s then e (DirectSum.of B (w,t) u) else 0)

/-- Sum matching homogeneous classes by the original inclusions and coefficient projection. -/
def sumMap : (⨁ w, B (w,s)) →ₗ[ℂ] V :=
  P.comp (e.toLinearMap.comp (embed B s))

include hdiag in
theorem inclusion_sumMap (u : ⨁ w, B (w,s)) :
    I (sumMap B e P s u) = e (embed B s u) := by
  induction u using DirectSum.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | of w u =>
    change I (P (e (embed B s (DirectSum.of (fun w => B (w,s)) w u)))) = _
    rw [embed_of,hdiag,if_pos rfl]

include hdiag in
theorem projector_eq (u : ⨁ d, B d) :
    e (embed B s (restrict B s u)) = I (P (e u)) := by
  induction u using DirectSum.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | of d u =>
    rcases d with ⟨w,t⟩
    rw [hdiag]
    by_cases h : t=s
    · subst t
      rw [if_pos rfl,restrict_of_same,embed_of]
    · rw [if_neg h,restrict_of_ne B s w t h,map_zero,map_zero]

/-- Exact fixed-degree extraction, preserving the specified direct-sum coordinates. -/
def equiv : (⨁ w, B (w,s)) ≃ₗ[ℂ] V :=
  { sumMap B e P s with
    invFun := fun v => restrict B s (e.symm (I v))
    left_inv := by
      intro u
      change restrict B s (e.symm (I (sumMap B e P s u))) = u
      rw [inclusion_sumMap B e I P s hdiag,e.symm_apply_apply,restrict_embed]
    right_inv := by
      intro v
      apply (Function.LeftInverse.injective hPI)
      change I (sumMap B e P s (restrict B s (e.symm (I v)))) = I v
      rw [inclusion_sumMap B e I P s hdiag,projector_eq B e I P s hdiag,
        e.apply_symm_apply,hPI] }

@[simp] theorem equiv_of (w : ℕ) (u : B (w,s)) :
    equiv B e I P s hPI hdiag (DirectSum.of (fun w => B (w,s)) w u) =
      P (e (DirectSum.of B (w,s) u)) := by
  change P (e (embed B s (DirectSum.of (fun w => B (w,s)) w u))) = _
  rw [embed_of]

@[simp] theorem equiv_symm_apply (v : V) (w : ℕ) :
    (equiv B e I P s hPI hdiag).symm v w = e.symm (I v) (w,s) := rfl

end KhanSL2.Factorization.DirectSumSlice
