module

public import KhanSL2.StrongMacdonald.Subst

@[expose] public section

/-!
# Substitutions on monomials and coordinate projections

`liftW` on a monomial is the ordered product of the odd images times the product of powers
of the even images. Projections killing some generators act diagonally on monomials, and an
element which only involves allowed even generators and is killed by the contractions in the
forbidden odd generators is fixed by the projection.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

open AddMonoidAlgebra (single)

/-! ## Projections -/

section Proj

variable (P : SMode → Prop) [DecidablePred P] (Q : PMode → Prop) [DecidablePred Q]

/-- Kill the even generators outside `P` and the odd generators outside `Q`. -/
def proj : W →ₐ[ℂ] W :=
  substW (fun g => if P g then sig g else 0) (fun m => if Q m then psi m else 0)
    (fun g => by split_ifs; exacts [isPar_sig g, IsPar.zero 0])
    (fun m => by split_ifs; exacts [isPar_psi m, IsPar.zero 1])

theorem orderedEval_generator (t : Finset PMode) :
    FiniteExterior.orderedEval FiniteExterior.generator t = FiniteExterior.monomial t := by
  have h := congrArg (fun φ : Ext →ₐ[ℂ] Ext => φ (FiniteExterior.monomial t))
    substituteLin_generator_eq_id
  simp only [AlgHom.id_apply] at h
  rw [← FiniteExterior.substituteLinear_monomial]
  exact h

theorem mono_zero_eq (t : Finset PMode) : mono 0 t = FiniteExterior.orderedEval psi t := by
  have h1 : FiniteExterior.orderedEval psi t =
      ofExt (FiniteExterior.orderedEval FiniteExterior.generator t) := by
    simp only [FiniteExterior.orderedEval, map_list_prod, List.map_map]
    rfl
  rw [h1, orderedEval_generator, ofExt_apply, mono]

theorem sig_pow_mul_mono (g : SMode) (k : ℕ) (e : Exp) (t : Finset PMode) :
    sig g ^ k * mono e t = mono (Finsupp.single g k + e) t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, sig_mul_mono, ← add_assoc, ← Finsupp.single_add, add_comm 1 k]

theorem proj_psi_zero (t : Finset PMode) :
    proj P Q (mono 0 t) = if ∀ m ∈ t, Q m then mono 0 t else 0 := by
  rw [mono_zero_eq, FiniteExterior.orderedEval, map_list_prod, List.map_map]
  have hf : (proj P Q) ∘ psi = fun m => if Q m then psi m else 0 := by
    funext m; simp [proj]
  rw [hf]
  split_ifs with h
  · congr 1
    refine List.map_congr_left fun m hm => ?_
    rw [if_pos (h m (by simpa using hm))]
  · push Not at h
    obtain ⟨m, hm, hQ⟩ := h
    apply List.prod_eq_zero
    rw [List.mem_map]
    exact ⟨m, by simpa using hm, by rw [if_neg hQ]⟩

theorem proj_mono (e : Exp) (t : Finset PMode) :
    proj P Q (mono e t) = if (∀ g ∈ e.support, P g) ∧ (∀ m ∈ t, Q m) then mono e t else 0 := by
  induction e using Finsupp.induction with
  | zero => simpa using proj_psi_zero P Q t
  | single_add g k e hg hk ih =>
    rw [← sig_pow_mul_mono, map_mul, map_pow, ih, Finsupp.support_single_add hg hk]
    have hsg : proj P Q (sig g) = if P g then sig g else 0 := by simp [proj]
    rw [hsg]
    by_cases hP : P g
    · rw [if_pos hP]
      by_cases hgood : (∀ g ∈ e.support, P g) ∧ (∀ m ∈ t, Q m)
      · rw [if_pos hgood, if_pos ⟨by simpa [hP] using hgood.1, hgood.2⟩, sig_pow_mul_mono]
      · rw [if_neg hgood, mul_zero, if_neg]
        rintro ⟨h1, h2⟩
        exact hgood ⟨fun g' hg' => h1 g' (by simp [hg']), h2⟩
    · rw [if_neg hP, zero_pow hk, zero_mul, if_neg]
      rintro ⟨h1, _⟩
      exact hP (h1 g (by simp))

theorem coefW_proj (x : W) (e : Exp) (t : Finset PMode) :
    coefW (proj P Q x) e t =
      if (∀ g ∈ e.support, P g) ∧ (∀ m ∈ t, Q m) then coefW x e t else 0 := by
  induction x using mono_induction with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, coefW_add, coefW_add, hx, hy]; split_ifs <;> simp
  | hsmul c x hx => rw [map_smul, coefW_smul, coefW_smul, hx]; split_ifs <;> simp
  | hmono e' t' =>
    rw [proj_mono]
    by_cases h1 : (∀ g ∈ e'.support, P g) ∧ (∀ m ∈ t', Q m)
    · rw [if_pos h1]
      by_cases h2 : (∀ g ∈ e.support, P g) ∧ (∀ m ∈ t, Q m)
      · rw [if_pos h2]
      · rw [if_neg h2, coefW_mono, if_neg]
        rintro ⟨rfl, rfl⟩
        exact h2 h1
    · rw [if_neg h1, coefW_zero]
      by_cases h2 : (∀ g ∈ e.support, P g) ∧ (∀ m ∈ t, Q m)
      · rw [if_pos h2, coefW_mono, if_neg]
        rintro ⟨rfl, rfl⟩
        exact h1 h2
      · rw [if_neg h2]

theorem coefW_sub (x y : W) (e : Exp) (t : Finset PMode) :
    coefW (x - y) e t = coefW x e t - coefW y e t := by
  simp [coefW]

theorem coefW_iP_erase {m : PMode} {t : Finset PMode} (hm : m ∈ t) (x : W) (e : Exp) :
    coefW (iP m x) e (t.erase m) =
      (-1 : ℂ) ^ FiniteExterior.position BGG.PositiveCE.Mode.code m t * coefW x e t := by
  induction x using mono_induction with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, coefW_add, coefW_add, hx, hy, mul_add]
  | hsmul c x hx => rw [map_smul, coefW_smul, coefW_smul, hx]; ring
  | hmono e' t' =>
    rw [iP_mono, coefW_mono]
    by_cases hm' : m ∈ t'
    · rw [if_pos hm', coefW_smul, coefW_mono]
      by_cases he : e' = e ∧ t' = t
      · obtain ⟨rfl, rfl⟩ := he
        simp
      · rw [if_neg he, mul_zero, if_neg]
        · simp
        rintro ⟨rfl, h2⟩
        apply he
        refine ⟨rfl, ?_⟩
        rw [← Finset.insert_erase hm', h2, Finset.insert_erase hm]
    · rw [if_neg hm', coefW_zero, if_neg, mul_zero]
      rintro ⟨-, rfl⟩
      exact hm' hm

theorem coefW_eq_zero_of_iP {m : PMode} {t : Finset PMode} (hm : m ∈ t) {x : W}
    (h : iP m x = 0) (e : Exp) : coefW x e t = 0 := by
  have := coefW_iP_erase hm x e
  rw [h, coefW_zero] at this
  rcases mul_eq_zero.mp this.symm with h1 | h1
  · exact absurd h1 (pow_ne_zero _ (by norm_num))
  · exact h1

/-- An element involving only allowed even generators and killed by the contractions in the
forbidden odd generators is fixed by the projection. -/
theorem proj_eq_self {x : W} (hσ : ∀ e t, coefW x e t ≠ 0 → ∀ g ∈ e.support, P g)
    (hψ : ∀ m, ¬ Q m → iP m x = 0) : proj P Q x = x := by
  rw [← sub_eq_zero]
  apply eq_zero_of_coefW
  intro e t
  rw [coefW_sub, coefW_proj, sub_eq_zero]
  split_ifs with h
  · rfl
  · symm
    by_contra hne
    apply h
    refine ⟨hσ e t hne, fun m hm => ?_⟩
    by_contra hQ
    exact hne (coefW_eq_zero_of_iP hm (hψ m hQ) e)

end Proj

end KhanSL2.StrongMacdonald
