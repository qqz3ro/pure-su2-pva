module

public import KhanSL2.StrongMacdonald.LapMain

@[expose] public section

/-!
# The FGT Hermitian metric on `W`

The monomials `mono e s` are orthogonal, with
`⟨mono e s | mono e s⟩ = (∏_g (e g)!) · ∏_{n ∈ s} 1/(n+1)`
(Bargmann on the even variables, `⟨ψ(-m)|ψ(-m)⟩ = 1/m` on the odd ones).
We define the form `herm`, prove that it is a positive definite Hermitian form, and
establish the two basic adjunctions `σ_g† = ∂_g` and `ψ_n† = (1/(n+1)) ι_n`.
Adjoint pairs are closed under sums, scalars, composition and locally finite sums.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace KhanSL2.StrongMacdonald

open AddMonoidAlgebra (single)

/-- Coordinates in the monomial basis. -/
def coefW (x : W) (e : Exp) (s : Finset PMode) : ℂ := x.coeff e s

@[simp] theorem coefW_add (x y : W) (e : Exp) (s : Finset PMode) :
    coefW (x + y) e s = coefW x e s + coefW y e s := by
  simp [coefW]

@[simp] theorem coefW_smul (c : ℂ) (x : W) (e : Exp) (s : Finset PMode) :
    coefW (c • x) e s = c * coefW x e s := by
  simp [coefW]

@[simp] theorem coefW_zero (e : Exp) (s : Finset PMode) : coefW 0 e s = 0 := by
  simp [coefW]

theorem coefW_mono (e e' : Exp) (s s' : Finset PMode) :
    coefW (mono e s) e' s' = if e = e' ∧ s = s' then 1 else 0 := by
  simp only [coefW, mono, AddMonoidAlgebra.coeff_single, FiniteExterior.monomial,
    Finsupp.single_apply]
  by_cases he : e = e'
  · subst he
    simp [Finsupp.single_apply]
  · simp [he]

/-- The metric weight of a monomial. -/
def wG (e : Exp) (s : Finset PMode) : ℝ :=
  (e.prod fun _ k => (k.factorial : ℝ)) * ∏ n ∈ s, (1 / ((n.index : ℝ) + 1))

theorem wG_pos (e : Exp) (s : Finset PMode) : 0 < wG e s := by
  unfold wG
  refine mul_pos ?_ ?_
  · exact Finset.prod_pos fun g _ => by dsimp only; exact_mod_cast Nat.factorial_pos _
  · exact Finset.prod_pos fun n _ => by positivity

/-- The FGT Hermitian form, antilinear in the first variable. -/
def herm (x y : W) : ℂ :=
  x.coeff.sum fun e u => u.sum fun s a => (wG e s : ℂ) * conj a * y.coeff e s

theorem herm_add_right (x y y' : W) : herm x (y + y') = herm x y + herm x y' := by
  simp only [herm, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add, Finsupp.sum_add]

theorem herm_smul_right (x y : W) (c : ℂ) : herm x (c • y) = c * herm x y := by
  simp only [herm, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun e _ => Finsupp.sum_congr fun s _ => by ring

theorem herm_zero_right (x : W) : herm x 0 = 0 := by
  simp [herm]

theorem herm_add_left (x x' y : W) : herm (x + x') y = herm x y + herm x' y := by
  unfold herm
  rw [AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index']
  · intro e; simp
  · intro e u v
    rw [Finsupp.sum_add_index']
    · intro s; simp
    · intro s a b; simp only [map_add]; ring

theorem herm_smul_left (x y : W) (c : ℂ) : herm (c • x) y = conj c * herm x y := by
  unfold herm
  rw [AddMonoidAlgebra.coeff_smul, Finsupp.sum_smul_index']
  · rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun e _ => ?_
    rw [Finsupp.sum_smul_index']
    · rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun s _ => ?_
      simp only [smul_eq_mul, map_mul]; ring
    · intro s; simp
  · intro e; simp

theorem herm_zero_left (y : W) : herm 0 y = 0 := by
  simp [herm]

theorem herm_neg_left (x y : W) : herm (-x) y = -herm x y := by
  rw [← neg_one_smul ℂ x, herm_smul_left]; simp

theorem herm_neg_right (x y : W) : herm x (-y) = -herm x y := by
  rw [← neg_one_smul ℂ y, herm_smul_right]; simp

theorem herm_sub_left (x x' y : W) : herm (x - x') y = herm x y - herm x' y := by
  rw [sub_eq_add_neg, herm_add_left, herm_neg_left, ← sub_eq_add_neg]

theorem herm_sub_right (x y y' : W) : herm x (y - y') = herm x y - herm x y' := by
  rw [sub_eq_add_neg, herm_add_right, herm_neg_right, ← sub_eq_add_neg]

theorem herm_sum_left {ι : Type*} (s : Finset ι) (x : ι → W) (y : W) :
    herm (∑ i ∈ s, x i) y = ∑ i ∈ s, herm (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, herm_add_left, ih, Finset.sum_insert ha]

theorem herm_sum_right {ι : Type*} (s : Finset ι) (x : W) (y : ι → W) :
    herm x (∑ i ∈ s, y i) = ∑ i ∈ s, herm x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, herm_add_right, ih, Finset.sum_insert ha]

theorem herm_mono_left (e : Exp) (s : Finset PMode) (y : W) :
    herm (mono e s) y = (wG e s : ℂ) * coefW y e s := by
  rw [herm, mono, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index,
    FiniteExterior.monomial, Finsupp.sum_single_index]
  · simp [coefW]
  · simp
  · simp

theorem herm_mono_right (x : W) (e : Exp) (s : Finset PMode) :
    herm x (mono e s) = (wG e s : ℂ) * conj (coefW x e s) := by
  unfold herm
  have h : ∀ e' (u : Ext), (u.sum fun s' a => (wG e' s' : ℂ) * conj a * (mono e s).coeff e' s') =
      if e' = e then (wG e s : ℂ) * conj (u s) else 0 := by
    intro e' u
    by_cases he : e' = e
    · subst he
      rw [if_pos rfl]
      simp only [mono, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
        FiniteExterior.monomial, Finsupp.single_apply, mul_ite, mul_one, mul_zero]
      rw [Finsupp.sum_ite_eq]
      split
      · ring
      · rename_i hs; rw [Finsupp.notMem_support_iff.mp hs]; simp
    · rw [if_neg he]
      simp [mono, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm he]
  simp only [h]
  rw [Finsupp.sum_ite_eq']
  split
  · rfl
  · rename_i he
    simp [coefW, Finsupp.notMem_support_iff.mp he]

/-- Every element is a combination of monomials. -/
theorem mono_induction {P : W → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : ℂ) x, P x → P (c • x)) (hmono : ∀ e s, P (mono e s)) (x : W) : P x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => exact h0
  | add x y hx hy => exact hadd x y hx hy
  | single e u =>
    induction u using Finsupp.induction_linear with
    | zero => simpa using h0
    | add u v hu hv => rw [AddMonoidAlgebra.single_add]; exact hadd _ _ hu hv
    | single s r =>
      have : (single e (Finsupp.single s r) : W) = r • mono e s := by
        simp [mono, FiniteExterior.monomial, AddMonoidAlgebra.smul_single]
      rw [this]
      exact hsmul r _ (hmono e s)

theorem herm_conj_symm (x y : W) : herm y x = conj (herm x y) := by
  revert y
  refine mono_induction (P := fun x => ∀ y, herm y x = conj (herm x y)) ?_ ?_ ?_ ?_ x
  · intro y; simp [herm_zero_left, herm_zero_right]
  · intro x x' hx hx' y; rw [herm_add_right, herm_add_left, hx, hx', map_add]
  · intro c x hx y; rw [herm_smul_right, herm_smul_left, hx, map_mul, Complex.conj_conj]
  · intro e s y
    rw [herm_mono_right, herm_mono_left, map_mul, Complex.conj_ofReal]

/-- `⟨x|x⟩` is the real number `Σ G |x|²`. -/
def hnormSq (x : W) : ℝ :=
  x.coeff.sum fun e u => u.sum fun s a => wG e s * Complex.normSq a

theorem herm_self (x : W) : herm x x = (hnormSq x : ℂ) := by
  unfold herm hnormSq Finsupp.sum
  rw [← Complex.ofRealHom_eq_coe, map_sum]
  refine Finset.sum_congr rfl (fun (e : Exp) _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun (s : Finset PMode) _ => ?_)
  rw [map_mul, Complex.ofRealHom_eq_coe, Complex.ofRealHom_eq_coe,
    Complex.normSq_eq_conj_mul_self]
  ring

theorem hnormSq_nonneg (x : W) : 0 ≤ hnormSq x :=
  Finsupp.sum_nonneg fun e _ => Finsupp.sum_nonneg fun s _ =>
    mul_nonneg (wG_pos e s).le (Complex.normSq_nonneg _)

theorem hnormSq_eq_zero {x : W} (h : hnormSq x = 0) : x = 0 := by
  unfold hnormSq Finsupp.sum at h
  have hc : ∀ e s, x.coeff e s = 0 := by
    intro e s
    by_contra hne
    have he : e ∈ x.coeff.support := by
      rw [Finsupp.mem_support_iff]; intro h0; rw [h0] at hne; exact hne rfl
    have hs : s ∈ (x.coeff e).support := Finsupp.mem_support_iff.mpr hne
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => Finset.sum_nonneg fun s _ =>
      mul_nonneg (wG_pos e s).le (Complex.normSq_nonneg _))).mp h e he
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ =>
      mul_nonneg (wG_pos e s).le (Complex.normSq_nonneg _))).mp h1 s hs
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact (wG_pos e s).ne' h3
    · exact hne (Complex.normSq_eq_zero.mp h3)
  apply AddMonoidAlgebra.coeff_injective
  ext e s
  simpa using hc e s

theorem herm_self_eq_zero {x : W} (h : herm x x = 0) : x = 0 := by
  rw [herm_self] at h
  exact hnormSq_eq_zero (by exact_mod_cast h)

/-! ## Adjoint pairs -/

/-- `Q` is the adjoint of `P`. -/
def IsAdj (P Q : Module.End ℂ W) : Prop := ∀ x y, herm (P x) y = herm x (Q y)

theorem isAdj_of_mono {P Q : Module.End ℂ W}
    (h : ∀ e s e' s', herm (P (mono e s)) (mono e' s') = herm (mono e s) (Q (mono e' s'))) :
    IsAdj P Q := by
  intro x y
  revert y
  refine mono_induction (P := fun x => ∀ y, herm (P x) y = herm x (Q y)) ?_ ?_ ?_ ?_ x
  · intro y; simp [herm_zero_left]
  · intro x x' hx hx' y; rw [map_add, herm_add_left, herm_add_left, hx, hx']
  · intro c x hx y; rw [map_smul, herm_smul_left, herm_smul_left, hx]
  · intro e s y
    refine mono_induction (P := fun y => herm (P (mono e s)) y = herm (mono e s) (Q y))
      ?_ ?_ ?_ ?_ y
    · simp [herm_zero_right]
    · intro y y' hy hy'; rw [map_add, herm_add_right, herm_add_right, hy, hy']
    · intro c y hy; rw [map_smul, herm_smul_right, herm_smul_right, hy]
    · intro e' s'; exact h e s e' s'

theorem IsAdj.symm {P Q : Module.End ℂ W} (h : IsAdj P Q) : IsAdj Q P := by
  intro x y
  rw [herm_conj_symm, ← h y x, ← herm_conj_symm]

theorem IsAdj.comp {P P' Q Q' : Module.End ℂ W} (hP : IsAdj P P') (hQ : IsAdj Q Q') :
    IsAdj (P * Q) (Q' * P') := by
  intro x y
  rw [Module.End.mul_apply, hP, hQ]; rfl

theorem IsAdj.add {P P' Q Q' : Module.End ℂ W} (hP : IsAdj P P') (hQ : IsAdj Q Q') :
    IsAdj (P + Q) (P' + Q') := by
  intro x y
  rw [LinearMap.add_apply, herm_add_left, hP, hQ, LinearMap.add_apply, herm_add_right]

theorem IsAdj.smul {P P' : Module.End ℂ W} (c : ℂ) (hP : IsAdj P P') :
    IsAdj (c • P) (conj c • P') := by
  intro x y
  rw [LinearMap.smul_apply, herm_smul_left, hP, LinearMap.smul_apply, herm_smul_right]

theorem IsAdj.neg {P P' : Module.End ℂ W} (hP : IsAdj P P') : IsAdj (-P) (-P') := by
  intro x y
  rw [LinearMap.neg_apply, herm_neg_left, hP, LinearMap.neg_apply, herm_neg_right]

theorem IsAdj.sub {P P' Q Q' : Module.End ℂ W} (hP : IsAdj P P') (hQ : IsAdj Q Q') :
    IsAdj (P - Q) (P' - Q') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact hP.add hQ.neg

theorem IsAdj.zero : IsAdj 0 0 := by
  intro x y; simp [herm_zero_left, herm_zero_right]

theorem IsAdj.one : IsAdj 1 1 := fun _ _ => rfl

theorem IsAdj.sum {ι : Type*} (s : Finset ι) {P P' : ι → Module.End ℂ W}
    (h : ∀ i ∈ s, IsAdj (P i) (P' i)) : IsAdj (∑ i ∈ s, P i) (∑ i ∈ s, P' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsAdj.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsAdj.lsum {P Q : ℕ → Module.End ℂ W} (hP : EvZero P) (hQ : EvZero Q)
    (h : ∀ i, IsAdj (P i) (Q i)) : IsAdj (lsum P hP) (lsum Q hQ) := by
  intro x y
  obtain ⟨N, hN⟩ := hP x
  obtain ⟨M, hM⟩ := hQ y
  rw [lsum_apply_of hP (N := max N M) (fun i hi => hN i (le_of_max_le_left hi)),
    lsum_apply_of hQ (N := max N M) (fun i hi => hM i (le_of_max_le_right hi)),
    herm_sum_left, herm_sum_right]
  exact Finset.sum_congr rfl fun i _ => h i x y

theorem IsAdj.unique {P Q Q' : Module.End ℂ W} (h : IsAdj P Q) (h' : IsAdj P Q') : Q = Q' := by
  apply LinearMap.ext
  intro y
  apply sub_eq_zero.mp
  apply herm_self_eq_zero
  rw [herm_sub_right, ← h, ← h', sub_self]

end KhanSL2.StrongMacdonald
