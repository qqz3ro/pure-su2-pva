module

public import KhanSL2.StrongMacdonald.Herm

@[expose] public section

/-!
# The two basic adjunctions

`σ_g† = ∂_g` (Bargmann) and `ψ_n† = (1/(n+1)) ι_n`.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace KhanSL2.StrongMacdonald

open AddMonoidAlgebra (single)

/-- The odd metric weight `1/(n+1)` of `ψ_n = ψ(-(n+1))`. -/
def lamP (n : PMode) : ℂ := 1 / ((n.index : ℂ) + 1)

theorem wG_add_single (g : SMode) (e : Exp) (s : Finset PMode) :
    wG (Finsupp.single g 1 + e) s = wG e s * ((e g : ℝ) + 1) := by
  unfold wG
  have key : ((Finsupp.single g 1 + e).prod fun _ k => (k.factorial : ℝ)) =
      (e.prod fun _ k => (k.factorial : ℝ)) * ((e g : ℝ) + 1) := by
    classical
    set S := insert g e.support
    have h1 : (Finsupp.single g 1 + e).support ⊆ S := by
      intro x hx
      rw [Finset.mem_insert]
      by_cases hxg : x = g
      · exact Or.inl hxg
      · right
        rw [Finsupp.mem_support_iff] at hx ⊢
        simpa [Finsupp.single_apply, Ne.symm hxg] using hx
    have h2 : e.support ⊆ S := Finset.subset_insert _ _
    rw [Finsupp.prod_of_support_subset _ h1 _ (fun _ _ => by simp),
      Finsupp.prod_of_support_subset _ h2 _ (fun _ _ => by simp),
      ← Finset.mul_prod_erase S _ (Finset.mem_insert_self g _),
      ← Finset.mul_prod_erase S _ (Finset.mem_insert_self g _)]
    have h3 : ∀ x ∈ S.erase g, ((((Finsupp.single g 1 + e : Exp)) x).factorial : ℝ) =
        ((e x).factorial : ℝ) := by
      intro x hx
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hx)),
        zero_add]
    rw [Finset.prod_congr rfl h3, Finsupp.add_apply, Finsupp.single_eq_same,
      show 1 + e g = e g + 1 by ring, Nat.factorial_succ]
    push_cast
    ring
  rw [key]
  ring

theorem wG_insert (e : Exp) {n : PMode} {s : Finset PMode} (hn : n ∉ s) :
    wG e (insert n s) = wG e s * (1 / ((n.index : ℝ) + 1)) := by
  unfold wG
  rw [Finset.prod_insert hn]
  ring

theorem sig_mul_mono' (g : SMode) (e : Exp) (s : Finset PMode) :
    sig g * mono e s = mono (Finsupp.single g 1 + e) s := sig_mul_mono g e s

theorem psi_mul_mono (n : PMode) (e : Exp) (s : Finset PMode) :
    psi n * mono e s = if n ∈ s then 0 else
      ((-1 : ℂ) ^ FiniteExterior.position BGG.PositiveCE.Mode.code n s) • mono e (insert n s) := by
  have hc : (FiniteExterior.GeneratorOrder.code : PMode → ℕ) = BGG.PositiveCE.Mode.code := rfl
  rw [mono, psi_mul_single, FiniteExterior.mul_def, FiniteExterior.generator]
  simp only [hc, FiniteExterior.wedge_monomial, FiniteExterior.monomialWedge,
    Finset.disjoint_singleton_left, FiniteExterior.inversionCount_singleton_left]
  split
  · rw [mono, FiniteExterior.monomial, AddMonoidAlgebra.smul_single, Finsupp.smul_single,
      smul_eq_mul, mul_one, ← Finset.insert_eq]
  · rename_i h
    simp only [AddMonoidAlgebra.single_zero]
    rw [if_pos (not_not.mp h)]

theorem iP_mono (n : PMode) (e : Exp) (s : Finset PMode) :
    iP n (mono e s) = if n ∈ s then
      ((-1 : ℂ) ^ FiniteExterior.position BGG.PositiveCE.Mode.code n s) • mono e (s.erase n)
      else 0 := by
  rw [mono, iP_single, FiniteExterior.contraction_monomial]
  split
  · rw [mono, AddMonoidAlgebra.smul_single]
  · simp

/-- `σ_g† = ∂_g`. -/
theorem isAdj_sig (g : SMode) : IsAdj (lmul (sig g)) (dS g) := by
  apply isAdj_of_mono
  intro e s e' s'
  rw [lmul_apply, sig_mul_mono', herm_mono_left, dS_mono, herm_mono_left, coefW_smul,
    coefW_mono, coefW_mono]
  by_cases hs : s' = s
  · subst hs
    by_cases he : e' = Finsupp.single g 1 + e
    · subst he
      have h1 : Finsupp.single g 1 + e - Finsupp.single g 1 = e := by simp
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨h1, rfl⟩, wG_add_single, Finsupp.add_apply,
        Finsupp.single_eq_same]
      push_cast
      ring
    · rw [if_neg (fun h => he h.1)]
      by_cases hg : e' g = 0
      · simp [hg]
      · rw [if_neg]
        · simp
        · rintro ⟨h1, _⟩
          apply he
          rw [← h1]
          have hle : Finsupp.single g 1 ≤ e' := by
            rw [Finsupp.single_le_iff]; omega
          exact (add_tsub_cancel_of_le hle).symm
  · rw [if_neg (fun h => hs h.2), if_neg (fun h => hs h.2)]
    simp

/-- `ψ_n† = (1/(n+1)) ι_n`. -/
theorem isAdj_psi (n : PMode) : IsAdj (lmul (psi n)) (lamP n • iP n) := by
  apply isAdj_of_mono
  intro e s e' s'
  rw [lmul_apply, psi_mul_mono, LinearMap.smul_apply, iP_mono, herm_smul_right]
  by_cases hns : n ∈ s
  · rw [if_pos hns, herm_zero_left]
    split
    · rw [herm_smul_right, herm_mono_left, coefW_mono, if_neg]
      · simp
      · rintro ⟨rfl, rfl⟩
        exact Finset.notMem_erase n s' hns
    · simp [herm_zero_right]
  · rw [if_neg hns, herm_smul_left, herm_mono_left, coefW_mono]
    by_cases h : e' = e ∧ s' = insert n s
    · obtain ⟨rfl, rfl⟩ : e = e' ∧ insert n s = s' := ⟨h.1.symm, h.2.symm⟩
      rw [if_pos ⟨rfl, rfl⟩, if_pos (Finset.mem_insert_self n s), herm_smul_right,
        herm_mono_left, coefW_mono, if_pos ⟨rfl, Finset.erase_insert hns⟩,
        FiniteExterior.position_insert_self, wG_insert e hns, lamP]
      simp only [map_pow, map_neg, map_one, mul_one]
      push_cast
      ring
    · rw [if_neg h]
      split
      · rename_i hn'
        rw [herm_smul_right, herm_mono_left, coefW_mono, if_neg]
        · simp
        · rintro ⟨rfl, hs⟩
          apply h
          refine ⟨rfl, ?_⟩
          rw [← hs, Finset.insert_erase hn']
      · simp [herm_zero_right]

end KhanSL2.StrongMacdonald
