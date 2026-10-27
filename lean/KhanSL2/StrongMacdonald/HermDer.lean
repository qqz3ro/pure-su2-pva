module

public import KhanSL2.StrongMacdonald.HermBasic

@[expose] public section

/-!
# Adjoints of derivations

Every homogeneous derivation is the locally finite sum of elementary fields
`D = Σ_k Σ_b (D(σ_{k,b}) ∂_{k,b} + D(ψ_{k,b}) ι_{k,b})`. Its adjoint is therefore
`Σ_k Σ_b (σ_{k,b} · D(σ_{k,b})† + (k+1) ψ_{k,b} · D(ψ_{k,b})†)`, where `y†` denotes the adjoint
of left multiplication by `y`.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace KhanSL2.StrongMacdonald

open AddMonoidAlgebra (single)

/-! ## Homogeneous elements commute up to parity -/

theorem IsPar.mul_comm' {q : ℕ} {y : W} (hy : IsPar q y) (a : W) :
    y * a = parity^[q] a * y := by
  refine induction_gen (P := fun a => y * a = parity^[q] a * y) ?_ ?_ ?_ ?_ ?_ ?_ a
  · simp [map_zero]
  · rw [mul_one, parity_iterate_one, one_mul]
  · intro a b ha hb
    rw [mul_add, ha, hb, parity_iterate_add, add_mul]
  · intro r a ha
    rw [mul_smul_comm, ha, parity_iterate_smul, smul_mul_assoc]
  · intro g a ha
    have h1 := hy.mul_gen (.s g)
    simp only [Gen.elt, Gen.par, mul_zero, pow_zero, one_smul] at h1
    rw [← mul_assoc, h1, mul_assoc, ha, parity_iterate_mul, ← mul_assoc]
    congr 2
    simpa [Gen.elt, Gen.par] using (parity_iterate_gen q (.s g)).symm
  · intro m a ha
    have h1 := hy.mul_gen (.p m)
    simp only [Gen.elt, Gen.par, mul_one] at h1
    rw [← mul_assoc, h1, smul_mul_assoc, mul_assoc, ha, parity_iterate_mul, ← mul_assoc,
      ← smul_mul_assoc, ← smul_mul_assoc]
    congr 2
    simpa [Gen.elt, Gen.par] using (parity_iterate_gen q (.p m)).symm

theorem parity_iterate_add_two (p : ℕ) (a : W) : parity^[p + 2] a = parity^[p] a := by
  rw [Function.iterate_add_apply]
  congr 1
  simp [parity_parity]

/-! ## Elementary fields are derivations -/

theorem dS_homDer (g : SMode) : HomDer 0 (dS g) := by
  refine ⟨isDer_of_gen (dS_one g) fun h x => ?_, fun h => ?_⟩
  · cases h with
    | s h => simp [Gen.elt, Gen.par, dS_sig_mul, dS_sig]
    | p n => simp [Gen.elt, Gen.par, dS_psi_mul, dS_psi]
  · cases h with
    | s h =>
      simp only [Gen.elt, Gen.par, dS_sig]
      split
      · exact isPar_one 0 rfl
      · exact IsPar.zero _
    | p n => simpa [Gen.elt, Gen.par, dS_psi] using IsPar.zero 1

theorem isDer_lmul_dS {p : ℕ} {y : W} (hy : IsPar p y) (g : SMode) : IsDer p (lmul y * dS g) := by
  intro a b
  simp only [Module.End.mul_apply, lmul_apply]
  rw [(dS_homDer g).isDer a b]
  simp only [Function.iterate_zero, id_eq, mul_add, ← mul_assoc, hy.mul_comm' a]

theorem isDer_lmul_iP {p : ℕ} {y : W} (hy : IsPar (p + 1) y) (n : PMode) :
    IsDer p (lmul y * iP n) := by
  intro a b
  simp only [Module.End.mul_apply, lmul_apply]
  rw [(iP_homDer n).isDer a b]
  simp only [Function.iterate_one, mul_add, ← mul_assoc, hy.mul_comm' (parity a)]
  congr 2
  rw [← Function.iterate_succ_apply, parity_iterate_add_two]

/-! ## The elementary representation -/

theorem kills_dS (b : Fin 3) : Kills (fun k => dS ⟨k, b⟩) :=
  kills_of_homDer (fun k => dS_homDer ⟨k, b⟩)
    (fun N k hk j c hj => by
      rw [sigOf, dS_sig, if_neg]
      intro h; cases h; omega)
    (fun _ _ _ _ _ _ => by rw [psiOf, dS_psi])

theorem kills_iP (b : Fin 3) : Kills (fun k => iP ⟨k, b⟩) := kills_iota b

/-- The elementary representation family of an operator `D`. -/
def repFam (D : Module.End ℂ W) (k : ℕ) : Module.End ℂ W :=
  ∑ b, (lmul (D (sigOf k b)) * dS ⟨k, b⟩ + lmul (D (psiOf k b)) * iP ⟨k, b⟩)

theorem kills_repFam (D : Module.End ℂ W) : Kills (repFam D) :=
  Kills.sum Finset.univ fun b _ =>
    ((kills_dS b).mul_left fun k => lmul (D (sigOf k b))).add
      ((kills_iP b).mul_left fun k => lmul (D (psiOf k b)))

theorem isDer_repFam {p : ℕ} {D : Module.End ℂ W} (hD : HomDer p D) (k : ℕ) :
    IsDer p (repFam D k) :=
  IsDer.sum _ _ fun b _ =>
    (isDer_lmul_dS (by
      have h := hD.2 (.s ⟨k, b⟩); simp only [Gen.elt, Gen.par, add_zero] at h; exact h) _).add
      (isDer_lmul_iP (by have h := hD.2 (.p ⟨k, b⟩); simp only [Gen.elt, Gen.par] at h; exact h) _)

theorem repFam_sig (D : Module.End ℂ W) (k : ℕ) (g : SMode) :
    repFam D k (sig g) = if k = g.index then D (sig g) else 0 := by
  simp only [repFam, LinearMap.sum_apply, LinearMap.add_apply, Module.End.mul_apply, lmul_apply,
    dS_sig, iP_sig, mul_zero, add_zero, mul_ite, mul_one]
  by_cases hk : k = g.index
  · subst hk
    rw [if_pos rfl]
    rw [Finset.sum_eq_single g.color]
    · rw [if_pos rfl]; rfl
    · intro c _ hc; rw [if_neg]; intro h; exact hc (congrArg SMode.color h)
    · simp
  · rw [if_neg hk]
    exact Finset.sum_eq_zero fun c _ => by
      rw [if_neg]; intro h; exact hk (congrArg SMode.index h)

theorem repFam_psi (D : Module.End ℂ W) (k : ℕ) (n : PMode) :
    repFam D k (psi n) = if k = n.index then D (psi n) else 0 := by
  simp only [repFam, LinearMap.sum_apply, LinearMap.add_apply, Module.End.mul_apply, lmul_apply,
    dS_psi, iP_psi, mul_zero, zero_add, mul_ite, mul_one]
  by_cases hk : k = n.index
  · subst hk
    rw [if_pos rfl]
    rw [Finset.sum_eq_single n.color]
    · rw [if_pos rfl]; rfl
    · intro c _ hc; rw [if_neg]; intro h; exact hc (congrArg BGG.PositiveCE.Mode.color h)
    · simp
  · rw [if_neg hk]
    exact Finset.sum_eq_zero fun c _ => by
      rw [if_neg]; intro h; exact hk (congrArg BGG.PositiveCE.Mode.index h)

/-- A homogeneous derivation is the locally finite sum of its elementary fields. -/
theorem rep_eq {p : ℕ} {D : Module.End ℂ W} (hD : HomDer p D) :
    D = lsum (repFam D) (kills_repFam D).evZero := by
  apply hD.isDer.ext (IsDer.lsum _ (isDer_repFam hD))
  intro g
  cases g with
  | s g =>
    have hlow : Low (g.index + 1) (sig g) := by
      simpa using (Low.sig (Nat.lt_succ_self _) Low.one : Low (g.index + 1) (sig g * 1))
    rw [Gen.elt, lsum_apply_low (kills_repFam D) hlow]
    simp only [repFam_sig]
    rw [Finset.sum_ite_eq' (Finset.range (g.index + 1)), if_pos (Finset.self_mem_range_succ _)]
  | p n =>
    have hlow : Low (n.index + 1) (psi n) := by
      simpa using (Low.psi (Nat.lt_succ_self _) Low.one : Low (n.index + 1) (psi n * 1))
    rw [Gen.elt, lsum_apply_low (kills_repFam D) hlow]
    simp only [repFam_psi]
    rw [Finset.sum_ite_eq' (Finset.range (n.index + 1)), if_pos (Finset.self_mem_range_succ _)]

/-! ## The adjoint family -/

theorem isAdj_dS (g : SMode) : IsAdj (dS g) (lmul (sig g)) := (isAdj_sig g).symm

theorem isAdj_iP (n : PMode) : IsAdj (iP n) (((n.index : ℂ) + 1) • lmul (psi n)) := by
  have h := ((isAdj_psi n).symm.smul ((n.index : ℂ) + 1))
  have hne : (n.index : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have hconj : conj ((n.index : ℂ) + 1) = (n.index : ℂ) + 1 := by
    rw [map_add, map_one, Complex.conj_natCast]
  rw [smul_smul, lamP, mul_one_div_cancel hne, one_smul, hconj] at h
  exact h

/-- The adjoint family built from adjoints `Yσ`, `Yψ` of the multiplications by generator values. -/
def adjFam (Yσ Yψ : ℕ → Fin 3 → Module.End ℂ W) (k : ℕ) : Module.End ℂ W :=
  ∑ b, (lmul (sigOf k b) * Yσ k b + ((k : ℂ) + 1) • (lmul (psiOf k b) * Yψ k b))

theorem isAdj_of_rep {p : ℕ} {D : Module.End ℂ W} (hD : HomDer p D)
    (Yσ Yψ : ℕ → Fin 3 → Module.End ℂ W)
    (hσ : ∀ k b, IsAdj (lmul (D (sigOf k b))) (Yσ k b))
    (hψ : ∀ k b, IsAdj (lmul (D (psiOf k b))) (Yψ k b)) (hev : EvZero (adjFam Yσ Yψ)) :
    IsAdj D (lsum (adjFam Yσ Yψ) hev) := by
  rw [rep_eq hD]
  refine IsAdj.lsum _ _ fun k => IsAdj.sum _ fun b _ => IsAdj.add ?_ ?_
  · exact (hσ k b).comp (isAdj_dS ⟨k, b⟩)
  · have := (hψ k b).comp (isAdj_iP ⟨k, b⟩)
    simp only [smul_mul_assoc] at this
    exact this

/-! ## Adjoints of combinations of generators -/

theorem lmul_sum {ι : Type*} (s : Finset ι) (y : ι → W) : lmul (∑ i ∈ s, y i) = ∑ i ∈ s, lmul (y i) := by
  apply LinearMap.ext; intro x; simp [Finset.sum_mul]

theorem isAdj_lmul_sigs (s : Finset (Fin 3)) (a : Fin 3 → ℂ) (k : Fin 3 → ℕ) :
    IsAdj (lmul (∑ c ∈ s, a c • sigOf (k c) c)) (∑ c ∈ s, conj (a c) • dS ⟨k c, c⟩) := by
  rw [lmul_sum]
  refine IsAdj.sum _ fun c _ => ?_
  rw [lmul_smul]
  exact (isAdj_sig _).smul _

theorem isAdj_lmul_psis (s : Finset (Fin 3)) (a : Fin 3 → ℂ) (k : Fin 3 → ℕ) :
    IsAdj (lmul (∑ c ∈ s, a c • psiOf (k c) c))
      (∑ c ∈ s, (conj (a c) * lamP ⟨k c, c⟩) • iP ⟨k c, c⟩) := by
  rw [lmul_sum]
  refine IsAdj.sum _ fun c _ => ?_
  rw [lmul_smul, mul_smul]
  exact (isAdj_psi _).smul _

theorem conj_epsilon (a b c : Fin 3) : conj (epsilon a b c) = epsilon a b c := by
  unfold epsilon
  split_ifs <;> simp

end KhanSL2.StrongMacdonald
