module

public import KhanSL2.StrongMacdonald.Subst
public import KhanSL2.StrongMacdonald.ExpDer
public import KhanSL2.StrongMacdonald.JetAlg

@[expose] public section

/-!
# Loop operators, linear spans and evaluation at points

`Lop a 0 = Y a` and `Lop a (i+1) = X i a` are the actions of `ξ_a z^m` on `W`. On the even
generators both act by `σ^b(-k) ↦ Σ_c ε_abc σ^c(-(k-m))`; on the odd generators in the
rescaled variables `ψ̃ = (k+1)ψ` they act by the same formula. A finite combination
`opA N Γ = Σ_{m<N} Σ_a Γ_{m,a} Lop a m` therefore acts on points by `cross Γ`.
-/

noncomputable section
open scoped BigOperators
open Complex PowerSeries

namespace KhanSL2.StrongMacdonald

/-! ## The loop operators -/

/-- The action of `ξ_a z^m`. -/
def Lop (a : Fin 3) : ℕ → Module.End ℂ W
  | 0 => Y a
  | i + 1 => X i a

theorem homDer_Lop (a : Fin 3) : ∀ m, HomDer 0 (Lop a m)
  | 0 => homDer_Y a
  | i + 1 => homDer_X i a

theorem Lop_apply_eq_zero {x : W} (hY : ∀ c, Y c x = 0) (hX : ∀ i a, X i a x = 0) (a : Fin 3) :
    ∀ m, Lop a m x = 0
  | 0 => hY a
  | i + 1 => hX i a

theorem Lop_sigOf (a b : Fin 3) (m k : ℕ) :
    Lop a m (sigOf k b) = if m ≤ k then ∑ c, epsilon a b c • sigOf (k - m) c else 0 := by
  cases m with
  | zero => simp [Lop, Y]
  | succ i => simp [Lop, X]

theorem Lop_psiOf (a b : Fin 3) (m k : ℕ) :
    Lop a m (psiOf k b) = if m ≤ k then
      ∑ c, (epsilon a b c * ((((k - m : ℕ) : ℂ) + 1) / ((k : ℂ) + 1))) • psiOf (k - m) c
      else 0 := by
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  cases m with
  | zero =>
    simp only [Lop, Y, LinearMap.add_apply, Rlow_psiOf, adLow_psiOf, zero_add, Nat.zero_le,
      if_true, Nat.sub_zero, div_self hk, mul_one]
  | succ i =>
    simp only [Lop, X, LinearMap.sub_apply, Rlow_psiOf, adUpDag_psiOf, zero_sub]
    split_ifs with h
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← neg_smul, epsilon_swap_right a c b, show k + 1 - (i + 1) = (k - (i + 1)) + 1 by omega]
      push_cast
      ring_nf
    · simp

/-! ## Linear spans of generators -/

/-- Linear combinations of even generators. -/
def SigLin : Submodule ℂ W := Submodule.span ℂ (Set.range sig)

/-- Linear combinations of odd generators. -/
def PsiLin : Submodule ℂ W := Submodule.span ℂ (Set.range psi)

theorem sig_mem_sigLin (g : SMode) : sig g ∈ SigLin := Submodule.subset_span ⟨g, rfl⟩

theorem psi_mem_psiLin (n : PMode) : psi n ∈ PsiLin := Submodule.subset_span ⟨n, rfl⟩

theorem sigLin_of_forall {P : Module.End ℂ W} (h : ∀ g, P (sig g) ∈ SigLin) {y : W}
    (hy : y ∈ SigLin) : P y ∈ SigLin := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨g, rfl⟩ := hy; exact h g
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact SigLin.add_mem hy hz
  | smul r y _ hy => rw [map_smul]; exact SigLin.smul_mem r hy

theorem psiLin_of_forall {P : Module.End ℂ W} (h : ∀ n, P (psi n) ∈ PsiLin) {y : W}
    (hy : y ∈ PsiLin) : P y ∈ PsiLin := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨g, rfl⟩ := hy; exact h g
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact PsiLin.add_mem hy hz
  | smul r y _ hy => rw [map_smul]; exact PsiLin.smul_mem r hy

theorem Lop_sig_mem (a : Fin 3) (m : ℕ) (g : SMode) : Lop a m (sig g) ∈ SigLin := by
  obtain ⟨k, b⟩ := g
  rw [show sig ⟨k, b⟩ = sigOf k b from rfl, Lop_sigOf]
  split_ifs
  · exact Submodule.sum_mem _ fun c _ => SigLin.smul_mem _ (sig_mem_sigLin _)
  · exact SigLin.zero_mem

theorem Lop_psi_mem (a : Fin 3) (m : ℕ) (n : PMode) : Lop a m (psi n) ∈ PsiLin := by
  obtain ⟨k, b⟩ := n
  rw [show psi ⟨k, b⟩ = psiOf k b from rfl, Lop_psiOf]
  split_ifs
  · exact Submodule.sum_mem _ fun c _ => PsiLin.smul_mem _ (psi_mem_psiLin _)
  · exact PsiLin.zero_mem

/-! ## The Euler contraction and the de Rham differential -/

/-- The Euler contraction `ψ̃^a(k) ↦ σ^a(-k)`, i.e. `ψ⟨k,a⟩ ↦ (k+1)⁻¹ σ⟨k,a⟩`. -/
def kap : Module.End ℂ W :=
  mkDer (fun _ => 0) (fun n => ((n.index : ℂ) + 1)⁻¹ • sig ⟨n.index, n.color⟩)

/-- The de Rham differential `σ^a(-k) ↦ ψ̃^a(k)`. -/
def dRham : Module.End ℂ W :=
  mkDer (fun g => ((g.index : ℂ) + 1) • psi ⟨g.index, g.color⟩) (fun _ => 0)

theorem homDer_kap : HomDer 1 kap :=
  mkDer_homDer _ _ (fun _ => IsPar.zero _)
    (fun _ => ((isPar_sig _).smul _).congr (by norm_num))

theorem kap_sig (g : SMode) : kap (sig g) = 0 := mkDer_sig _ _ _

theorem kap_psi (n : PMode) : kap (psi n) = ((n.index : ℂ) + 1)⁻¹ • sig ⟨n.index, n.color⟩ :=
  mkDer_psi _ _ _

theorem dRham_sig (g : SMode) : dRham (sig g) = ((g.index : ℂ) + 1) • psi ⟨g.index, g.color⟩ :=
  mkDer_sig _ _ _

theorem kap_eq_zero_of_sigLin {y : W} (hy : y ∈ SigLin) : kap y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨g, rfl⟩ := hy; exact kap_sig g
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul r y _ hy => rw [map_smul, hy, smul_zero]

theorem dRham_kap_of_psiLin {y : W} (hy : y ∈ PsiLin) : dRham (kap y) = y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, rfl⟩ := hy
    rw [kap_psi, map_smul, dRham_sig, smul_smul, inv_mul_cancel₀ (Nat.cast_add_one_ne_zero _),
      one_smul]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul r y _ hy => rw [map_smul, map_smul, hy]

theorem eq_zero_of_kap_eq_zero {y : W} (hy : y ∈ PsiLin) (h : kap y = 0) : y = 0 := by
  rw [← dRham_kap_of_psiLin hy, h, map_zero]

theorem Lop_comm_kap (a : Fin 3) (m : ℕ) : Lop a m * kap = kap * Lop a m := by
  have hD := HomDer.comm_even homDer_kap (homDer_Lop a m)
  have h0 : kap * Lop a m - Lop a m * kap = 0 := by
    apply hD.isDer.ext (IsDer.zero 1)
    intro g
    cases g with
    | s g =>
      show kap (Lop a m (sig g)) - Lop a m (kap (sig g)) = 0
      rw [kap_eq_zero_of_sigLin (Lop_sig_mem a m g), kap_sig, map_zero, sub_zero]
    | p n =>
      obtain ⟨k, b⟩ := n
      show kap (Lop a m (psiOf k b)) - Lop a m (kap (psiOf k b)) = 0
      rw [psiOf, kap_psi, map_smul, show sig ⟨k, b⟩ = sigOf k b from rfl, Lop_sigOf,
        ← psiOf, Lop_psiOf]
      split_ifs
      · simp only [map_sum, map_smul, psiOf, kap_psi, smul_smul, Finset.smul_sum]
        rw [sub_eq_zero]
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 1
        have h1 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
        have h2 : (((k - m : ℕ) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
        field_simp
      · simp
  rw [sub_eq_zero] at h0
  exact h0.symm

/-! ## Finite combinations of loop operators -/

/-- `Σ_{m<N} Σ_a Γ_{m,a} · (ξ_a z^m)`. -/
def opA (N : ℕ) (Γ : Jet) : Module.End ℂ W :=
  ∑ m ∈ Finset.range N, ∑ a, (coeff m (Γ a)) • Lop a m

theorem homDer_opA (N : ℕ) (Γ : Jet) : HomDer 0 (opA N Γ) :=
  HomDer.sum _ _ fun m _ => HomDer.sum _ _ fun a _ => (homDer_Lop a m).smul _

theorem opA_apply_eq_zero {x : W} (hY : ∀ c, Y c x = 0) (hX : ∀ i a, X i a x = 0)
    (N : ℕ) (Γ : Jet) : opA N Γ x = 0 := by
  simp [opA, Lop_apply_eq_zero hY hX]

theorem opA_sig_mem (N : ℕ) (Γ : Jet) (g : SMode) : opA N Γ (sig g) ∈ SigLin := by
  simp only [opA, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun m _ => Submodule.sum_mem _ fun a _ =>
    SigLin.smul_mem _ (Lop_sig_mem a m g)

theorem opA_psi_mem (N : ℕ) (Γ : Jet) (n : PMode) : opA N Γ (psi n) ∈ PsiLin := by
  simp only [opA, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun m _ => Submodule.sum_mem _ fun a _ =>
    PsiLin.smul_mem _ (Lop_psi_mem a m n)

theorem opA_comm_kap (N : ℕ) (Γ : Jet) : opA N Γ * kap = kap * opA N Γ := by
  simp only [opA, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Lop_comm_kap]

theorem opA_pow_sigLin (N : ℕ) (Γ : Jet) (n : ℕ) {y : W} (hy : y ∈ SigLin) :
    (opA N Γ ^ n) y ∈ SigLin := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact sigLin_of_forall (opA_sig_mem N Γ) ih

theorem opA_pow_psiLin (N : ℕ) (Γ : Jet) (n : ℕ) {y : W} (hy : y ∈ PsiLin) :
    (opA N Γ ^ n) y ∈ PsiLin := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact psiLin_of_forall (opA_psi_mem N Γ) ih

theorem opA_pow_comm_kap (N : ℕ) (Γ : Jet) (n : ℕ) : opA N Γ ^ n * kap = kap * opA N Γ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, opA_comm_kap, ← mul_assoc, ih, mul_assoc]

/-! ## Points as jets -/

/-- The jet of a point. -/
def toJet (pt : SMode → ℂ) : Jet := fun b => PowerSeries.mk fun k => pt ⟨k, b⟩

/-- The point of a jet. -/
def ofJet (P : Jet) : SMode → ℂ := fun g => coeff g.index (P g.color)

@[simp] theorem toJet_ofJet (P : Jet) : toJet (ofJet P) = P := by
  funext b; ext k; simp [toJet, ofJet]

@[simp] theorem ofJet_toJet (pt : SMode → ℂ) : ofJet (toJet pt) = pt := by
  funext g; simp [toJet, ofJet]

theorem coeff_toJet (pt : SMode → ℂ) (b : Fin 3) (k : ℕ) : coeff k (toJet pt b) = pt ⟨k, b⟩ := by
  simp [toJet]

/-! ## Scalars in the exterior algebra -/

/-- The scalar part of an exterior element. -/
def scal (u : Ext) : ℂ := u ∅

theorem scal_algebraMap (c : ℂ) : scal (algebraMap ℂ Ext c) = c := by
  have h1 : (1 : Ext) ∅ = 1 := by
    show (FiniteExterior.monomial ∅ : Ext) ∅ = 1
    simp [FiniteExterior.monomial]
  simp [scal, Algebra.algebraMap_eq_smul_one, h1]

theorem evalAt_sigLin_exists (pt : SMode → ℂ) {y : W} (hy : y ∈ SigLin) :
    ∃ c, evalAt pt y = algebraMap ℂ Ext c := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨g, rfl⟩ := hy; exact ⟨pt g, evalAt_sig _ g⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc⟩ := hy; obtain ⟨d, hd⟩ := hz
    exact ⟨c + d, by rw [map_add, hc, hd, map_add]⟩
  | smul r y _ hy =>
    obtain ⟨c, hc⟩ := hy
    exact ⟨r * c, by rw [map_smul, hc, map_mul, Algebra.smul_def]⟩

theorem evalAt_sigLin (pt : SMode → ℂ) {y : W} (hy : y ∈ SigLin) :
    evalAt pt y = algebraMap ℂ Ext (scal (evalAt pt y)) := by
  obtain ⟨c, hc⟩ := evalAt_sigLin_exists pt hy
  rw [hc, scal_algebraMap]

theorem evalAt_psiLin_mem (pt : SMode → ℂ) {y : W} (hy : y ∈ PsiLin) : evalAt pt y ∈ Deg1 := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨n, rfl⟩ := hy; rw [evalAt_psi]; exact generator_mem_deg1 n
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Deg1.add_mem hy hz
  | smul r y _ hy => rw [map_smul]; exact Deg1.smul_mem r hy

theorem eq_zero_of_sigLin {y : W} (hy : y ∈ SigLin) (h : ∀ pt, scal (evalAt pt y) = 0) :
    y = 0 :=
  eq_zero_of_evalAt_all fun pt => by rw [evalAt_sigLin pt hy, h, map_zero]

/-- The scalar part of the evaluation, as a linear functional. -/
def evScal (pt : SMode → ℂ) : W →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (∅ : Finset PMode)).comp (evalAt pt).toLinearMap

theorem evScal_apply (pt : SMode → ℂ) (y : W) : evScal pt y = scal (evalAt pt y) := rfl

theorem evScal_sigOf (pt : SMode → ℂ) (k : ℕ) (b : Fin 3) : evScal pt (sigOf k b) = pt ⟨k, b⟩ := by
  rw [evScal_apply, sigOf, evalAt_sig, scal_algebraMap]

/-! ## The transpose of `opA` on points -/

theorem sum_range_ite_le_of_vanish {M : Type*} [AddCommMonoid M] (N k : ℕ) (f : ℕ → M)
    (hf : ∀ m, N ≤ m → f m = 0) :
    ∑ m ∈ Finset.range N, (if m ≤ k then f m else 0) = ∑ m ∈ Finset.range (k + 1), f m := by
  have h1 : ∑ m ∈ Finset.range N, (if m ≤ k then f m else 0) =
      ∑ m ∈ Finset.range (N + (k + 1)), (if m ≤ k then f m else 0) := by
    apply Finset.sum_subset
    · intro m hm; simp only [Finset.mem_range] at hm ⊢; omega
    · intro m hm hm'
      simp only [Finset.mem_range, not_lt] at hm'
      rw [hf m hm', ite_self]
  have h2 : ∑ m ∈ Finset.range (k + 1), f m =
      ∑ m ∈ Finset.range (N + (k + 1)), (if m ≤ k then f m else 0) := by
    rw [← Finset.sum_filter]
    congr 1
    ext m; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [h1, h2]

/-- A loop element is *truncated below `N`* if its coefficients of degree `≥ N` vanish. -/
def Trunc (N : ℕ) (Γ : Jet) : Prop := ∀ a m, N ≤ m → coeff m (Γ a) = 0

theorem evScal_opA_sigOf {N : ℕ} {Γ : Jet} (hΓ : Trunc N Γ) (pt : SMode → ℂ) (k : ℕ) (b : Fin 3) :
    evScal pt (opA N Γ (sigOf k b)) = coeff k (jcross Γ (toJet pt) b) := by
  simp only [opA, LinearMap.sum_apply, LinearMap.smul_apply, Lop_sigOf, map_sum, map_smul,
    apply_ite (evScal pt), map_zero, evScal_sigOf, smul_eq_mul, jcross, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_toJet, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_range_ite_le_of_vanish N k _ (fun m hm => by rw [hΓ a m hm, zero_mul])]
  simp only [Finset.mul_sum, Nat.succ_eq_add_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem evalAt_opA_sigLin {N : ℕ} {Γ : Jet} (hΓ : Trunc N Γ) (pt : SMode → ℂ) {y : W}
    (hy : y ∈ SigLin) :
    evScal pt (opA N Γ y) = evScal (ofJet (jcross Γ (toJet pt))) y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨k, b⟩, rfl⟩ := hy
    rw [show sig ⟨k, b⟩ = sigOf k b from rfl, evScal_opA_sigOf hΓ, evScal_sigOf]
    rfl
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, map_add]
  | smul r y _ hy => rw [map_smul, map_smul, hy, map_smul]

theorem evalAt_opA_pow_sigLin {N : ℕ} {Γ : Jet} (hΓ : Trunc N Γ) (n : ℕ) (pt : SMode → ℂ)
    {y : W} (hy : y ∈ SigLin) :
    evScal pt ((opA N Γ ^ n) y) = evScal (ofJet ((jcross Γ)^[n] (toJet pt))) y := by
  induction n generalizing pt with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, evalAt_opA_sigLin hΓ pt (opA_pow_sigLin N Γ n hy),
      ih, toJet_ofJet, ← Function.iterate_succ_apply]

theorem evScal_opA_pow_sigOf {N : ℕ} {Γ : Jet} (hΓ : Trunc N Γ) (n : ℕ) (pt : SMode → ℂ)
    (k : ℕ) (b : Fin 3) :
    evScal pt ((opA N Γ ^ n) (sigOf k b)) = coeff k ((jcross Γ)^[n] (toJet pt) b) := by
  rw [sigOf, evalAt_opA_pow_sigLin hΓ n pt (sig_mem_sigLin _), ← sigOf, evScal_sigOf]
  rfl

/-- Local nilpotency of `opA` from vanishing of the iterated point action. -/
theorem locNil_opA {N : ℕ} {Γ : Jet} (hΓ : Trunc N Γ)
    (h : ∀ k (b : Fin 3), ∃ n, ∀ P : Jet, coeff k ((jcross Γ)^[n] P b) = 0) :
    LocNil (opA N Γ) := by
  have hσ : ∀ k b, ∃ n, (opA N Γ ^ n) (sigOf k b) = 0 := by
    intro k b
    obtain ⟨n, hn⟩ := h k b
    refine ⟨n, eq_zero_of_sigLin (opA_pow_sigLin N Γ n (sig_mem_sigLin _)) fun pt => ?_⟩
    rw [← evScal_apply, evScal_opA_pow_sigOf hΓ, hn]
  apply locNil_of_gen (homDer_opA N Γ).isDer
  intro g
  cases g with
  | s g => obtain ⟨k, b⟩ := g; exact hσ k b
  | p m =>
    obtain ⟨k, b⟩ := m
    obtain ⟨n, hn⟩ := hσ k b
    refine ⟨n, eq_zero_of_kap_eq_zero (opA_pow_psiLin N Γ n (psi_mem_psiLin _)) ?_⟩
    show kap ((opA N Γ ^ n) (psi ⟨k, b⟩)) = 0
    rw [← Module.End.mul_apply, ← opA_pow_comm_kap, Module.End.mul_apply, kap_psi, map_smul]
    erw [hn, smul_zero]

theorem opA_pow_sigOf_eq_zero {N : ℕ} {Γ : Jet} (hΓ : Trunc N Γ) (n k : ℕ) (b : Fin 3)
    (h : ∀ P : Jet, coeff k ((jcross Γ)^[n] P b) = 0) : (opA N Γ ^ n) (sigOf k b) = 0 :=
  eq_zero_of_sigLin (opA_pow_sigLin N Γ n (sig_mem_sigLin _)) fun pt => by
    rw [← evScal_apply, evScal_opA_pow_sigOf hΓ, h]

/-! ## One move -/

/-- The point reached by `exp(opA N Γ)`. -/
def movePt (N : ℕ) (Γ : Jet) (hN : LocNil (opA N Γ)) (pt : SMode → ℂ) : SMode → ℂ :=
  fun g => scal (evalAt pt (expDer (opA N Γ) (homDer_opA N Γ).isDer hN (sig g)))

theorem expDer_opA_sig_mem {N : ℕ} {Γ : Jet} (hN : LocNil (opA N Γ)) (g : SMode) :
    expDer (opA N Γ) (homDer_opA N Γ).isDer hN (sig g) ∈ SigLin := by
  obtain ⟨n, hn⟩ := hN (sig g)
  rw [expDer_apply_of _ hN hn]
  exact Submodule.sum_mem _ fun k _ =>
    SigLin.smul_mem _ (opA_pow_sigLin N Γ k (sig_mem_sigLin g))

theorem evalAt_expDer_opA_psi_mem {N : ℕ} {Γ : Jet} (hN : LocNil (opA N Γ)) (pt : SMode → ℂ)
    (m : PMode) : evalAt pt (expDer (opA N Γ) (homDer_opA N Γ).isDer hN (psi m)) ∈ Deg1 := by
  obtain ⟨n, hn⟩ := hN (psi m)
  rw [expDer_apply_of _ hN hn]
  exact evalAt_psiLin_mem pt (Submodule.sum_mem _ fun k _ =>
    PsiLin.smul_mem _ (opA_pow_psiLin N Γ k (psi_mem_psiLin m)))

/-- Invariance under one move: the value at `pt` is an odd substitution of the value at the
moved point. -/
theorem evalAt_eq_move {x : W} (hY : ∀ c, Y c x = 0) (hX : ∀ i a, X i a x = 0) {N : ℕ}
    {Γ : Jet} (hN : LocNil (opA N Γ)) (pt : SMode → ℂ) :
    ∃ Θ : Ext →ₐ[ℂ] Ext, evalAt pt x = Θ (evalAt (movePt N Γ hN pt) x) := by
  set D := opA N Γ
  have hD := (homDer_opA N Γ).isDer
  have hx : expDer D hD hN x = x := expDer_of_eq_zero hD hN (opA_apply_eq_zero hY hX N Γ)
  have hψ := evalAt_expDer_opA_psi_mem hN pt
  refine ⟨substituteLin _ hψ, ?_⟩
  have key : (evalAt pt).comp (expDer D hD hN) =
      (substituteLin _ hψ).comp (evalAt (movePt N Γ hN pt)) := by
    apply algHom_ext_W
    · intro g
      simp only [AlgHom.comp_apply, evalAt_sig, AlgHom.commutes]
      exact evalAt_sigLin pt (expDer_opA_sig_mem hN g)
    · intro m
      simp only [AlgHom.comp_apply, evalAt_psi, substituteLin_generator]
      rfl
  calc evalAt pt x = ((evalAt pt).comp (expDer D hD hN)) x := by
        rw [AlgHom.comp_apply, hx]
    _ = _ := by rw [key, AlgHom.comp_apply]

theorem movePt_apply {N : ℕ} {Γ : Jet} (hΓ : Trunc N Γ) (hN : LocNil (opA N Γ))
    (pt : SMode → ℂ) (k : ℕ) (b : Fin 3) {K : ℕ} (hK : (opA N Γ ^ K) (sigOf k b) = 0) :
    movePt N Γ hN pt ⟨k, b⟩ =
      ∑ n ∈ Finset.range K, ((n.factorial : ℂ)⁻¹) * coeff k ((jcross Γ)^[n] (toJet pt) b) := by
  rw [movePt, ← evScal_apply, show sig ⟨k, b⟩ = sigOf k b from rfl, expDer_apply_of _ hN hK]
  simp only [map_sum, map_smul, evScal_opA_pow_sigOf hΓ, smul_eq_mul]

theorem coeff_trunc_mul {N k : ℕ} (hk : k < N) (f g : PowerSeries ℂ) :
    coeff k ((trunc N f : PowerSeries ℂ) * g) = coeff k (f * g) := by
  rw [coeff_mul_eq_coeff_trunc_mul_trunc _ _ hk, coeff_mul_eq_coeff_trunc_mul_trunc f g hk,
    trunc_trunc]

/-- `e`-coordinate (doubled) of a point at mode `j`. -/
def eCo (pt : SMode → ℂ) (j : ℕ) : ℂ := pt ⟨j, 0⟩ - I * pt ⟨j, 1⟩

theorem eCo_eq (pt : SMode → ℂ) (j : ℕ) : eCo pt j = coeff j (eTw (toJet pt)) := by
  simp [eCo, eTw, coeff_toJet, coeff_C_mul]

end KhanSL2.StrongMacdonald
