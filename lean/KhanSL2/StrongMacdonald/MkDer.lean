module

public import KhanSL2.StrongMacdonald.OrderCalculus
public import KhanSL2.ExteriorContraction

@[expose] public section

/-!
# Super-derivations from generator values

The two primitive derivations are the partial derivative `dS g` in an even variable and
the signed contraction `iP m` in an odd variable. A general derivation is the locally
finite sum `Σ fσ g * dS g + Σ fψ m * iP m`.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

open AddMonoidAlgebra (single)

/-! ## Linear maps from values on monomials -/

/-- The linear map with prescribed values on the monomials `single e (monomial s)`. -/
def monoLinear (F : Exp → Finset PMode → W) : W →ₗ[ℂ] W :=
  (Finsupp.lsum ℂ fun e => Finsupp.linearCombination ℂ (F e)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem monoLinear_single (F : Exp → Finset PMode → W) (e : Exp) (u : Ext) :
    monoLinear F (single e u) = Finsupp.linearCombination ℂ (F e) u := by
  change (Finsupp.lsum ℂ fun e => Finsupp.linearCombination ℂ (F e)) (single e u).coeff = _
  rw [AddMonoidAlgebra.coeff_single, Finsupp.lsum_single]

theorem monoLinear_mono (F : Exp → Finset PMode → W) (e : Exp) (s : Finset PMode) :
    monoLinear F (mono e s) = F e s := by
  simp [mono, monoLinear_single, FiniteExterior.monomial]

/-- Two linear maps agreeing on monomials agree. -/
theorem linear_ext_mono {A B : W →ₗ[ℂ] W} (h : ∀ e s, A (mono e s) = B (mono e s)) : A = B := by
  apply LinearMap.ext
  intro x
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single e u =>
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => rw [AddMonoidAlgebra.single_add, map_add, map_add, hu, hv]
    | single s r =>
      have : (single e (Finsupp.single s r) : W) = r • mono e s := by
        simp [mono, FiniteExterior.monomial, AddMonoidAlgebra.smul_single]
      rw [this, map_smul, map_smul, h]

/-! ## The primitive derivations -/

/-- Partial derivative in the even variable `g`. -/
def dS (g : SMode) : Module.End ℂ W :=
  monoLinear fun e s => ((e g : ℕ) : ℂ) • mono (e - Finsupp.single g 1) s

/-- Signed contraction in the odd variable `m`. -/
def iP (m : PMode) : Module.End ℂ W :=
  monoLinear fun e s => single e (FiniteExterior.contraction BGG.PositiveCE.Mode.code m
    (FiniteExterior.monomial s))

theorem dS_single (g : SMode) (e : Exp) (u : Ext) :
    dS g (single e u) = ((e g : ℕ) : ℂ) • single (e - Finsupp.single g 1) u := by
  rw [dS, monoLinear_single]
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, hu, hv, AddMonoidAlgebra.single_add, smul_add]
  | single s r =>
    simp [mono, FiniteExterior.monomial, AddMonoidAlgebra.smul_single, smul_smul, mul_comm]

theorem iP_single (m : PMode) (e : Exp) (u : Ext) :
    iP m (single e u) = single e (FiniteExterior.contraction BGG.PositiveCE.Mode.code m u) := by
  rw [iP, monoLinear_single]
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, hu, hv, map_add, AddMonoidAlgebra.single_add]
  | single s r =>
    simp [FiniteExterior.monomial, AddMonoidAlgebra.smul_single, ← map_smul]

theorem dS_mono (g : SMode) (e : Exp) (t : Finset PMode) :
    dS g (mono e t) = ((e g : ℕ) : ℂ) • mono (e - Finsupp.single g 1) t := by
  rw [mono, dS_single]; rfl

theorem dS_mono_of_not_mem {g : SMode} {e : Exp} (hg : g ∉ e.support) (t : Finset PMode) :
    dS g (mono e t) = 0 := by
  rw [dS_mono, Finsupp.notMem_support_iff.mp hg]
  simp

theorem iP_mono_of_not_mem {m : PMode} (e : Exp) {t : Finset PMode} (hm : m ∉ t) :
    iP m (mono e t) = 0 := by
  rw [mono, iP_single, FiniteExterior.contraction_monomial, if_neg hm]
  simp

theorem sig_mul_mono (h : SMode) (e : Exp) (t : Finset PMode) :
    sig h * mono e t = mono (Finsupp.single h 1 + e) t := by
  rw [mono, sig_mul_single]; rfl

theorem dS_sig_mul (g h : SMode) (x : W) :
    dS g (sig h * x) = (if g = h then x else 0) + sig h * dS g x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]; split <;> abel
  | single e u =>
    rw [sig_mul_single, dS_single, dS_single, mul_smul_comm, sig_mul_single]
    by_cases hgh : g = h
    · subst hgh
      rw [if_pos rfl, Finsupp.add_apply, Finsupp.single_eq_same, add_tsub_cancel_left]
      by_cases he : e g = 0
      · rw [he]; simp
      · have hle : Finsupp.single g 1 ≤ e := by
          rw [Finsupp.single_le_iff]; omega
        rw [← add_tsub_assoc_of_le hle, add_tsub_cancel_left]
        push_cast; rw [add_smul, one_smul, add_comm]
    · rw [if_neg hgh, zero_add, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hgh),
        zero_add]
      by_cases he : e g = 0
      · rw [he]; simp
      · have hle : Finsupp.single g 1 ≤ e := by
          rw [Finsupp.single_le_iff]; omega
        rw [add_tsub_assoc_of_le hle]

theorem dS_psi_mul (g : SMode) (m : PMode) (x : W) : dS g (psi m * x) = psi m * dS g x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]
  | single e u => rw [psi_mul_single, dS_single, dS_single, mul_smul_comm, psi_mul_single]

theorem iP_psi_mul (m n : PMode) (x : W) :
    iP m (psi n * x) = (if m = n then x else 0) - psi n * iP m x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]; split <;> abel
  | single e u =>
    have hc : (FiniteExterior.GeneratorOrder.code : PMode → ℕ) = BGG.PositiveCE.Mode.code := rfl
    rw [psi_mul_single, iP_single, iP_single, psi_mul_single, FiniteExterior.mul_def,
      FiniteExterior.mul_def]
    simp only [hc]
    rw [FiniteExterior.contraction_generator_wedge _ BGG.PositiveCE.Mode.code_injective,
      AddMonoidAlgebra.single_sub]
    split <;> simp

theorem iP_sig_mul (m : PMode) (h : SMode) (x : W) : iP m (sig h * x) = sig h * iP m x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]
  | single e u => rw [sig_mul_single, iP_single, iP_single, sig_mul_single]

theorem dS_one (g : SMode) : dS g 1 = 0 := by
  rw [one_eq_mono, dS_mono]; simp

theorem iP_one (m : PMode) : iP m 1 = 0 := by
  rw [one_eq_mono]; exact iP_mono_of_not_mem 0 (Finset.notMem_empty m)

theorem dS_sig (g h : SMode) : dS g (sig h) = if g = h then 1 else 0 := by
  simpa [dS_one] using dS_sig_mul g h 1

theorem dS_psi (g : SMode) (m : PMode) : dS g (psi m) = 0 := by
  simpa [dS_one] using dS_psi_mul g m 1

theorem iP_psi (m n : PMode) : iP m (psi n) = if m = n then 1 else 0 := by
  simpa [iP_one] using iP_psi_mul m n 1

theorem iP_sig (m : PMode) (h : SMode) : iP m (sig h) = 0 := by
  simpa [iP_one] using iP_sig_mul m h 1

/-! ## Derivations from generator values -/

/-- The super-derivation with values `fσ` on even and `fψ` on odd generators. -/
def mkDer (fσ : SMode → W) (fψ : PMode → W) : Module.End ℂ W :=
  monoLinear fun e t =>
    (∑ g ∈ e.support, fσ g * dS g (mono e t)) + ∑ m ∈ t, fψ m * iP m (mono e t)

/-- The defining sums may be taken over any finite supersets of the supports. -/
theorem mkDer_mono_eq (fσ : SMode → W) (fψ : PMode → W) (e : Exp) (t : Finset PMode)
    (M : Finset SMode) (hM : e.support ⊆ M) (N : Finset PMode) (hN : t ⊆ N) :
    mkDer fσ fψ (mono e t) =
      (∑ g ∈ M, fσ g * dS g (mono e t)) + ∑ m ∈ N, fψ m * iP m (mono e t) := by
  rw [mkDer, monoLinear_mono]
  congr 1
  · apply Finset.sum_subset hM
    intro g _ hg
    rw [dS_mono_of_not_mem hg, mul_zero]
  · apply Finset.sum_subset hN
    intro m _ hm
    rw [iP_mono_of_not_mem e hm, mul_zero]

theorem parity_iterate_add (n : ℕ) (x y : W) :
    parity^[n] (x + y) = parity^[n] x + parity^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

theorem parity_iterate_smul (n : ℕ) (r : ℂ) (x : W) : parity^[n] (r • x) = r • parity^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_smul]

theorem parity_iterate_mul (n : ℕ) (x y : W) :
    parity^[n] (x * y) = parity^[n] x * parity^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

/-- A linear map satisfying the Leibniz rule against generators is a derivation. -/
theorem isDer_of_gen {p : ℕ} {D : Module.End ℂ W} (h1 : D 1 = 0)
    (hgen : ∀ (g : Gen) (x : W),
      D (g.elt * x) = D g.elt * x + ((-1 : ℂ) ^ (p * g.par)) • (g.elt * D x)) : IsDer p D := by
  intro x y
  refine induction_gen (P := fun x => D (x * y) = D x * y + (parity^[p] x) * D y) ?_ ?_ ?_ ?_ ?_ ?_ x
  · simp
  · rw [one_mul, h1, zero_mul, zero_add, parity_iterate_one, one_mul]
  · intro x x' hx hx'
    rw [add_mul, map_add, hx, hx', map_add, parity_iterate_add]
    noncomm_ring
  · intro r x hx
    rw [smul_mul_assoc, map_smul, hx, map_smul, parity_iterate_smul, smul_add, smul_mul_assoc,
      smul_mul_assoc]
  · intro g x hx
    have := hgen (.s g) (x * y)
    simp only [Gen.elt, Gen.par, mul_zero, pow_zero, one_smul] at this
    have hx2 := hgen (.s g) x
    simp only [Gen.elt, Gen.par, mul_zero, pow_zero, one_smul] at hx2
    rw [mul_assoc, this, hx, hx2]
    have hg := parity_iterate_gen p (.s g)
    simp only [Gen.elt, Gen.par, mul_zero, pow_zero, one_smul] at hg
    rw [parity_iterate_mul, hg]
    noncomm_ring
  · intro m x hx
    have := hgen (.p m) (x * y)
    simp only [Gen.elt, Gen.par, mul_one] at this
    have hx2 := hgen (.p m) x
    simp only [Gen.elt, Gen.par, mul_one] at hx2
    rw [mul_assoc, this, hx, hx2]
    have hg := parity_iterate_gen p (.p m)
    simp only [Gen.elt, Gen.par, mul_one] at hg
    rw [parity_iterate_mul, hg]
    simp only [mul_add, add_mul, smul_mul_assoc, mul_assoc, smul_add]
    abel

/-- The superset formula for arbitrary exterior coefficients. -/
theorem mkDer_single_eq (fσ : SMode → W) (fψ : PMode → W) (e : Exp) (u : Ext)
    (M : Finset SMode) (hM : e.support ⊆ M) (N : Finset PMode) (hN : ∀ t ∈ u.support, t ⊆ N) :
    mkDer fσ fψ (single e u) =
      (∑ g ∈ M, fσ g * dS g (single e u)) + ∑ m ∈ N, fψ m * iP m (single e u) := by
  have hu : u = ∑ t ∈ u.support, u t • FiniteExterior.monomial t := by
    simpa only [Finsupp.sum, FiniteExterior.monomial, Finsupp.smul_single, smul_eq_mul, mul_one]
      using (Finsupp.sum_single u).symm
  have hsplit : (single e u : W) = ∑ t ∈ u.support, u t • mono e t := by
    have h2 := congrArg (AddMonoidAlgebra.lsingle (R := ℂ) (M := Exp) e) hu
    rw [map_sum] at h2
    simpa [mono, AddMonoidAlgebra.smul_single] using h2
  rw [hsplit]
  simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm (s := M), Finset.sum_comm (s := N), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [mkDer_mono_eq fσ fψ e t M hM N (hN t ht), smul_add, Finset.smul_sum, Finset.smul_sum]

theorem mkDer_sig (fσ : SMode → W) (fψ : PMode → W) (h : SMode) : mkDer fσ fψ (sig h) = fσ h := by
  have hs : sig h = mono (Finsupp.single h 1) ∅ := rfl
  rw [hs, mkDer_mono_eq fσ fψ _ _ {h} Finsupp.support_single_subset ∅ subset_rfl, ← hs]
  simp [dS_sig]

theorem mkDer_psi (fσ : SMode → W) (fψ : PMode → W) (n : PMode) : mkDer fσ fψ (psi n) = fψ n := by
  have hs : psi n = mono 0 {n} := rfl
  rw [hs, mkDer_mono_eq fσ fψ _ _ ∅ (by simp) {n} subset_rfl, ← hs]
  simp [iP_psi]

theorem mkDer_one (fσ : SMode → W) (fψ : PMode → W) : mkDer fσ fψ 1 = 0 := by
  rw [one_eq_mono, mkDer_mono_eq fσ fψ _ _ ∅ (by simp) ∅ subset_rfl]
  simp

/-- `mkDer` is a super-derivation of parity `p` when the generator values are homogeneous. -/
theorem mkDer_isDer {p : ℕ} (fσ : SMode → W) (fψ : PMode → W) (hσ : ∀ g, IsPar p (fσ g))
    (hψ : ∀ m, IsPar (p + 1) (fψ m)) : IsDer p (mkDer fσ fψ) := by
  apply isDer_of_gen (mkDer_one fσ fψ)
  intro g
  have hlin : (mkDer fσ fψ).comp (lmul g.elt) =
      (lmul (mkDer fσ fψ g.elt)) + ((-1 : ℂ) ^ (p * g.par)) • ((lmul g.elt).comp (mkDer fσ fψ)) := by
    apply linear_ext_mono
    intro e t
    simp only [LinearMap.comp_apply, lmul_apply, LinearMap.add_apply, LinearMap.smul_apply]
    cases g with
    | s h =>
      simp only [Gen.elt, Gen.par, mul_zero, pow_zero, one_smul, mkDer_sig]
      rw [sig_mul_mono, mkDer_mono_eq fσ fψ _ t (insert h e.support)
          (by intro x hx; rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hx
              rw [Finset.mem_insert, Finsupp.mem_support_iff]
              by_cases hxh : x = h
              · exact Or.inl hxh
              · right; rwa [Finsupp.single_apply, if_neg (Ne.symm hxh), zero_add] at hx) t subset_rfl,
        mkDer_mono_eq fσ fψ e t (insert h e.support) (Finset.subset_insert _ _) t subset_rfl,
        ← sig_mul_mono]
      simp only [dS_sig_mul, iP_sig_mul, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_insert_self, ↓reduceIte, Finset.mul_sum]
      rw [add_assoc]
      congr 1
      congr 1
      · apply Finset.sum_congr rfl; intro g _
        rw [← mul_assoc, ← mul_assoc, (sig_commute h (fσ g)).symm]
      · apply Finset.sum_congr rfl; intro m _
        rw [← mul_assoc, ← mul_assoc, (sig_commute h (fψ m)).symm]
    | p n =>
      simp only [Gen.elt, Gen.par, mul_one, mkDer_psi]
      have hsupp : ∀ t' ∈ (FiniteExterior.generator n * FiniteExterior.monomial t : Ext).support,
          t' ⊆ insert n t := by
        intro t' ht'
        rw [FiniteExterior.mul_def] at ht'
        have := FiniteExterior.wedge_generator_monomial_eq FiniteExterior.GeneratorOrder.code n t
        rw [this] at ht'
        split at ht'
        · simp at ht'
        · rw [FiniteExterior.monomial, Finsupp.smul_single, Finsupp.support_single_ne_zero _
            (by simp)] at ht'
          rw [Finset.mem_singleton.mp ht']
      have hx : psi n * mono e t = single e (FiniteExterior.generator n * FiniteExterior.monomial t) := by
        rw [mono, psi_mul_single]
      rw [hx, mkDer_single_eq fσ fψ e _ e.support subset_rfl (insert n t) hsupp, ← hx,
        mkDer_mono_eq fσ fψ e t e.support subset_rfl (insert n t) (Finset.subset_insert _ _)]
      simp only [dS_psi_mul, iP_psi_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_insert_self, ↓reduceIte, mul_add, smul_add, Finset.mul_sum,
        Finset.smul_sum]
      have h1 : ∀ g, fσ g * (psi n * dS g (mono e t)) =
          ((-1 : ℂ) ^ p) • (psi n * (fσ g * dS g (mono e t))) := by
        intro g
        rw [← mul_assoc, mul_psi, hσ g]
        simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
      have h2 : ∀ m, fψ m * (psi n * iP m (mono e t)) =
          -(((-1 : ℂ) ^ p) • (psi n * (fψ m * iP m (mono e t)))) := by
        intro m
        rw [← mul_assoc, mul_psi, hψ m]
        simp only [mul_smul_comm, smul_mul_assoc, mul_assoc, pow_succ, mul_neg, mul_one, neg_smul,
          neg_mul]
      simp only [h1, h2, Finset.sum_neg_distrib, sub_neg_eq_add]
      abel
  intro x
  exact LinearMap.congr_fun hlin x

end KhanSL2.StrongMacdonald
