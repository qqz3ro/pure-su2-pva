module

public import KhanSL2.StrongMacdonald.Torus
public import KhanSL2.StrongMacdonald.Project
public import KhanSL2.StrongMacdonald.Generators

@[expose] public section

/-!
# The slice restriction at `A = 1`

`rho1` substitutes the slice `X₀ = ½(1-φ(z))ξ₀ + ½ i(1+φ(z))ξ₁` (that is `e + φ f` in the
normalization of `slicePt 1`), with `φ_k = sigOf k 0` as new even variables, and keeps the odd
variables. Evaluation at `slicePt 1 B` factors through `rho1`.
-/

noncomputable section
open scoped BigOperators
open Complex PowerSeries

namespace KhanSL2.StrongMacdonald

/-! ## Generalities on substitutions -/

theorem substW_parity (fσ : SMode → W) (fψ : PMode → W) (hσ : ∀ g, IsPar 0 (fσ g))
    (hψ : ∀ m, IsPar 1 (fψ m)) (x : W) :
    substW fσ fψ hσ hψ (parity x) = parity (substW fσ fψ hσ hψ x) := by
  have h : (substW fσ fψ hσ hψ).comp parity = parity.comp (substW fσ fψ hσ hψ) := by
    apply algHom_ext_W
    · intro g
      have h1 := hσ g
      simp only [IsPar, pow_zero, one_smul] at h1
      simp [h1]
    · intro m
      have h1 := hψ m
      simp only [IsPar, pow_one, neg_smul, one_smul] at h1
      simp [h1]
  exact congrArg (fun φ => φ x) h

theorem IsPar.substW {q : ℕ} {x : W} (hx : IsPar q x) (fσ : SMode → W) (fψ : PMode → W)
    (hσ : ∀ g, IsPar 0 (fσ g)) (hψ : ∀ m, IsPar 1 (fψ m)) :
    IsPar q (substW fσ fψ hσ hψ x) := by
  unfold IsPar at hx ⊢
  rw [← substW_parity, hx, map_smul]

/-- Two odd derivations along an algebra map `φ` which agree on generators are equal. -/
theorem twisted_ext (φ : W →ₐ[ℂ] W) (F G : W →ₗ[ℂ] W)
    (hF : ∀ x y, F (x * y) = F x * φ y + parity (φ x) * F y)
    (hG : ∀ x y, G (x * y) = G x * φ y + parity (φ x) * G y)
    (hgen : ∀ g : Gen, F g.elt = G g.elt) : F = G := by
  have h1 : ∀ H : W →ₗ[ℂ] W, (∀ x y, H (x * y) = H x * φ y + parity (φ x) * H y) → H 1 = 0 := by
    intro H hH
    have := hH 1 1
    simp only [mul_one, one_mul, map_one] at this
    simpa using this
  apply LinearMap.ext
  intro x
  refine induction_gen (P := fun x => F x = G x) (by simp) (by rw [h1 F hF, h1 G hG]) ?_ ?_ ?_ ?_ x
  · intro x y hx hy; rw [map_add, map_add, hx, hy]
  · intro r x hx; rw [map_smul, map_smul, hx]
  · intro g x hx
    rw [hF, hG, hx]
    have := hgen (.s g)
    simp only [Gen.elt] at this
    rw [this]
  · intro m x hx
    rw [hF, hG, hx]
    have := hgen (.p m)
    simp only [Gen.elt] at this
    rw [this]

/-! ## The slice restriction -/

/-- The constant `[k = 0]` in `W`. -/
def dl (k : ℕ) : W := if k = 0 then 1 else 0

theorem isPar_dl (k : ℕ) : IsPar 0 (dl k) := by
  unfold dl; split_ifs
  · exact isPar_one 0 rfl
  · exact IsPar.zero 0

/-- The slice coordinates: `σ⟨k,0⟩ ↦ ½([k=0] - φ_k)`, `σ⟨k,1⟩ ↦ ½ i([k=0] + φ_k)`,
`σ⟨k,2⟩ ↦ 0`, with `φ_k = sigOf k 0`. -/
def rhoSig (g : SMode) : W :=
  ![(1 / 2 : ℂ) • (dl g.index - sigOf g.index 0), (I / 2) • (dl g.index + sigOf g.index 0), 0]
    g.color

theorem isPar_rhoSig (g : SMode) : IsPar 0 (rhoSig g) := by
  obtain ⟨k, c⟩ := g
  fin_cases c
  · exact ((isPar_dl k).sub (isPar_sig _)).smul _
  · exact ((isPar_dl k).add (isPar_sig _)).smul _
  · exact IsPar.zero 0

/-- The restriction to the slice `A = 1`. -/
def rho1 : W →ₐ[ℂ] W := substW rhoSig psi isPar_rhoSig isPar_psi

@[simp] theorem rho1_sig (g : SMode) : rho1 (sig g) = rhoSig g := substW_sig _ _ _ _ _

@[simp] theorem rho1_psi (m : PMode) : rho1 (psi m) = psi m := substW_psi _ _ _ _ _

theorem rho1_parity (x : W) : rho1 (parity x) = parity (rho1 x) := substW_parity _ _ _ _ x

/-- The point with `φ_k = coeff k B`. -/
def phiPt (B : PowerSeries ℂ) : SMode → ℂ := fun g => if g.color = 0 then coeff g.index B else 0

theorem evalAt_dl (pt : SMode → ℂ) (k : ℕ) : evalAt pt (dl k) = algebraMap ℂ Ext (if k = 0 then 1 else 0) := by
  unfold dl; split_ifs <;> simp

theorem evalAt_single_zero (pt : SMode → ℂ) (u : Ext) :
    evalAt pt (AddMonoidAlgebra.single 0 u) = u := by
  rw [← ofExt_apply, evalAt_ofExt]

/-- Evaluation on the slice `A = 1` factors through `rho1`. -/
theorem evalAt_slicePt_one (B : PowerSeries ℂ) :
    (evalAt (phiPt B)).comp rho1 = evalAt (slicePt 1 B) := by
  apply algHom_ext_W
  · rintro ⟨k, c⟩
    simp only [AlgHom.comp_apply, rho1_sig, evalAt_sig]
    fin_cases c
    · simp [rhoSig, slicePt, ofJet, phiPt, evalAt_dl, sigOf, coeff_C_mul, coeff_C, map_sub,
        Algebra.smul_def, evalAt_single_zero]
    · simp [rhoSig, slicePt, ofJet, phiPt, evalAt_dl, sigOf, coeff_C_mul, coeff_C, map_add,
        Algebra.smul_def, evalAt_single_zero]
      rw [div_eq_inv_mul, map_mul, mul_assoc]
    · simp [rhoSig, slicePt, ofJet]
  · intro m
    simp

/-! ## Transported odd derivations -/

/-- `d_a(-(j+1))†` transported to the slice. -/
def Dp (a : Fin 3) (j : ℕ) : Module.End ℂ W := mkDer (fun _ => 0) (fun n => rho1 (dUd j a (psi n)))

theorem homDer_Dp (a : Fin 3) (j : ℕ) : HomDer 1 (Dp a j) := by
  refine mkDer_homDer _ _ (fun _ => IsPar.zero _) fun n => ?_
  have h := (homDer_dUd j a).2 (.p n)
  simp only [Gen.elt, Gen.par] at h
  exact h.substW _ _ _ _

theorem Dp_sig (a : Fin 3) (j : ℕ) (g : SMode) : Dp a j (sig g) = 0 := mkDer_sig _ _ _

theorem Dp_psi (a : Fin 3) (j : ℕ) (n : PMode) : Dp a j (psi n) = rho1 (dUd j a (psi n)) :=
  mkDer_psi _ _ _

theorem Dp_dl (a : Fin 3) (j k : ℕ) : Dp a j (dl k) = 0 := by
  unfold dl; split_ifs
  · exact (homDer_Dp a j).map_one
  · exact map_zero _

theorem Dp_rhoSig (a : Fin 3) (j : ℕ) (g : SMode) : Dp a j (rhoSig g) = 0 := by
  obtain ⟨k, c⟩ := g
  fin_cases c <;> simp [rhoSig, map_sub, map_add, map_smul, Dp_dl, sigOf, Dp_sig]

theorem Dp_sig_mul (a : Fin 3) (j : ℕ) (g : SMode) (x : W) :
    Dp a j (sig g * x) = sig g * Dp a j x := by
  rw [(homDer_Dp a j).isDer, Dp_sig, zero_mul, zero_add]
  simp

theorem rho1_dUd (a : Fin 3) (j : ℕ) (x : W) : rho1 (dUd j a x) = Dp a j (rho1 x) := by
  have h := twisted_ext rho1 (rho1.toLinearMap ∘ₗ dUd j a) (Dp a j ∘ₗ rho1.toLinearMap)
    (fun x y => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
      rw [(homDer_dUd j a).isDer x y, map_add, map_mul, map_mul, Function.iterate_one,
        rho1_parity])
    (fun x y => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul]
      rw [(homDer_Dp a j).isDer, Function.iterate_one])
    (fun g => by
      cases g with
      | s g =>
        simp only [Gen.elt, LinearMap.comp_apply, AlgHom.toLinearMap_apply, rho1_sig, Dp_rhoSig]
        obtain ⟨k, b⟩ := g
        rw [show sig ⟨k, b⟩ = sigOf k b from rfl, dUd_sigOf, map_zero]
      | p n => simp [Gen.elt, Dp_psi])
  exact congrArg (fun F => F x) h

theorem Dp_psiOf (a : Fin 3) (j k : ℕ) (b : Fin 3) :
    Dp a j (psiOf k b) = if j ≤ k then
      ∑ c, (epsilon a c b * (1 / ((k : ℂ) + 1))) • rhoSig ⟨k - j, c⟩ else 0 := by
  rw [psiOf, Dp_psi, ← psiOf, dUd_psiOf']
  by_cases h : j ≤ k
  · rw [if_pos (by omega), if_pos h, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, sigOf, rho1_sig, show k + 1 - (j + 1) = k - j by omega]
  · rw [if_neg (by omega), if_neg h, map_zero]

/-! ## Adapted odd coordinates on the slice -/

/-- `U_k = (k+1)(ψ⁰_k + iψ¹_k)`. -/
def Uk (k : ℕ) : W := ((k : ℂ) + 1) • (psiOf k 0 + I • psiOf k 1)

/-- `V_k = (k+1)(-ψ⁰_k + iψ¹_k)`. -/
def Vk (k : ℕ) : W := ((k : ℂ) + 1) • (-psiOf k 0 + I • psiOf k 1)

/-- `Z_k = (k+1)ψ²_k`. -/
def Zk (k : ℕ) : W := ((k : ℂ) + 1) • psiOf k 2

/-- `E'_n = U_n + Σ_l φ_l V_{n-l}`, twice the slice restriction of `E(n+1)`. -/
def Ek (n : ℕ) : W := Uk n + ∑ l ∈ Finset.range (n + 1), sigOf l 0 * Vk (n - l)

/-- `U` expressed in the new variables. -/
def Ut (k : ℕ) : W := psiOf k 0 - ∑ l ∈ Finset.range (k + 1), sigOf l 0 * psiOf (k - l) 1

theorem isPar_psiOf_smul (r : ℂ) (k : ℕ) (b : Fin 3) : IsPar 1 (r • psiOf k b) :=
  (isPar_psi _).smul r

theorem isPar_Uk (k : ℕ) : IsPar 1 (Uk k) :=
  ((isPar_psi _).add ((isPar_psi _).smul _)).smul _

theorem isPar_Vk (k : ℕ) : IsPar 1 (Vk k) :=
  ((isPar_psi _).neg.add ((isPar_psi _).smul _)).smul _

theorem isPar_Zk (k : ℕ) : IsPar 1 (Zk k) := (isPar_psi _).smul _

theorem isPar_Ek (n : ℕ) : IsPar 1 (Ek n) :=
  (isPar_Uk n).add (IsPar.sum _ _ fun l _ => ((isPar_sig _).mul (isPar_Vk _)).congr (by omega))

theorem isPar_Ut (k : ℕ) : IsPar 1 (Ut k) :=
  (isPar_psi _).sub (IsPar.sum _ _ fun l _ => ((isPar_sig _).mul (isPar_psi _)).congr (by omega))

/-- New odd generators: `ψ⁰_n ↦ E'_n`, `ψ¹_n ↦ V_n`, `ψ²_n ↦ Z_n`. -/
def psiNew (m : PMode) : W := ![Ek m.index, Vk m.index, Zk m.index] m.color

/-- The old odd generators in terms of the new ones. -/
def psiOld (m : PMode) : W :=
  ![(1 / (2 * ((m.index : ℂ) + 1))) • (Ut m.index - psiOf m.index 1),
    (-I / (2 * ((m.index : ℂ) + 1))) • (Ut m.index + psiOf m.index 1),
    (1 / ((m.index : ℂ) + 1)) • psiOf m.index 2] m.color

theorem isPar_psiNew (m : PMode) : IsPar 1 (psiNew m) := by
  obtain ⟨k, c⟩ := m
  fin_cases c
  · exact isPar_Ek k
  · exact isPar_Vk k
  · exact isPar_Zk k

theorem isPar_psiOld (m : PMode) : IsPar 1 (psiOld m) := by
  obtain ⟨k, c⟩ := m
  fin_cases c
  · exact ((isPar_Ut k).sub (isPar_psi _)).smul _
  · exact ((isPar_Ut k).add (isPar_psi _)).smul _
  · exact (isPar_psi _).smul _

/-- The unimodular change of odd variables. -/
def Psi : W →ₐ[ℂ] W := substW sig psiNew isPar_sig isPar_psiNew

/-- Its inverse. -/
def PsiInv : W →ₐ[ℂ] W := substW sig psiOld isPar_sig isPar_psiOld

@[simp] theorem Psi_sig (g : SMode) : Psi (sig g) = sig g := substW_sig _ _ _ _ _
@[simp] theorem Psi_psi (m : PMode) : Psi (psi m) = psiNew m := substW_psi _ _ _ _ _
@[simp] theorem PsiInv_sig (g : SMode) : PsiInv (sig g) = sig g := substW_sig _ _ _ _ _
@[simp] theorem PsiInv_psi (m : PMode) : PsiInv (psi m) = psiOld m := substW_psi _ _ _ _ _

theorem Psi_psiOf (k : ℕ) (b : Fin 3) : Psi (psiOf k b) = psiNew ⟨k, b⟩ := Psi_psi _

theorem PsiInv_psiOf (k : ℕ) (b : Fin 3) : PsiInv (psiOf k b) = psiOld ⟨k, b⟩ := PsiInv_psi _

theorem Psi_sigOf (k : ℕ) (b : Fin 3) : Psi (sigOf k b) = sigOf k b := Psi_sig _

theorem PsiInv_sigOf (k : ℕ) (b : Fin 3) : PsiInv (sigOf k b) = sigOf k b := PsiInv_sig _

theorem Psi_Ut (k : ℕ) : Psi (Ut k) = Uk k := by
  simp only [Ut, map_sub, map_sum, map_mul, Psi_psiOf, Psi_sigOf, psiNew, Ek]
  simp

theorem PsiInv_Uk (k : ℕ) : PsiInv (Uk k) = Ut k := by
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  simp only [Uk, map_smul, map_add, PsiInv_psiOf, psiOld]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  match_scalars <;> field_simp <;> ring_nf <;> simp [I_sq]; norm_num

theorem PsiInv_Vk (k : ℕ) : PsiInv (Vk k) = psiOf k 1 := by
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  simp only [Vk, map_smul, map_add, map_neg, PsiInv_psiOf, psiOld]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  match_scalars <;> field_simp <;> ring_nf <;> simp [I_sq]; norm_num

theorem Psi_PsiInv (x : W) : Psi (PsiInv x) = x := by
  have h : Psi.comp PsiInv = AlgHom.id ℂ W := by
    apply algHom_ext_W
    · intro g; simp
    · rintro ⟨k, c⟩
      have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
      simp only [AlgHom.comp_apply, PsiInv_psi, AlgHom.id_apply]
      fin_cases c
      · simp only [psiOld, Fin.zero_eta, Matrix.cons_val_zero, map_smul, map_sub, Psi_Ut,
          Psi_psiOf, psiNew, Matrix.cons_val_one, Uk, Vk]
        rw [show psi ⟨k, 0⟩ = psiOf k 0 from rfl]
        match_scalars <;> field_simp <;> ring
      · simp only [psiOld, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, map_smul,
          map_add, Psi_Ut, Psi_psiOf, psiNew, Uk, Vk]
        rw [show psi ⟨k, 1⟩ = psiOf k 1 from rfl]
        match_scalars <;> field_simp <;> ring_nf; simp [I_sq]
      · simp only [psiOld, Fin.reduceFinMk, Matrix.cons_val, map_smul, Psi_psiOf, psiNew, Zk]
        rw [show psi ⟨k, 2⟩ = psiOf k 2 from rfl, smul_smul, one_div, inv_mul_cancel₀ hk,
          one_smul]
  exact congrArg (fun φ => φ x) h

theorem PsiInv_Psi (x : W) : PsiInv (Psi x) = x := by
  have h : PsiInv.comp Psi = AlgHom.id ℂ W := by
    apply algHom_ext_W
    · intro g; simp
    · rintro ⟨k, c⟩
      have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
      simp only [AlgHom.comp_apply, Psi_psi, AlgHom.id_apply]
      fin_cases c
      · simp only [psiNew, Fin.zero_eta, Matrix.cons_val_zero, Ek, map_add, map_sum, map_mul,
          PsiInv_Uk, PsiInv_Vk, PsiInv_sigOf, Ut]
        rw [show psi ⟨k, 0⟩ = psiOf k 0 from rfl]
        abel
      · simp only [psiNew, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, PsiInv_Vk]
        rfl
      · simp only [psiNew, Fin.reduceFinMk, Matrix.cons_val, Zk, map_smul, PsiInv_psiOf, psiOld]
        rw [show psi ⟨k, 2⟩ = psiOf k 2 from rfl, smul_smul, one_div, mul_inv_cancel₀ hk,
          one_smul]
  exact congrArg (fun φ => φ x) h

theorem Psi_injective : Function.Injective Psi := fun x y h => by
  rw [← PsiInv_Psi x, h, PsiInv_Psi]

/-! ## The transported derivations in the new coordinates -/

theorem Psi_parity (x : W) : Psi (parity x) = parity (Psi x) := substW_parity _ _ _ _ x

theorem rhoSig_zero (k : ℕ) : rhoSig ⟨k, 0⟩ = (1 / 2 : ℂ) • (dl k - sigOf k 0) := rfl
theorem rhoSig_one (k : ℕ) : rhoSig ⟨k, 1⟩ = (I / 2) • (dl k + sigOf k 0) := rfl
theorem rhoSig_two (k : ℕ) : rhoSig ⟨k, 2⟩ = 0 := rfl

section Dp2

variable (j : ℕ)

theorem Dp2_psiOf_zero (k : ℕ) :
    Dp 2 j (psiOf k 0) = if j ≤ k then (-(1 / ((k : ℂ) + 1))) • rhoSig ⟨k - j, 1⟩ else 0 := by
  rw [Dp_psiOf]; split_ifs <;> simp [Fin.sum_univ_three, epsilon]

theorem Dp2_psiOf_one (k : ℕ) :
    Dp 2 j (psiOf k 1) = if j ≤ k then (1 / ((k : ℂ) + 1)) • rhoSig ⟨k - j, 0⟩ else 0 := by
  rw [Dp_psiOf]; split_ifs <;> simp [Fin.sum_univ_three, epsilon]

theorem Dp2_psiOf_two (k : ℕ) : Dp 2 j (psiOf k 2) = 0 := by
  rw [Dp_psiOf]; split_ifs <;> simp [Fin.sum_univ_three, epsilon]

theorem Dp2_Vk (k : ℕ) : Dp 2 j (Vk k) = if j ≤ k then I • dl (k - j) else 0 := by
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  simp only [Vk, map_smul, map_add, map_neg, Dp2_psiOf_zero, Dp2_psiOf_one]
  split_ifs
  · simp only [rhoSig_zero, rhoSig_one]
    match_scalars <;> field_simp <;> ring
  · simp

theorem Dp2_Uk (k : ℕ) : Dp 2 j (Uk k) = if j ≤ k then (-I) • sigOf (k - j) 0 else 0 := by
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  simp only [Uk, map_smul, map_add, Dp2_psiOf_zero, Dp2_psiOf_one]
  split_ifs
  · simp only [rhoSig_zero, rhoSig_one]
    match_scalars <;> field_simp <;> ring
  · simp

theorem Dp2_Zk (k : ℕ) : Dp 2 j (Zk k) = 0 := by
  rw [Zk, map_smul, Dp2_psiOf_two, smul_zero]

theorem Dp2_Ek (n : ℕ) : Dp 2 j (Ek n) = 0 := by
  rw [Ek, map_add, map_sum]
  simp only [sigOf, Dp_sig_mul, Dp2_Vk, Dp2_Uk, mul_ite, mul_zero]
  have hsum : ∑ l ∈ Finset.range (n + 1),
      (if j ≤ n - l then sig ⟨l, 0⟩ * I • dl (n - l - j) else 0) =
      if j ≤ n then I • sig ⟨n - j, 0⟩ else 0 := by
    rw [Finset.sum_eq_single (n - j)]
    · split_ifs with h1 h2 h2
      · rw [show n - (n - j) - j = 0 by omega, dl, if_pos rfl, mul_smul_comm, mul_one]
      · omega
      · omega
      · rfl
    · intro l hl hl'
      have := Finset.mem_range.mp hl
      split_ifs with h
      · rw [dl, if_neg (by omega), smul_zero, mul_zero]
      · rfl
    · intro h
      simp only [Finset.mem_range, not_lt] at h
      rw [if_neg (by omega)]
  rw [hsum]
  split_ifs
  · rw [neg_smul, neg_add_cancel]
  · rw [add_zero]

theorem Dp2_Psi (x : W) : Dp 2 j (Psi x) = Psi ((I • iP ⟨j, 1⟩) x) := by
  have h := twisted_ext Psi (Dp 2 j ∘ₗ Psi.toLinearMap) (Psi.toLinearMap ∘ₗ (I • iP ⟨j, 1⟩))
    (fun x y => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul]
      rw [(homDer_Dp 2 j).isDer, Function.iterate_one])
    (fun x y => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply, map_smul]
      rw [(iP_homDer ⟨j, 1⟩).isDer x y, Function.iterate_one, map_add, map_mul, map_mul,
        Psi_parity, smul_add, smul_mul_assoc, mul_smul_comm])
    (fun g => by
      cases g with
      | s g => simp [Gen.elt, Dp_sig, iP_sig]
      | p n =>
        obtain ⟨k, c⟩ := n
        simp only [Gen.elt, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Psi_psi,
          LinearMap.smul_apply, iP_psi]
        fin_cases c
        · simp [psiNew, Dp2_Ek]
        · simp only [psiNew, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Dp2_Vk]
          by_cases hkj : k = j
          · subst hkj; simp [dl]
          · rw [if_neg (show ¬ (⟨j, 1⟩ : PMode) = ⟨k, 1⟩ from fun h => hkj
              (congrArg BGG.PositiveCE.Mode.index h).symm)]
            split_ifs
            · rw [dl, if_neg (by omega)]; simp
            · simp
        · simp [psiNew, Dp2_Zk])
  exact congrArg (fun F => F x) h

end Dp2

section DpF

variable (j : ℕ)

/-- The transported `f`-direction: `-D_0 + i D_1`. -/
def DpF : Module.End ℂ W := -Dp 0 j + I • Dp 1 j

theorem homDer_DpF : HomDer 1 (DpF j) := (homDer_Dp 0 j).neg.add ((homDer_Dp 1 j).smul I)

theorem DpF_sig (g : SMode) : DpF j (sig g) = 0 := by
  simp [DpF, Dp_sig]

theorem DpF_sig_mul (g : SMode) (x : W) : DpF j (sig g * x) = sig g * DpF j x := by
  rw [(homDer_DpF j).isDer, DpF_sig, zero_mul, zero_add]
  simp

theorem DpF_psiOf_zero (k : ℕ) : DpF j (psiOf k 0) = 0 := by
  simp only [DpF, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, Dp_psiOf]
  split_ifs <;> simp [Fin.sum_univ_three, epsilon, rhoSig_two]

theorem DpF_psiOf_one (k : ℕ) : DpF j (psiOf k 1) = 0 := by
  simp only [DpF, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, Dp_psiOf]
  split_ifs <;> simp [Fin.sum_univ_three, epsilon, rhoSig_two]

theorem DpF_psiOf_two (k : ℕ) :
    DpF j (psiOf k 2) = if j ≤ k then (-I / ((k : ℂ) + 1)) • dl (k - j) else 0 := by
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  simp only [DpF, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, Dp_psiOf]
  split_ifs
  · simp only [Fin.sum_univ_three, epsilon]
    simp only [rhoSig_zero, rhoSig_one, rhoSig_two]
    simp
    match_scalars <;> field_simp <;> ring
  · simp

theorem DpF_Uk (k : ℕ) : DpF j (Uk k) = 0 := by
  simp [Uk, DpF_psiOf_zero, DpF_psiOf_one]

theorem DpF_Vk (k : ℕ) : DpF j (Vk k) = 0 := by
  simp [Vk, DpF_psiOf_zero, DpF_psiOf_one]

theorem DpF_Ek (n : ℕ) : DpF j (Ek n) = 0 := by
  simp [Ek, sigOf, DpF_sig_mul, DpF_Uk, DpF_Vk]

theorem DpF_Zk (k : ℕ) : DpF j (Zk k) = if j ≤ k then (-I) • dl (k - j) else 0 := by
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [Zk, map_smul, DpF_psiOf_two]
  split_ifs
  · rw [smul_smul, mul_div_cancel₀ _ hk]
  · rw [smul_zero]

theorem DpF_Psi (x : W) : DpF j (Psi x) = Psi (((-I) • iP ⟨j, 2⟩) x) := by
  have h := twisted_ext Psi (DpF j ∘ₗ Psi.toLinearMap) (Psi.toLinearMap ∘ₗ ((-I) • iP ⟨j, 2⟩))
    (fun x y => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul]
      rw [(homDer_DpF j).isDer, Function.iterate_one])
    (fun x y => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply, map_smul]
      rw [(iP_homDer ⟨j, 2⟩).isDer x y, Function.iterate_one, map_add, map_mul, map_mul,
        Psi_parity, smul_add, smul_mul_assoc, mul_smul_comm])
    (fun g => by
      cases g with
      | s g => simp [Gen.elt, DpF_sig, iP_sig]
      | p n =>
        obtain ⟨k, c⟩ := n
        simp only [Gen.elt, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Psi_psi,
          LinearMap.smul_apply, iP_psi]
        fin_cases c
        · simp [psiNew, DpF_Ek]
        · simp [psiNew, DpF_Vk]
        · simp only [psiNew, Fin.reduceFinMk, Matrix.cons_val, DpF_Zk]
          by_cases hkj : k = j
          · subst hkj; simp [dl]
          · rw [if_neg (show ¬ (⟨j, 2⟩ : PMode) = ⟨k, 2⟩ from fun h => hkj
              (congrArg BGG.PositiveCE.Mode.index h).symm)]
            split_ifs
            · rw [dl, if_neg (by omega)]; simp
            · simp)
  exact congrArg (fun F => F x) h

end DpF

/-! ## Slice restrictions of the generators -/

theorem dl_mul (k : ℕ) (x : W) : dl k * x = if k = 0 then x else 0 := by
  unfold dl; split_ifs <;> simp

theorem mul_dl (k : ℕ) (x : W) : x * dl k = if k = 0 then x else 0 := by
  unfold dl; split_ifs <;> simp

theorem rhoSig_prod (m n : ℕ) :
    rhoSig ⟨m, 0⟩ * rhoSig ⟨n, 0⟩ + rhoSig ⟨m, 1⟩ * rhoSig ⟨n, 1⟩ =
      (-(1 / 2 : ℂ)) • (dl m * sigOf n 0 + sigOf m 0 * dl n) := by
  simp only [rhoSig_zero, rhoSig_one, smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub,
    add_mul, mul_add, smul_sub, smul_add]
  match_scalars <;> ring_nf <;> simp [I_sq] <;> ring

theorem rho1_Sgen (k : ℕ) : rho1 (Sgen k) = -sigOf k 0 := by
  simp only [Sgen, map_sum, Fin.sum_univ_three, map_add, map_mul, sigOf, rho1_sig, rhoSig_two,
    mul_zero, add_zero]
  rw [Finset.sum_congr rfl fun m _ => rhoSig_prod m (k - m)]
  rw [← Finset.smul_sum, Finset.sum_add_distrib]
  simp only [dl_mul, mul_dl]
  rw [Finset.sum_ite_eq' (Finset.range (k + 1)) 0, if_pos (by simp)]
  rw [Finset.sum_eq_single k]
  · rw [if_pos (Nat.sub_self k), Nat.sub_zero, ← sigOf, ← two_smul ℂ, smul_smul]
    norm_num
  · intro m hm hmk
    rw [if_neg (by have := Finset.mem_range.mp hm; omega)]
  · intro h; exact absurd (Finset.self_mem_range_succ k) h

theorem rho1_Egen_term (k j : ℕ) :
    ((j : ℂ) + 1) • (rhoSig ⟨k - j, 0⟩ * psiOf j 0 + rhoSig ⟨k - j, 1⟩ * psiOf j 1) =
      (1 / 2 : ℂ) • (dl (k - j) * Uk j + sigOf (k - j) 0 * Vk j) := by
  simp only [rhoSig_zero, rhoSig_one, Uk, Vk, smul_mul_assoc, mul_smul_comm, sub_mul, add_mul,
    mul_add, mul_neg, smul_add, smul_sub, smul_neg, smul_smul]
  match_scalars <;> ring

theorem rho1_psiOf (k : ℕ) (b : Fin 3) : rho1 (psiOf k b) = psiOf k b := rho1_psi _

theorem rho1_Egen (k : ℕ) : rho1 (Egen (k + 1)) = (1 / 2 : ℂ) • Ek k := by
  simp only [Egen, map_sum, map_smul, Fin.sum_univ_three, map_add, map_mul, sigOf, rho1_sig,
    rho1_psiOf, rhoSig_two, zero_mul, add_zero, Nat.add_sub_cancel, smul_zero, ← smul_add]
  rw [Finset.sum_congr rfl fun j _ => rho1_Egen_term k j, ← Finset.smul_sum]
  congr 1
  rw [Finset.sum_add_distrib, Ek]
  congr 1
  · rw [Finset.sum_eq_single k]
    · rw [Nat.sub_self, dl, if_pos rfl, one_mul]
    · intro j hj hjk
      rw [dl, if_neg (by have := Finset.mem_range.mp hj; omega), zero_mul]
    · intro h; exact absurd (Finset.self_mem_range_succ k) h
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    rw [show k + 1 - 1 - j = k - j by omega, show k - (k - j) = j by omega]

/-! ## The free algebra on `S(n)`, `E(n)` -/

theorem isPar_Sgen (n : ℕ) : IsPar 0 (Sgen n) :=
  IsPar.sum _ _ fun _ _ => IsPar.sum _ _ fun _ _ => (isPar_sig _).mul (isPar_sig _)

theorem isPar_Egen (n : ℕ) : IsPar 1 (Egen n) :=
  IsPar.sum _ _ fun _ _ => IsPar.sum _ _ fun _ _ =>
    (((isPar_sig _).mul (isPar_psi _)).congr (by omega)).smul _

/-- Generator images: `σ⁰_k ↦ -S(k)`, `ψ⁰_k ↦ 2 E(k+1)`, all other generators `↦ 0`. -/
def Gsig (g : SMode) : W := if g.color = 0 then -Sgen g.index else 0

def Gpsi (m : PMode) : W := if m.color = 0 then (2 : ℂ) • Egen (m.index + 1) else 0

theorem isPar_Gsig (g : SMode) : IsPar 0 (Gsig g) := by
  unfold Gsig; split_ifs
  · exact (isPar_Sgen _).neg
  · exact IsPar.zero 0

theorem isPar_Gpsi (m : PMode) : IsPar 1 (Gpsi m) := by
  unfold Gpsi; split_ifs
  · exact (isPar_Egen _).smul _
  · exact IsPar.zero 1

/-- The free super-commutative algebra on `σ⁰_k` (even) and `ψ⁰_k` (odd), mapped to `W` by
`σ⁰_k ↦ -S(k)` and `ψ⁰_k ↦ 2E(k+1)`. -/
def Gmap : W →ₐ[ℂ] W := substW Gsig Gpsi isPar_Gsig isPar_Gpsi

/-- The projection onto the subalgebra generated by the colour-`0` generators. -/
def projFull : W →ₐ[ℂ] W := proj (fun g : SMode => g.color = 0) (fun m : PMode => m.color = 0)

theorem projFull_sig (g : SMode) : projFull (sig g) = if g.color = 0 then sig g else 0 := by
  simp [projFull, proj]

theorem projFull_psi (m : PMode) : projFull (psi m) = if m.color = 0 then psi m else 0 := by
  simp [projFull, proj]

theorem rho1_comp_Gmap : rho1.comp Gmap = Psi.comp projFull := by
  apply algHom_ext_W
  · rintro ⟨k, c⟩
    simp only [AlgHom.comp_apply, Gmap, substW_sig, projFull_sig, Gsig]
    split_ifs with hc
    · subst hc
      rw [map_neg, rho1_Sgen, neg_neg, Psi_sig]
      rfl
    · simp
  · rintro ⟨k, c⟩
    simp only [AlgHom.comp_apply, Gmap, substW_psi, projFull_psi, Gpsi]
    split_ifs with hc
    · subst hc
      rw [map_smul, rho1_Egen, smul_smul, Psi_psi]
      norm_num
      rfl
    · simp

/-- An algebra map whose generator images are killed by a derivation lands in its kernel. -/
theorem der_comp_eq_zero {p : ℕ} {D : Module.End ℂ W} (hD : IsDer p D) (φ : W →ₐ[ℂ] W)
    (hgen : ∀ g : Gen, D (φ g.elt) = 0) (y : W) : D (φ y) = 0 := by
  refine induction_gen (P := fun y => D (φ y) = 0) (by simp) (by rw [map_one]; exact hD.map_one)
    ?_ ?_ ?_ ?_ y
  · intro x y hx hy; rw [map_add, map_add, hx, hy, add_zero]
  · intro r x hx; rw [map_smul, map_smul, hx, smul_zero]
  · intro g x hx
    rw [map_mul, hD, hx, mul_zero, add_zero]
    have := hgen (.s g)
    simp only [Gen.elt] at this
    rw [this, zero_mul]
  · intro m x hx
    rw [map_mul, hD, hx, mul_zero, add_zero]
    have := hgen (.p m)
    simp only [Gen.elt] at this
    rw [this, zero_mul]

theorem Gmap_gen_mem_harm (g : Gen) : Gmap g.elt ∈ harm := by
  cases g with
  | s g =>
    simp only [Gen.elt, Gmap, substW_sig, Gsig]
    split_ifs
    · exact harm.neg_mem (Sgen_mem_harm _)
    · exact harm.zero_mem
  | p m =>
    simp only [Gen.elt, Gmap, substW_psi, Gpsi]
    split_ifs
    · exact harm.smul_mem _ (Egen_mem_harm _)
    · exact harm.zero_mem

/-- Every element of the image of the free algebra is a harmonic invariant. -/
theorem Gmap_mem_harm (y : W) : Gmap y ∈ harm := by
  refine mem_harm_iff.mpr ⟨mem_inv.mpr fun c => ?_, fun i a => ?_, fun i a => ?_⟩
  · exact der_comp_eq_zero (homDer_Y c).isDer Gmap
      (fun g => (mem_inv.mp (mem_harm_iff.mp (Gmap_gen_mem_harm g)).1) c) y
  · exact der_comp_eq_zero (homDer_X i a).isDer Gmap
      (fun g => (mem_harm_iff.mp (Gmap_gen_mem_harm g)).2.1 i a) y
  · exact der_comp_eq_zero (homDer_dUd i a).isDer Gmap
      (fun g => (mem_harm_iff.mp (Gmap_gen_mem_harm g)).2.2 i a) y

/-! ## Generation and freeness -/

/-- Keep only the colour-`0` even generators. -/
def projS : W →ₐ[ℂ] W := proj (fun g : SMode => g.color = 0) (fun _ : PMode => True)

theorem projS_sig (g : SMode) : projS (sig g) = if g.color = 0 then sig g else 0 := by
  simp [projS, proj]

theorem projS_psi (m : PMode) : projS (psi m) = psi m := by
  simp [projS, proj]

theorem projS_sigOf_zero (k : ℕ) : projS (sigOf k 0) = sigOf k 0 := by
  rw [sigOf, projS_sig, if_pos rfl]

theorem projS_dl (k : ℕ) : projS (dl k) = dl k := by
  unfold dl; split_ifs <;> simp

theorem projS_comp_rho1 : projS.comp rho1 = rho1 := by
  apply algHom_ext_W
  · rintro ⟨k, c⟩
    simp only [AlgHom.comp_apply, rho1_sig]
    fin_cases c <;> simp [rhoSig, projS_dl, projS_sigOf_zero, map_sub, map_add]
  · intro m; simp [projS_psi]

theorem projS_comp_PsiInv : projS.comp PsiInv = PsiInv.comp projS := by
  apply algHom_ext_W
  · intro g
    simp only [AlgHom.comp_apply, PsiInv_sig, projS_sig]
    split_ifs <;> simp
  · rintro ⟨k, c⟩
    simp only [AlgHom.comp_apply, PsiInv_psi, projS_psi]
    fin_cases c <;>
      simp [psiOld, Ut, map_sum, map_mul, projS_sigOf_zero, psiOf, projS_psi, map_sub, map_add]

/-- **Generation.** Every harmonic invariant is the image of an element of the free algebra. -/
theorem exists_free_preimage {f : W} (hf : f ∈ harm) : ∃ y, projFull y = y ∧ Gmap y = f := by
  obtain ⟨-, -, hD⟩ := mem_harm_iff.mp hf
  set y := PsiInv (rho1 f) with hydef
  have hPy : Psi y = rho1 f := Psi_PsiInv _
  have h1 : ∀ j, iP ⟨j, 1⟩ y = 0 := by
    intro j
    have h3 : Psi ((I • iP ⟨j, 1⟩) y) = 0 := by
      rw [← Dp2_Psi, hPy, ← rho1_dUd, hD j 2, map_zero]
    have h4 : (I • iP ⟨j, 1⟩) y = 0 := Psi_injective (by rw [h3, map_zero])
    rw [LinearMap.smul_apply] at h4
    exact (smul_eq_zero.mp h4).resolve_left I_ne_zero
  have h2 : ∀ j, iP ⟨j, 2⟩ y = 0 := by
    intro j
    have h3 : Psi (((-I) • iP ⟨j, 2⟩) y) = 0 := by
      rw [← DpF_Psi, hPy, DpF, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
        ← rho1_dUd, ← rho1_dUd, hD j 0, hD j 1, map_zero, neg_zero, smul_zero, add_zero]
    have h4 : ((-I) • iP ⟨j, 2⟩) y = 0 := Psi_injective (by rw [h3, map_zero])
    rw [LinearMap.smul_apply] at h4
    exact (smul_eq_zero.mp h4).resolve_left (neg_ne_zero.mpr I_ne_zero)
  have hS : projS y = y := by
    rw [hydef, ← AlgHom.comp_apply, projS_comp_PsiInv, AlgHom.comp_apply, ← AlgHom.comp_apply projS,
      projS_comp_rho1]
  have hσ : ∀ e t, coefW y e t ≠ 0 → ∀ g ∈ e.support, g.color = 0 := by
    intro e t hne g hg
    by_contra hc
    apply hne
    rw [← hS, projS, coefW_proj, if_neg]
    rintro ⟨h, -⟩
    exact hc (h g hg)
  have hy : projFull y = y := by
    refine proj_eq_self _ _ hσ fun m hm => ?_
    obtain ⟨j, c⟩ := m
    fin_cases c
    · exact absurd rfl hm
    · exact h1 j
    · exact h2 j
  refine ⟨y, hy, ?_⟩
  have hrho : rho1 (Gmap y) = rho1 f := by
    rw [← AlgHom.comp_apply, rho1_comp_Gmap, AlgHom.comp_apply, hy, hPy]
  have hdiff : f - Gmap y ∈ harm := harm.sub_mem hf (Gmap_mem_harm y)
  obtain ⟨hinv', hX', -⟩ := mem_harm_iff.mp hdiff
  have h0 := eq_zero_of_slicePt (x := f - Gmap y) (mem_inv.mp hinv') hX' fun A B hA => by
    obtain ⟨Θ, hΘ⟩ := reach_slicePt_one_mul (mem_inv.mp hinv') hX' A hA B
    rw [hΘ, ← evalAt_slicePt_one, AlgHom.comp_apply, map_sub, hrho, sub_self, map_zero, map_zero]
  exact (sub_eq_zero.mp h0).symm

/-- **Freeness.** The map from the free algebra is injective. -/
theorem Gmap_injOn {y : W} (hy : projFull y = y) (h0 : Gmap y = 0) : y = 0 := by
  have h : Psi y = 0 := by
    rw [← hy, ← AlgHom.comp_apply, ← rho1_comp_Gmap, AlgHom.comp_apply, h0, map_zero]
  exact Psi_injective (by rw [h, map_zero])

/-- **FGT Theorem B for `𝔰𝔩₂`, invariant-theoretic form.** The harmonic invariants are exactly
the image of the free super-commutative algebra on even `σ⁰_k ↦ -S(k)` (`k ≥ 0`) and odd
`ψ⁰_k ↦ 2E(k+1)` (`k ≥ 0`), and this map is injective on the free algebra. -/
theorem harm_free :
    (∀ y, Gmap y ∈ harm) ∧ (∀ f ∈ harm, ∃ y, projFull y = y ∧ Gmap y = f) ∧
      (∀ y, projFull y = y → Gmap y = 0 → y = 0) :=
  ⟨Gmap_mem_harm, fun _ hf => exists_free_preimage hf, fun _ hy h0 => Gmap_injOn hy h0⟩

end KhanSL2.StrongMacdonald
