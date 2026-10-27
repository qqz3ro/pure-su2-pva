module

public import KhanSL2.StrongMacdonald.HermLap
public import KhanSL2.StrongMacdonald.LapMain

@[expose] public section

/-!
# The invariant subcomplex

The constant loops act on `W` by the even derivations `Y c`. They commute with `∂̄` and,
by adjointness, with `∂̄†`; so the invariants `C = ⋂_c ker Y_c` form a subcomplex stable
under the Laplacian. On `C` the term `K` of FGT Lemma 3.13 vanishes, so `□̄ = □ + D` there.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

@[simp] theorem Y_psiOf (c b : Fin 3) (k : ℕ) :
    Y c (psiOf k b) = ∑ d, epsilon c b d • psiOf k d := by
  simp [Y]

theorem HomDer.zero_mul_apply {D : Module.End ℂ W} (hD : HomDer 0 D) (x y : W) :
    D (x * y) = D x * y + x * D y := hD.1 x y

/-- Equivariance of the invariant tensor `Σ ε_abe u_a v_e`. -/
theorem even_der_eps {D : Module.End ℂ W} (hD : HomDer 0 D) (c b : Fin 3) (u v : Fin 3 → W)
    (hu : ∀ a, D (u a) = ∑ f, epsilon c a f • u f)
    (hv : ∀ e, D (v e) = ∑ f, epsilon c e f • v f) :
    D (∑ a, ∑ e, epsilon a b e • (u a * v e)) =
      ∑ d, epsilon c b d • ∑ a, ∑ e, epsilon a d e • (u a * v e) := by
  simp only [map_sum, map_smul, hD.zero_mul_apply, hu, hv, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, smul_add, Finset.sum_add_distrib]
  simp only [Fin.sum_univ_three]
  fin_cases c <;> fin_cases b <;> simp [epsilon] <;> module

/-! ## `Y` commutes with `∂̄` and `∂̄†` -/

theorem Y_comm_dbar (c : Fin 3) : Y c * dbar = dbar * Y c := by
  have hD := HomDer.comm_even homDer_dbar (homDer_Y c)
  have h0 : dbar * Y c - Y c * dbar = 0 := by
    apply hD.isDer.ext (IsDer.zero 1)
    intro g
    cases g with
    | s g =>
      obtain ⟨k, b⟩ := g
      show dbar (Y c (sigOf k b)) - Y c (dbar (sigOf k b)) = 0
      have h1 : Y c (dbar (sigOf k b)) = ∑ j ∈ Finset.range k, ∑ d, epsilon c b d •
          ∑ a, ∑ e, epsilon a d e • (psiOf j a * sigOf (k - 1 - j) e) := by
        rw [dbar_sigOf, map_sum]
        exact Finset.sum_congr rfl fun j _ => even_der_eps (homDer_Y c) c b _ _
          (fun a => Y_psiOf c a j) (fun e => Y_sigOf (k - 1 - j) e c)
      have h2 : dbar (Y c (sigOf k b)) = ∑ d, epsilon c b d • ∑ j ∈ Finset.range k,
          ∑ a, ∑ e, epsilon a d e • (psiOf j a * sigOf (k - 1 - j) e) := by
        simp only [Y_sigOf, map_sum, map_smul, dbar_sigOf]
      rw [h1, h2, sub_eq_zero, Finset.sum_comm]
      simp only [Finset.smul_sum]
    | p n =>
      obtain ⟨k, b⟩ := n
      show dbar (Y c (psiOf k b)) - Y c (dbar (psiOf k b)) = 0
      have h1 : Y c (dbar (psiOf k b)) = (1 / 2 : ℂ) • ∑ j ∈ Finset.range k, ∑ d, epsilon c b d •
          ∑ a, ∑ e, epsilon a d e • (psiOf j a * psiOf (k - 1 - j) e) := by
        rw [dbar_psiOf, map_smul, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => even_der_eps (homDer_Y c) c b _ _
          (fun a => Y_psiOf c a j) (fun e => Y_psiOf c e _)
      have h2 : dbar (Y c (psiOf k b)) = ∑ d, epsilon c b d • ((1 / 2 : ℂ) • ∑ j ∈ Finset.range k,
          ∑ a, ∑ e, epsilon a d e • (psiOf j a * psiOf (k - 1 - j) e)) := by
        simp only [Y_psiOf, map_sum, map_smul, dbar_psiOf]
      rw [h1, h2, sub_eq_zero, Finset.sum_comm]
      simp only [Finset.smul_sum, smul_comm (1 / 2 : ℂ)]
  rw [sub_eq_zero] at h0
  exact h0.symm

/-- Commutation passes to adjoints. -/
theorem comm_of_adj {A A' B B' : Module.End ℂ W} (hA : IsAdj A A') (hB : IsAdj B B')
    (h : A * B = B * A) : B' * A' = A' * B' := by
  have h1 : IsAdj (A * B - B * A) (B' * A' - A' * B') := (hA.comp hB).sub (hB.comp hA)
  rw [h, sub_self] at h1
  exact sub_eq_zero.mp (IsAdj.unique h1 IsAdj.zero)

theorem Y_comm_dbarDag (c : Fin 3) : Y c * dbarDag = dbarDag * Y c := by
  have h := comm_of_adj (isAdj_Y c) isAdj_dbar (Y_comm_dbar c)
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun P : Module.End ℂ W => P x) h
  simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_inj] at hx
  exact hx.symm

/-! ## The invariant subcomplex -/

/-- The `𝔤`-invariants `C = ⋂_c ker Y_c`. -/
def inv : Submodule ℂ W := ⨅ c, LinearMap.ker (Y c)

theorem mem_inv {x : W} : x ∈ inv ↔ ∀ c, Y c x = 0 := by
  simp [inv, Submodule.mem_iInf]

theorem mem_inv_of_comm {P : Module.End ℂ W} (hP : ∀ c, Y c * P = P * Y c) {x : W}
    (hx : x ∈ inv) : P x ∈ inv := by
  rw [mem_inv] at hx ⊢
  intro c
  rw [← Module.End.mul_apply, hP c, Module.End.mul_apply, hx c, map_zero]

theorem dbar_mem_inv {x : W} (hx : x ∈ inv) : dbar x ∈ inv := mem_inv_of_comm Y_comm_dbar hx

theorem dbarDag_mem_inv {x : W} (hx : x ∈ inv) : dbarDag x ∈ inv :=
  mem_inv_of_comm Y_comm_dbarDag hx

/-! ## `K` vanishes on invariants -/

theorem KD_eps_comm (i : ℕ) :
    ∑ a, ∑ b, ∑ c, epsilon a b c • (Y c * KD i a b - KD i a b * Y c) = 0 := by
  have hD : HomDer 0 (∑ a, ∑ b, ∑ c, epsilon a b c • (Y c * KD i a b - KD i a b * Y c)) :=
    HomDer.sum _ _ fun a _ => HomDer.sum _ _ fun b _ => HomDer.sum _ _ fun c _ =>
      ((homDer_Y c).comm_even (homDer_KD i a b)).smul _
  apply hD.isDer.ext (IsDer.zero 0)
  intro g
  cases g with
  | s g =>
    obtain ⟨k, d⟩ := g
    show (∑ a, ∑ b, ∑ c, epsilon a b c • (Y c * KD i a b - KD i a b * Y c)) (sigOf k d) = 0
    simp [KD, Y_sigOf]
  | p n =>
    obtain ⟨k, d⟩ := n
    show (∑ a, ∑ b, ∑ c, epsilon a b c • (Y c * KD i a b - KD i a b * Y c)) (psiOf k d) = 0
    by_cases hik : i = k
    · subst hik
      fin_cases d <;> simp [KD, Fin.sum_univ_three, epsilon]
    · simp [KD, hik]

theorem KFam_apply_of_mem_inv {x : W} (hx : x ∈ inv) (i : ℕ) : KFam i x = 0 := by
  have hY := mem_inv.mp hx
  have key := congrArg (fun P : Module.End ℂ W => P x) (KD_eps_comm i)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, hY, map_zero, sub_zero, LinearMap.zero_apply] at key
  have h : ∀ a b c, (-(epsilon a b c * lam i)) • Y c (KD i a b x) =
      (-lam i) • (epsilon a b c • Y c (KD i a b x)) := by
    intro a b c
    rw [smul_smul]
    congr 1
    ring
  simp only [KFam, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, h,
    ← Finset.smul_sum, key, smul_zero]

theorem KOp_apply_of_mem_inv {x : W} (hx : x ∈ inv) : KOp x = 0 := by
  rw [KOp, lsum_apply_of _ (N := 0) fun i _ => KFam_apply_of_mem_inv hx i]
  simp

theorem lap_apply_of_mem_inv {x : W} (hx : x ∈ inv) : lap x = boxOp x + DOp x := by
  rw [lap_eq_box_D_K, LinearMap.add_apply, KOp_apply_of_mem_inv hx, add_zero,
    LinearMap.add_apply]

end KhanSL2.StrongMacdonald
