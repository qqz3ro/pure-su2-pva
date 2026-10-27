module

public import KhanSL2.StrongMacdonald.Operators

@[expose] public section

/-!
# The Laplacian `□̄ = ∂̄∂̄^† + ∂̄^†∂̄` and its Cartan form

`∂̄^† = Σ_{a,m} T_a(m)^† ψ^a(-m)^†` with `ψ^a(-m)^† = (1/m) ι_{a,m}`. The Cartan formula
`ι_{a,m} ∂̄ + ∂̄ ι_{a,m} = L_a(m)` turns the Laplacian into
`□̄ = Σ_{a,m} (1/m) (E_a(m) ι_{a,m} + T_a(m)^† L_a(m))`, `E_a(m) = [∂̄, T_a(m)^†]`,
a locally finite sum of products of two derivations.

We also define the three operators of FGT Lemma 3.13:
`□ = Σ (1/m) X^† X`, `D = Σ d d^†` and `K = -Σ ε_abc (1/m) Y_c ψ^a ι^b`.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

/-! ## Sum helpers -/

theorem sum_range_ite_eq (n i : ℕ) (f : ℕ → W) :
    ∑ j ∈ Finset.range n, (if i = j then f j else 0) = if i < n then f i else 0 := by
  rw [Finset.sum_ite_eq]
  simp

theorem sum_range_ite_rev (n i : ℕ) (f : ℕ → W) :
    ∑ j ∈ Finset.range n, (if i = n - 1 - j then f j else 0) =
      if i < n then f (n - 1 - i) else 0 := by
  rw [← Finset.sum_range_reflect]
  have : ∀ j ∈ Finset.range n, (if i = n - 1 - (n - 1 - j) then f (n - 1 - j) else 0) =
      if i = j then f (n - 1 - j) else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show n - 1 - (n - 1 - j) = j by omega]
  rw [Finset.sum_congr rfl this, sum_range_ite_eq]

theorem iota_psiOf_mul (i j : ℕ) (a b : Fin 3) (x : W) :
    iota i a (psiOf j b * x) = (if i = j ∧ a = b then x else 0) - psiOf j b * iota i a x := by
  rw [iota, psiOf, iP_psi_mul]
  congr 1
  by_cases h : i = j ∧ a = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    cases h'
    exact h ⟨rfl, rfl⟩

theorem iota_sigOf_mul (i k : ℕ) (a b : Fin 3) (x : W) :
    iota i a (sigOf k b * x) = sigOf k b * iota i a x := iP_sig_mul _ _ _

/-! ## The adjoint differential and the Laplacian -/

theorem kills_dbarDag :
    Kills (fun i => ∑ a, lam i • (Td i a * iota i a)) :=
  Kills.sum Finset.univ fun a _ => ((kills_iota a).mul_left fun i => Td i a).smul lam

/-- `∂̄^† = Σ_{a,m} T_a(m)^† (1/m) ι_{a,m}`. -/
def dbarDag : Module.End ℂ W := lsum _ kills_dbarDag.evZero

/-- The Laplacian. -/
def lap : Module.End ℂ W := dbar * dbarDag + dbarDag * dbar

/-- `E_a(m) = [∂̄, T_a(m)^†]`. -/
def E (i : ℕ) (a : Fin 3) : Module.End ℂ W := dbar * Td i a - Td i a * dbar

theorem homDer_E (i : ℕ) (a : Fin 3) : HomDer 1 (E i a) :=
  homDer_dbar.comm_even (homDer_Td i a)

/-! ## The Cartan formula -/

theorem cartan_sigOf (i k : ℕ) (a b : Fin 3) :
    (iota i a * dbar + dbar * iota i a) (sigOf k b) = L i a (sigOf k b) := by
  simp only [LinearMap.add_apply, Module.End.mul_apply, iota_sigOf, map_zero, add_zero,
    dbar_sigOf, map_sum, map_smul, iota_psiOf_mul, L, Rlow_sigOf, adLow_sigOf, mul_zero, sub_zero]
  simp only [ite_and, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (γ := ℕ)]
  simp only [Finset.sum_ite_eq, Finset.mem_range]
  by_cases h : i < k
  · rw [if_pos (by omega : i + 1 ≤ k)]
    simp only [h, if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [show k - 1 - i = k - (i + 1) by omega]
  · rw [if_neg (by omega)]
    simp [h]

theorem cartan_psiOf (i n : ℕ) (a b : Fin 3) :
    (iota i a * dbar + dbar * iota i a) (psiOf n b) = L i a (psiOf n b) := by
  have h0 : dbar (iota i a (psiOf n b)) = 0 := by
    rw [iota_psiOf]; split
    · exact homDer_dbar.map_one
    · exact map_zero _
  have hA : ∑ j ∈ Finset.range n, ∑ a', ∑ c, epsilon a' b c •
      (if i = j ∧ a = a' then psiOf (n - 1 - j) c else 0) =
      if i < n then ∑ c, epsilon a b c • psiOf (n - 1 - i) c else 0 := by
    simp only [ite_and, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_comm (γ := ℕ)]
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    by_cases h : i < n
    · simp only [h, if_true]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · simp [h]
  have hB : ∑ j ∈ Finset.range n, ∑ a', ∑ c, epsilon a' b c •
      (if i = n - 1 - j ∧ a = c then psiOf j a' else 0) =
      if i < n then ∑ a', epsilon a' b a • psiOf (n - 1 - i) a' else 0 := by
    simp only [ite_and, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_comm (γ := ℕ)]
    simp only [sum_range_ite_rev]
    by_cases h : i < n
    · simp only [h, if_true, Finset.sum_ite_eq, Finset.mem_univ]
    · simp [h]
  rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, h0, add_zero]
  simp only [dbar_psiOf, map_sum, map_smul, iota_psiOf_mul, iota_psiOf, mul_ite, mul_one,
    mul_zero, L, LinearMap.add_apply, Rlow_psiOf, adLow_psiOf, zero_add, smul_sub,
    Finset.sum_sub_distrib]
  rw [hA, hB]
  by_cases h : i < n
  · simp only [h, if_true, show i + 1 ≤ n by omega]
    have hneg : ∑ a', epsilon a' b a • psiOf (n - 1 - i) a' =
        -∑ c, epsilon a b c • psiOf (n - 1 - i) c := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [epsilon_rotate c b a, epsilon_swap_left b a c, neg_smul]
    rw [hneg, smul_neg, sub_neg_eq_add, show n - 1 - i = n - (i + 1) by omega, ← add_smul]
    norm_num
  · have h' : ¬ (i + 1 ≤ n) := by omega
    simp [h, h']

/-- The Cartan formula `ι_{a,m} ∂̄ + ∂̄ ι_{a,m} = L_a(m)`. -/
theorem cartan (i : ℕ) (a : Fin 3) : iota i a * dbar + dbar * iota i a = L i a := by
  apply ((homDer_iota i a).anticomm homDer_dbar).isDer.ext (homDer_L i a).isDer
  intro g
  cases g with
  | s g => exact cartan_sigOf i g.index a g.color
  | p n => exact cartan_psiOf i n.index a n.color

/-! ## The Cartan form of the Laplacian -/

/-- The summands `Σ_a (1/m) (E_a(m) ι_{a,m} + T_a(m)^† L_a(m))`. -/
def starFam (i : ℕ) : Module.End ℂ W := ∑ a, lam i • (E i a * iota i a + Td i a * L i a)

theorem kills_star : Kills starFam :=
  Kills.sum Finset.univ fun a _ =>
    (((kills_iota a).mul_left fun i => E i a).add ((kills_L a).mul_left fun i => Td i a)).smul lam

/-- `□̄ = Σ_{a,m} (1/m) (E_a(m) ι_{a,m} + T_a(m)^† L_a(m))`. -/
theorem lap_eq : lap = lsum starFam kills_star.evZero := by
  rw [lap, dbarDag, lsum_mul_left, lsum_mul_right, lsum_add]
  apply lsum_congr
  intro i
  simp only [starFam, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, mul_smul_comm,
    smul_mul_assoc, ← smul_add]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [← cartan i a, E]
  simp only [sub_mul, mul_add, mul_assoc]
  abel

/-! ## The FGT operators `□`, `D`, `K` -/

/-- `ψ^a(-m) ι_{b,m}`, an even derivation. -/
def KD (i : ℕ) (a b : Fin 3) : Module.End ℂ W := lmul (psiOf i a) * iota i b

theorem homDer_KD (i : ℕ) (a b : Fin 3) : HomDer 0 (KD i a b) := (homDer_iota i b).psi_mul ⟨i, a⟩

def boxFam (i : ℕ) : Module.End ℂ W := ∑ a, lam i • (Xd i a * X i a)
def DFam (i : ℕ) : Module.End ℂ W := ∑ a, dU i a * dUd i a
def KFam (i : ℕ) : Module.End ℂ W :=
  ∑ a, ∑ b, ∑ c, (-(epsilon a b c * lam i)) • (Y c * KD i a b)

theorem kills_box : Kills boxFam :=
  Kills.sum Finset.univ fun a _ => ((kills_X a).mul_left fun i => Xd i a).smul lam

theorem kills_D : Kills DFam :=
  Kills.sum Finset.univ fun a _ => (kills_dUd a).mul_left fun i => dU i a

theorem kills_KD (a b : Fin 3) : Kills (fun i => KD i a b) :=
  (kills_iota b).mul_left fun i => lmul (psiOf i a)

theorem kills_K : Kills KFam :=
  Kills.sum Finset.univ fun a _ => Kills.sum Finset.univ fun b _ =>
    Kills.sum Finset.univ fun c _ =>
      ((kills_KD a b).mul_left fun _ => Y c).smul fun i => -(epsilon a b c * lam i)

/-- `□ = Σ_{a,m} (1/m) X_a(m)^† X_a(m)`. -/
def boxOp : Module.End ℂ W := lsum boxFam kills_box.evZero
/-- `D = Σ_{a,m} d_a(-m) d_a(-m)^†`. -/
def DOp : Module.End ℂ W := lsum DFam kills_D.evZero
/-- `K = -Σ ε_abc (1/m) Y_c ψ^a(-m) ι_{b,m}`. -/
def KOp : Module.End ℂ W := lsum KFam kills_K.evZero

/-! ## Reduction to generators and pairs -/

/-- The difference family. -/
def Fam (i : ℕ) : Module.End ℂ W := starFam i - (boxFam i + DFam i + KFam i)

theorem kills_Fam : Kills Fam := kills_star.sub ((kills_box.add kills_D).add kills_K)

theorem lap_sub_eq : lap - (boxOp + DOp + KOp) = lsum Fam kills_Fam.evZero := by
  rw [lap_eq, boxOp, DOp, KOp, lsum_add, lsum_add, lsum_sub]
  rfl

theorem gcomm_add_two (p : ℕ) (P : Module.End ℂ W) (g : Gen) :
    gcomm (p + 2) P g = gcomm p P g := by
  simp only [gcomm]
  congr 2
  rw [add_mul, pow_add, mul_comm 2, pow_mul]
  simp

theorem IsDiffOp.of_add_two {k p : ℕ} {P : Module.End ℂ W} (h : IsDiffOp k (p + 2) P) :
    IsDiffOp k p P := by
  induction k generalizing p P with
  | zero => intro g; rw [← gcomm_add_two]; exact h g
  | succ k ih => intro g; rw [← gcomm_add_two]; exact ih ((h g).congr_par (by ring))

theorem HomDer.mul_isDiffOp {p q : ℕ} {A B : Module.End ℂ W} (hA : HomDer p A)
    (hB : HomDer q B) : IsDiffOp 2 (p + q) (A * B) :=
  hA.isDiffOp.mul hB.isDiffOp

theorem HomDer.mul_isDiffOp_even {p q : ℕ} {A B : Module.End ℂ W} (hA : HomDer p A)
    (hB : HomDer q B) (h : p = 0 ∧ q = 0 ∨ p = 1 ∧ q = 1) : IsDiffOp 2 0 (A * B) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hA.mul_isDiffOp hB).congr_par rfl
  · exact ((hA.mul_isDiffOp hB).congr_par (show 1 + 1 = 0 + 2 from rfl)).of_add_two

theorem isDiffOp_Fam (i : ℕ) : IsDiffOp 2 0 (Fam i) := by
  have hstar : IsDiffOp 2 0 (starFam i) := by
    unfold starFam
    refine IsDiffOp.sum _ _ fun a _ => IsDiffOp.smul _ (IsDiffOp.add ?_ ?_)
    · exact (homDer_E i a).mul_isDiffOp_even (homDer_iota i a) (.inr ⟨rfl, rfl⟩)
    · exact (homDer_Td i a).mul_isDiffOp_even (homDer_L i a) (.inl ⟨rfl, rfl⟩)
  have hbox : IsDiffOp 2 0 (boxFam i) := by
    unfold boxFam
    exact IsDiffOp.sum _ _ fun a _ => IsDiffOp.smul _
      ((homDer_Xd i a).mul_isDiffOp_even (homDer_X i a) (.inl ⟨rfl, rfl⟩))
  have hD : IsDiffOp 2 0 (DFam i) := by
    unfold DFam
    exact IsDiffOp.sum _ _ fun a _ =>
      (homDer_dU i a).mul_isDiffOp_even (homDer_dUd i a) (.inr ⟨rfl, rfl⟩)
  have hK : IsDiffOp 2 0 (KFam i) := by
    unfold KFam
    exact IsDiffOp.sum _ _ fun a _ => IsDiffOp.sum _ _ fun b _ => IsDiffOp.sum _ _ fun c _ =>
      IsDiffOp.smul _ ((homDer_Y c).mul_isDiffOp_even (homDer_KD i a b) (.inl ⟨rfl, rfl⟩))
  unfold Fam
  exact hstar.sub ((hbox.add hD).add hK)

/-- The second-order defect of an even operator. -/
def cross (P : Module.End ℂ W) (x y : W) : W := P (x * y) - P x * y - x * P y

theorem cross_add (P Q : Module.End ℂ W) (x y : W) :
    cross (P + Q) x y = cross P x y + cross Q x y := by
  simp only [cross, LinearMap.add_apply, add_mul, mul_add]; abel

theorem cross_sub (P Q : Module.End ℂ W) (x y : W) :
    cross (P - Q) x y = cross P x y - cross Q x y := by
  simp only [cross, LinearMap.sub_apply, sub_mul, mul_sub]; abel

theorem cross_smul (r : ℂ) (P : Module.End ℂ W) (x y : W) :
    cross (r • P) x y = r • cross P x y := by
  simp only [cross, LinearMap.smul_apply, smul_mul_assoc, mul_smul_comm, smul_sub]

theorem cross_sum {ι : Type*} (s : Finset ι) (P : ι → Module.End ℂ W) (x y : W) :
    cross (∑ j ∈ s, P j) x y = ∑ j ∈ s, cross (P j) x y := by
  simp only [cross, LinearMap.sum_apply, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

theorem IsPar.parity_iterate {r : ℕ} {x : W} (hx : IsPar r x) (p : ℕ) :
    parity^[p] x = ((-1 : ℂ) ^ (p * r)) • x := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, hx, smul_smul, ← pow_add]
    congr 1
    ring

/-- The defect of a product of two homogeneous derivations of even total parity. -/
theorem HomDer.cross_mul {p q : ℕ} {A B : Module.End ℂ W} (hA : HomDer p A) (hB : HomDer q B)
    (hpq : (p + q) % 2 = 0) (g : Gen) (y : W) :
    cross (A * B) g.elt y = ((-1 : ℂ) ^ (p * (q + g.par))) • (B g.elt * A y) +
      ((-1 : ℂ) ^ (q * g.par)) • (A g.elt * B y) := by
  have hBg := hB.2 g
  simp only [cross, Module.End.mul_apply]
  rw [hB.1, parity_iterate_gen, map_add, hA.1, smul_mul_assoc, map_smul, hA.1,
    hBg.parity_iterate, parity_iterate_gen]
  have hs : ((-1 : ℂ) ^ (q * g.par) * (-1) ^ (p * g.par)) = 1 := by
    rw [← pow_add, ← add_mul]
    obtain ⟨t, ht⟩ : ∃ t, q + p = 2 * t := ⟨(p + q) / 2, by omega⟩
    rw [ht, mul_assoc, pow_mul]; simp
  simp only [smul_add, smul_mul_assoc, smul_smul, hs, one_smul]
  abel

/-- Generators lie in the low subalgebras above their index. -/
def Gen.index : Gen → ℕ
  | .s g => g.index
  | .p m => m.index

theorem Gen.low_mul (g : Gen) {N : ℕ} (hg : g.index < N) {y : W} (hy : Low N y) :
    Low N (g.elt * y) := by
  cases g with
  | s g => exact .sig hg hy
  | p m => exact .psi hg hy

theorem lsum_apply_low {P : ℕ → Module.End ℂ W} (hP : Kills P) {N : ℕ} {x : W} (hx : Low N x) :
    lsum P hP.evZero x = ∑ i ∈ Finset.range N, P i x :=
  lsum_apply_of _ fun i hi => hP N i hi x hx

/-- FGT Lemma 3.13 follows from its instances on single generators and on pairs. -/
theorem lap_eq_of
    (hgen : ∀ (g : Gen) (N : ℕ), g.index < N → ∑ i ∈ Finset.range N, Fam i g.elt = 0)
    (hpair : ∀ (g h : Gen) (N : ℕ), g.index < N → h.index < N →
      ∑ i ∈ Finset.range N, cross (Fam i) g.elt h.elt = 0) :
    lap = boxOp + DOp + KOp := by
  rw [← sub_eq_zero, lap_sub_eq]
  apply (IsDiffOp.lsum kills_Fam.evZero isDiffOp_Fam).eq_zero
  intro x hx
  rcases hx with rfl | ⟨g, y, hy, rfl⟩
  · rw [lsum_apply_low kills_Fam Low.one (N := 0)]
    simp
  · rcases hy with rfl | ⟨h, z, hz, rfl⟩
    · rw [mul_one, ← mul_one g.elt,
        lsum_apply_low kills_Fam (g.low_mul (Nat.lt_succ_self _) Low.one)]
      simpa using hgen g (g.index + 1) (Nat.lt_succ_self _)
    · have hz1 : z = 1 := hz
      subst hz1
      rw [mul_one]
      set N := max g.index h.index + 1
      have hgN : g.index < N := by omega
      have hhN : h.index < N := by omega
      have hgl : Low N g.elt := by simpa using g.low_mul hgN Low.one
      have hhl : Low N h.elt := by simpa using h.low_mul hhN Low.one
      rw [lsum_apply_low kills_Fam (g.low_mul hgN hhl)]
      have hsplit : ∀ i, Fam i (g.elt * h.elt) =
          Fam i g.elt * h.elt + g.elt * Fam i h.elt + cross (Fam i) g.elt h.elt := by
        intro i; simp only [cross]; abel
      simp only [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        hgen g N hgN, hgen h N hhN, hpair g h N hgN hhN]
      simp

end KhanSL2.StrongMacdonald
