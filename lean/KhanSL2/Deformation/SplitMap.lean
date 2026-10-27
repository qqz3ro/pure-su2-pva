module

public import KhanSL2.Deformation.SplitExact

@[expose] public section

/-!
# Split coordinates (blueprint `lem:D0split`, paper Lemma 5.1(iii))

The relative CE complex of `𝔞₀ = 𝔤[z, ε]/(ε² - 1)` modulo the constant `𝔤` is written in the
original coordinates `c_n = (zⁿ)^∨` (`n ≥ 1`), `b_j = (ε z^j)^∨`. The complement
`𝔥 = (z𝔤[z]) e₊ ⊕ 𝔤[z] e₋` of the diagonal constants is a subalgebra, with dual coordinates
`c⁺_{j+1}` (Lean `c j`) and `c⁻_j` (Lean `b j`). The coordinate change is the algebra map `Ψ`:
`c_{j+1} ↦ ½(c⁺_{j+1} + c⁻_{j+1})`, `b_0 ↦ -½ c⁻_0`, `b_{j+1} ↦ ½(c⁺_{j+1} - c⁻_{j+1})`.

* `splitMap_D0`: `Ψ ∘ (Q + δ₀) = (D'' + A) ∘ Ψ`, where `A = -½ Σ_e b₀ᵉ L_e` vanishes on invariants;
* `totalZero_exact`: **`D₀ = Q + δ₀` is exact on invariants in positive `T`**.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-! ## Contracted pairs of families -/

/-- `[x, y]_a = Σ_{b,c} ε_{abc} x_b y_c`. -/
def br (x y : Fin 3 → Cochain) (a : Fin 3) : Cochain :=
  ∑ b : Fin 3, ∑ c : Fin 3, epsilon a b c • (x b * y c)

/-- The family `c_i^•`. -/
def cc (i : ℕ) : Fin 3 → Cochain := fun b => generator (.c i b)

/-- The family `b_i^•`. -/
def bb (i : ℕ) : Fin 3 → Cochain := fun b => generator (.b i b)

theorem br_add_left (x x' y : Fin 3 → Cochain) (a : Fin 3) :
    br (x + x') y a = br x y a + br x' y a := by
  simp only [br, Pi.add_apply, add_mul, smul_add, Finset.sum_add_distrib]

theorem br_add_right (x y y' : Fin 3 → Cochain) (a : Fin 3) :
    br x (y + y') a = br x y a + br x y' a := by
  simp only [br, Pi.add_apply, mul_add, smul_add, Finset.sum_add_distrib]

theorem br_sub_left (x x' y : Fin 3 → Cochain) (a : Fin 3) :
    br (x - x') y a = br x y a - br x' y a := by
  simp only [br, Pi.sub_apply, sub_mul, smul_sub, Finset.sum_sub_distrib]

theorem br_sub_right (x y y' : Fin 3 → Cochain) (a : Fin 3) :
    br x (y - y') a = br x y a - br x y' a := by
  simp only [br, Pi.sub_apply, mul_sub, smul_sub, Finset.sum_sub_distrib]

theorem br_smul_left (r : ℂ) (x y : Fin 3 → Cochain) (a : Fin 3) :
    br (r • x) y a = r • br x y a := by
  simp only [br, Pi.smul_apply, smul_mul_assoc, Finset.smul_sum, smul_comm r]

theorem br_smul_right (r : ℂ) (x y : Fin 3 → Cochain) (a : Fin 3) :
    br x (r • y) a = r • br x y a := by
  simp only [br, Pi.smul_apply, mul_smul_comm, Finset.smul_sum, smul_comm r]

theorem br_gen_comm (f g : Fin 3 → Mode) (a : Fin 3) :
    br (fun b => generator (f b)) (fun c => generator (g c)) a =
      br (fun c => generator (g c)) (fun b => generator (f b)) a :=
  epsilon_pair_swap a f g

theorem br_cc_bb (i k : ℕ) (a : Fin 3) : br (cc i) (bb k) a = br (bb k) (cc i) a :=
  br_gen_comm (fun b => .c i b) (fun c => .b k c) a

theorem br_bb_bb (i k : ℕ) (a : Fin 3) : br (bb i) (bb k) a = br (bb k) (bb i) a :=
  br_gen_comm (fun b => .b i b) (fun c => .b k c) a

theorem bbPair_eq_br (i k : ℕ) (a : Fin 3) : bbPair i k a = br (bb i) (bb k) a := rfl

theorem qGenerator_c_eq_br (j : ℕ) (a : Fin 3) :
    qGenerator (.c j a) = (-(1 / 2 : ℂ)) • ∑ i ∈ Finset.range j, br (cc i) (cc (j - 1 - i)) a :=
  rfl

theorem qGenerator_b_eq_br (j : ℕ) (a : Fin 3) :
    qGenerator (.b j a) = -∑ i ∈ Finset.range j, br (cc i) (bb (j - 1 - i)) a := rfl

/-- The image of a family under a linear map. -/
def fmap (F : Cochain →ₗ[ℂ] Cochain) (x : Fin 3 → Cochain) : Fin 3 → Cochain := fun b => F (x b)

theorem algHom_br (F : Cochain →ₐ[ℂ] Cochain) (x y : Fin 3 → Cochain) (a : Fin 3) :
    F (br x y a) = br (fmap F.toLinearMap x) (fmap F.toLinearMap y) a := by
  simp only [br, map_sum, map_smul, map_mul, fmap, AlgHom.toLinearMap_apply]

/-- `bbConv (j+1) = b₀b_{j+1} + Σ b_{i+1}b_{j-i} + b_{j+1}b₀`. -/
theorem bbConv_succ_expand (j : ℕ) (a : Fin 3) :
    bbConv (j + 1) a = bbPair 0 (j + 1) a +
      ∑ i ∈ Finset.range j, br (bb (i + 1)) (bb (j - 1 - i + 1)) a + bbPair (j + 1) 0 a := by
  rw [bbConv, Finset.sum_range_succ, Finset.sum_range_succ', Nat.sub_self, Nat.sub_zero]
  have h : ∀ i ∈ Finset.range j, bbPair (i + 1) (j + 1 - (i + 1)) a =
      br (bb (i + 1)) (bb (j - 1 - i + 1)) a := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [bbPair_eq_br]
    congr 2
    omega
  rw [Finset.sum_congr rfl h]
  abel

/-! ## The coordinate change -/

/-- Generator images of `Ψ`. -/
def splitGen : Mode → Cochain
  | .c j a => (1 / 2 : ℂ) • (generator (.c j a) + generator (.b (j + 1) a))
  | .b 0 a => (-(1 / 2 : ℂ)) • generator (.b 0 a)
  | .b (j + 1) a => (1 / 2 : ℂ) • (generator (.c j a) - generator (.b (j + 1) a))

/-- Generator images of `Ψ⁻¹`. -/
def splitInvGen : Mode → Cochain
  | .c j a => generator (.c j a) + generator (.b (j + 1) a)
  | .b 0 a => (-2 : ℂ) • generator (.b 0 a)
  | .b (j + 1) a => generator (.c j a) - generator (.b (j + 1) a)

theorem splitGen_parity (m : Mode) : FiniteExterior.parityLinear (splitGen m) = -splitGen m := by
  rw [← cochainParity_apply]
  cases m with
  | c j a => simp [splitGen, map_add, add_comm]
  | b j a => cases j <;> simp [splitGen, map_sub, neg_sub, sub_eq_add_neg, add_comm]

theorem splitInvGen_parity (m : Mode) : FiniteExterior.parityLinear (splitInvGen m) = -splitInvGen m := by
  rw [← cochainParity_apply]
  cases m with
  | c j a => simp [splitInvGen, map_add, add_comm]
  | b j a => cases j <;> simp [splitInvGen, map_sub, neg_sub, sub_eq_add_neg, add_comm]

/-- **The coordinate change `Ψ`.** -/
def splitMap : Cochain →ₐ[ℂ] Cochain := FiniteExterior.substituteOdd splitGen splitGen_parity

/-- Its inverse. -/
def splitInv : Cochain →ₐ[ℂ] Cochain := FiniteExterior.substituteOdd splitInvGen splitInvGen_parity

@[simp] theorem splitMap_generator (m : Mode) : splitMap (generator m) = splitGen m :=
  FiniteExterior.substituteOdd_generator _ _ m

@[simp] theorem splitInv_generator (m : Mode) : splitInv (generator m) = splitInvGen m :=
  FiniteExterior.substituteOdd_generator _ _ m

theorem splitInv_splitMap (u : Cochain) : splitInv (splitMap u) = u := by
  have : splitInv.comp splitMap = AlgHom.id ℂ Cochain := by
    apply FiniteExterior.algHom_ext
    intro m
    change splitInv (splitMap (generator m)) = generator m
    cases m with
    | c j a =>
      simp only [splitMap_generator, splitGen, map_smul, map_add, splitInv_generator, splitInvGen]
      module
    | b j a =>
      cases j with
      | zero => simp only [splitMap_generator, splitGen, map_smul, splitInv_generator, splitInvGen]; module
      | succ j =>
        simp only [splitMap_generator, splitGen, map_smul, map_sub, splitInv_generator, splitInvGen]
        module
  exact congrArg (fun F : Cochain →ₐ[ℂ] Cochain => F u) this

theorem splitMap_splitInv (u : Cochain) : splitMap (splitInv u) = u := by
  have : splitMap.comp splitInv = AlgHom.id ℂ Cochain := by
    apply FiniteExterior.algHom_ext
    intro m
    change splitMap (splitInv (generator m)) = generator m
    cases m with
    | c j a =>
      simp only [splitInv_generator, splitInvGen, map_add, splitMap_generator, splitGen]
      module
    | b j a =>
      cases j with
      | zero => simp only [splitInv_generator, splitInvGen, map_smul, splitMap_generator, splitGen]; module
      | succ j =>
        simp only [splitInv_generator, splitInvGen, map_sub, splitMap_generator, splitGen]
        module
  exact congrArg (fun F : Cochain →ₐ[ℂ] Cochain => F u) this

theorem splitMap_injective : Function.Injective splitMap :=
  fun u v h => by rw [← splitInv_splitMap u, h, splitInv_splitMap]

theorem splitMap_generator_parity (m : Mode) :
    cochainParity (splitMap (generator m)) = -splitMap (generator m) := by
  rw [splitMap_generator, cochainParity_apply, splitGen_parity]

theorem splitMap_colorAction (e : Fin 3) (u : Cochain) :
    splitMap (colorAction e u) = colorAction e (splitMap u) :=
  twisted_even splitMap (isEvenDer_colorAction e) (isEvenDer_colorAction e) (fun m => by
    rw [colorAction_generator, splitMap_generator]
    cases m with
    | c j a =>
      simp only [colorGenerator, Mode.color, Mode.recolor, map_sum, map_smul, splitMap_generator,
        splitGen, map_add, colorAction_generator, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro f _ <;> rw [smul_comm]
    | b j a =>
      cases j with
      | zero =>
        simp only [colorGenerator, Mode.color, Mode.recolor, map_sum, map_smul, splitMap_generator,
          splitGen, colorAction_generator, Finset.smul_sum]
        apply Finset.sum_congr rfl; intro f _; rw [smul_comm]
      | succ j =>
        simp only [colorGenerator, Mode.color, Mode.recolor, map_sum, map_smul, splitMap_generator,
          splitGen, map_sub, colorAction_generator, smul_sub, Finset.sum_sub_distrib,
          Finset.smul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro f _ <;> rw [smul_comm]) u

theorem splitInv_colorAction (e : Fin 3) (u : Cochain) :
    splitInv (colorAction e u) = colorAction e (splitInv u) := by
  apply splitMap_injective
  rw [splitMap_colorAction, splitMap_splitInv, splitMap_splitInv]

theorem splitMap_mem_invariants {u : Cochain} (hu : ∀ e, colorAction e u = 0) (e : Fin 3) :
    colorAction e (splitMap u) = 0 := by
  rw [← splitMap_colorAction, hu e, map_zero]

theorem splitInv_mem_invariants {u : Cochain} (hu : ∀ e, colorAction e u = 0) (e : Fin 3) :
    colorAction e (splitInv u) = 0 := by
  rw [← splitInv_colorAction, hu e, map_zero]

theorem splitMap_mem_coarse {d : ℤ × ℤ} {u : Cochain} (hu : u ∈ gPiece coarse d) :
    splitMap u ∈ gPiece coarse d :=
  algHom_mem_gPiece coarse splitMap (fun m => by
    rw [splitMap_generator]
    cases m with
    | c j a =>
      apply (gPiece _ _).smul_mem
      refine Submodule.add_mem _ (generator_mem_gPiece coarse _) ?_
      convert generator_mem_gPiece coarse (.b (j + 1) a) using 2
      simp [coarse, Mode.tdeg]
    | b j a =>
      cases j with
      | zero => exact (gPiece _ _).smul_mem _ (generator_mem_gPiece coarse _)
      | succ j =>
        apply (gPiece _ _).smul_mem
        refine Submodule.sub_mem _ ?_ (generator_mem_gPiece coarse _)
        convert generator_mem_gPiece coarse (.c j a) using 2
        simp [coarse, Mode.tdeg]) hu

theorem splitInv_mem_coarse {d : ℤ × ℤ} {u : Cochain} (hu : u ∈ gPiece coarse d) :
    splitInv u ∈ gPiece coarse d :=
  algHom_mem_gPiece coarse splitInv (fun m => by
    rw [splitInv_generator]
    cases m with
    | c j a =>
      refine Submodule.add_mem _ (generator_mem_gPiece coarse _) ?_
      convert generator_mem_gPiece coarse (.b (j + 1) a) using 2
      simp [coarse, Mode.tdeg]
    | b j a =>
      cases j with
      | zero => exact (gPiece _ _).smul_mem _ (generator_mem_gPiece coarse _)
      | succ j =>
        refine Submodule.sub_mem _ ?_ (generator_mem_gPiece coarse _)
        convert generator_mem_gPiece coarse (.c j a) using 2
        simp [coarse, Mode.tdeg]) hu

/-! ## The families under `Ψ` -/

theorem fmap_split_cc (i : ℕ) : fmap splitMap.toLinearMap (cc i) = (1 / 2 : ℂ) • (cc i + bb (i + 1)) := by
  funext b; simp [fmap, cc, bb, splitGen]

theorem fmap_split_bb_zero : fmap splitMap.toLinearMap (bb 0) = (-(1 / 2 : ℂ)) • bb 0 := by
  funext b; simp [fmap, bb, splitGen]

theorem fmap_split_bb_succ (i : ℕ) :
    fmap splitMap.toLinearMap (bb (i + 1)) = (1 / 2 : ℂ) • (cc i - bb (i + 1)) := by
  funext b; simp [fmap, cc, bb, splitGen]

/-! ## The term `A` -/

/-- `A = -½ Σ_e b₀ᵉ L_e`. -/
def Aop : Cochain →ₗ[ℂ] Cochain :=
  ∑ e : Fin 3, (-(1 / 2 : ℂ)) • (LinearMap.mulLeft ℂ (generator (.b 0 e)) ∘ₗ colorAction e)

theorem isOddDer_Aop : IsOddDer Aop :=
  isOddDer_sum3 (fun e => (isOddDer_mulLeft _ (isEvenDer_colorAction e)).smul _)

theorem Aop_eq_zero {v : Cochain} (hv : ∀ e, colorAction e v = 0) : Aop v = 0 := by
  simp [Aop, LinearMap.sum_apply, hv]

theorem Aop_generator (m : Mode) :
    Aop (generator m) = (1 / 2 : ℂ) • br (bb 0) (fun f => generator (m.recolor f)) m.color := by
  simp only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, colorAction_generator, colorGenerator, Finset.mul_sum,
    mul_smul_comm, br, bb, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl; intro e _
  apply Finset.sum_congr rfl; intro f _
  rw [epsilon_swap_left]
  congr 1
  ring

theorem Aop_cc (j : ℕ) (a : Fin 3) : Aop (generator (.c j a)) = (1 / 2 : ℂ) • br (bb 0) (cc j) a :=
  Aop_generator _

theorem Aop_bb (j : ℕ) (a : Fin 3) : Aop (generator (.b j a)) = (1 / 2 : ℂ) • br (bb 0) (bb j) a :=
  Aop_generator _

/-! ## `Ψ ∘ D₀ = (D'' + A) ∘ Ψ` on generators -/

theorem splitMap_D0_c (j : ℕ) (a : Fin 3) :
    splitMap (qGenerator (.c j a) + deltaGenerator 0 (.c j a)) =
      dpp (splitMap (generator (.c j a))) + Aop (splitMap (generator (.c j a))) := by
  rw [deltaGenerator_c, Nat.sub_zero, splitMap_generator, splitGen]
  simp only [map_add, map_smul, dpp_generator, dppGen, Aop_cc, Aop_bb]
  rw [bbConv_succ_expand, qGenerator_c_eq_br]
  simp only [map_add, map_smul, map_sum, bbPair_eq_br, algHom_br, fmap_split_cc, fmap_split_bb_zero,
    fmap_split_bb_succ, br_add_left, br_add_right, br_sub_left, br_sub_right, br_smul_left,
    br_smul_right, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.smul_sum]
  rw [br_cc_bb j 0, br_bb_bb (j + 1) 0]
  module

theorem splitMap_D0_b_zero (a : Fin 3) :
    splitMap (qGenerator (.b 0 a) + deltaGenerator 0 (.b 0 a)) =
      dpp (splitMap (generator (.b 0 a))) + Aop (splitMap (generator (.b 0 a))) := by
  rw [splitMap_generator, splitGen, qGenerator_b_zero, deltaGenerator_b, add_zero, map_zero]
  simp only [map_smul, dpp_generator, dppGen, Aop_bb, bbConv, zero_add, Finset.range_one,
    Finset.sum_singleton, Nat.sub_zero, bbPair_eq_br]
  module

theorem sum_br_bb_cc_reflect (k : ℕ) (a : Fin 3) :
    ∑ i ∈ Finset.range k, br (bb (i + 1)) (cc (k - 1 - i)) a =
      ∑ i ∈ Finset.range k, br (cc i) (bb (k - 1 - i + 1)) a := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [br_cc_bb]
  congr 2
  omega

theorem splitMap_D0_b_succ (k : ℕ) (a : Fin 3) :
    splitMap (qGenerator (.b (k + 1) a) + deltaGenerator 0 (.b (k + 1) a)) =
      dpp (splitMap (generator (.b (k + 1) a))) + Aop (splitMap (generator (.b (k + 1) a))) := by
  rw [deltaGenerator_b, add_zero, splitMap_generator, splitGen, qGenerator_b_eq_br, Finset.sum_range_succ]
  have hmid : ∀ i ∈ Finset.range k, br (cc i) (bb (k + 1 - 1 - i)) a =
      br (cc i) (bb (k - 1 - i + 1)) a := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    congr 2
    omega
  rw [Finset.sum_congr rfl hmid]
  simp only [map_sub, map_smul, dpp_generator, dppGen, Aop_cc, Aop_bb, qGenerator_c_eq_br]
  rw [bbConv_succ_expand]
  simp only [Nat.add_sub_cancel, Nat.sub_self, map_neg, map_add, map_smul, map_sum, bbPair_eq_br,
    algHom_br, fmap_split_cc, fmap_split_bb_zero, fmap_split_bb_succ, br_add_left, br_add_right,
    br_sub_left, br_sub_right, br_smul_left, br_smul_right, smul_add, smul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum]
  rw [sum_br_bb_cc_reflect, br_cc_bb k 0, br_bb_bb (k + 1) 0]
  module

theorem isOddDer_D0 : IsOddDer (q + delta 0) := isOddDer_q.add (isOddDer_delta (Nat.zero_le 1))

/-- **`Ψ ∘ (Q + δ₀) = (D'' + A) ∘ Ψ`.** -/
theorem splitMap_D0 (u : Cochain) : splitMap (q u + delta 0 u) = dpp (splitMap u) + Aop (splitMap u) := by
  have := twisted_odd splitMap splitMap_generator_parity isOddDer_D0 (isOddDer_dpp.add isOddDer_Aop)
    (fun m => by
      simp only [LinearMap.add_apply, q_generator, delta_generator]
      cases m with
      | c j a => exact splitMap_D0_c j a
      | b j a =>
        cases j with
        | zero => exact splitMap_D0_b_zero a
        | succ k => exact splitMap_D0_b_succ k a) u
  simpa only [LinearMap.add_apply] using this

/-- **`D₀ = Q + δ₀` is exact on invariants in positive `T`** (paper Lemma 5.1(iii)). -/
theorem totalZero_exact {n T : ℤ} (hT : T ≠ 0) {z : Cochain} (hz : ∀ e, colorAction e z = 0)
    (hzd : z ∈ gPiece coarse (n, T)) (hD : q z + delta 0 z = 0) :
    ∃ w ∈ gPiece coarse (n - 1, T), (∀ e, colorAction e w = 0) ∧ z = q w + delta 0 w := by
  have hu := splitMap_mem_invariants hz
  have hDu : dpp (splitMap z) = 0 := by
    have := splitMap_D0 z
    rw [hD, map_zero, Aop_eq_zero hu, add_zero] at this
    exact this.symm
  obtain ⟨w', hw'd, hw'inv, hw'⟩ := dpp_exact hT (splitMap_mem_coarse hzd) hu hDu
  refine ⟨splitInv w', splitInv_mem_coarse hw'd, splitInv_mem_invariants hw'inv, ?_⟩
  apply splitMap_injective
  rw [splitMap_D0, splitMap_splitInv, Aop_eq_zero hw'inv, add_zero, hw']

end KhanSL2
