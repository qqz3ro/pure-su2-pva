module

public import KhanSL2.Deformation.BDecomposition
public import KhanSL2.Deformation.CasimirReduction
public import KhanSL2.Deformation.Staircase
public import KhanSL2.Deformation.AcyclicOne

@[expose] public section

/-!
# Künneth for `d_c + d_Z` on the fully invariant part (blueprint `lem:Hlpos`, step 3)

`V00` is the space of cochains invariant under the colour actions on the `c` modes, the
`b_{≥1}` modes and the `b₀` modes separately. On it the split differential reduces to
`d_c + d_Z`, the tensor product of two copies of the `B = 0` complex (and the inert `b₀` part).

* `dC_exact_fine`: in positive `T_c`, `d_c`-cycles in `V00` are `d_c`-boundaries in `V00`
  (coefficientwise `B = 0` exactness, then Casimir projections restore the invariances);
* `kunneth_tc`: the staircase over the `b`-count assembles `d_c + d_Z`-exactness at `T_c > 0`;
* `kunneth`: in positive `T`, using the swap `σ` when `T_c = 0`.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-! ## Restricted actions on disjoint classes commute -/

theorem colorActionOn_of_false {R : Mode → Bool} (hR : ∀ m, R m = false) (e : Fin 3) :
    colorActionOn R e = 0 := by
  have : (fun m => if R m = true then colorGenerator e m else 0) = fun _ => (0 : Cochain) :=
    funext fun m => by simp [hR m]
  rw [colorActionOn, this, extendDerivation_zero_fun]

theorem colorActionOn_comm_disjoint {P Q : Mode → Bool} (hP : ColorStable P) (hQ : ColorStable Q)
    (hPQ : ∀ m, (P m && Q m) = false) (a b : Fin 3) (u : Cochain) :
    colorActionOn P a (colorActionOn Q b u) = colorActionOn Q b (colorActionOn P a u) := by
  have h := colorActionOn_comm hP hQ a b u
  simp only [colorActionOn_of_false hPQ, LinearMap.zero_apply, smul_zero,
    Finset.sum_const_zero] at h
  exact sub_eq_zero.mp h

theorem LC_LZ (a b : Fin 3) (u : Cochain) : LC a (LZ b u) = LZ b (LC a u) :=
  colorActionOn_comm_disjoint colorStable_isC colorStable_isZ
    (fun m => by cases m <;> rfl) a b u

theorem LC_LB0 (a b : Fin 3) (u : Cochain) : LC a (LB0 b u) = LB0 b (LC a u) :=
  colorActionOn_comm_disjoint colorStable_isC colorStable_isB0
    (fun m => by cases m <;> rfl) a b u

theorem LZ_LB0 (a b : Fin 3) (u : Cochain) : LZ a (LB0 b u) = LB0 b (LZ a u) :=
  colorActionOn_comm_disjoint colorStable_isZ colorStable_isB0
    (fun m => by cases m with
      | c j x => rfl
      | b j x => cases j <;> rfl) a b u

/-! ## The fully invariant part -/

/-- Cochains invariant under `L^C`, `L^Z` and `L^{B₀}` separately. -/
def V00 : Submodule ℂ Cochain :=
  ⨅ e : Fin 3, LinearMap.ker (LC e) ⊓ LinearMap.ker (LZ e) ⊓ LinearMap.ker (LB0 e)

theorem mem_V00 {u : Cochain} : u ∈ V00 ↔ ∀ e, LC e u = 0 ∧ LZ e u = 0 ∧ LB0 e u = 0 := by
  simp only [V00, Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker, and_assoc]

theorem V00_of_comm (E : Cochain →ₗ[ℂ] Cochain) (hC : ∀ e v, LC e (E v) = E (LC e v))
    (hZ : ∀ e v, LZ e (E v) = E (LZ e v)) (hB : ∀ e v, LB0 e (E v) = E (LB0 e v))
    {u : Cochain} (hu : u ∈ V00) : E u ∈ V00 := by
  rw [mem_V00] at hu ⊢
  intro e
  obtain ⟨h1, h2, h3⟩ := hu e
  exact ⟨by rw [hC, h1, map_zero], by rw [hZ, h2, map_zero], by rw [hB, h3, map_zero]⟩

theorem dC_V00 {u : Cochain} (hu : u ∈ V00) : dC u ∈ V00 :=
  V00_of_comm dC (fun e v => (dC_LC e v).symm) (fun e v => (dC_LZ e v).symm)
    (fun e v => (dC_LB0 e v).symm) hu

theorem dZ_V00 {u : Cochain} (hu : u ∈ V00) : dZ u ∈ V00 :=
  V00_of_comm dZ (fun e v => (dZ_LC e v).symm) (fun e v => (dZ_LZ e v).symm)
    (fun e v => (dZ_LB0 e v).symm) hu

theorem swap_V00 {u : Cochain} (hu : u ∈ V00) : swap u ∈ V00 := by
  rw [mem_V00] at hu ⊢
  intro e
  obtain ⟨h1, h2, h3⟩ := hu e
  exact ⟨by rw [← swap_LZ, h2, map_zero], by rw [← swap_LC, h1, map_zero],
    by rw [← swap_LB0, h3, map_zero]⟩

theorem gProj_fine_V00 {u : Cochain} (hu : u ∈ V00) (d : ℤ × ℤ × ℤ × ℤ) : gProj fine d u ∈ V00 :=
  V00_of_comm (gProj fine d)
    (fun e v => (gProj_comm_zero fine _ (fun _ _ h => colorActionOn_mem_fine _ e h) d v).symm)
    (fun e v => (gProj_comm_zero fine _ (fun _ _ h => colorActionOn_mem_fine _ e h) d v).symm)
    (fun e v => (gProj_comm_zero fine _ (fun _ _ h => colorActionOn_mem_fine _ e h) d v).symm) hu

/-! ## The grading `(cochain degree, T_c, T_b)` -/

/-- Cochain degree and the `T`-degrees of the `c` and `b` modes. -/
def g3 (m : Mode) : ℤ × ℤ × ℤ := (1, m.tcDeg, m.tbDeg)

/-- The same with the two `T`-degrees exchanged. -/
def g3s (m : Mode) : ℤ × ℤ × ℤ := (1, m.tbDeg, m.tcDeg)

def fineToG3 : ℤ × ℤ × ℤ × ℤ →+ ℤ × ℤ × ℤ where
  toFun d := (d.1, d.2.2.1, d.2.2.2)
  map_zero' := rfl
  map_add' _ _ := rfl

def g3ToCoarse : ℤ × ℤ × ℤ →+ ℤ × ℤ where
  toFun d := (d.1, d.2.1 + d.2.2)
  map_zero' := rfl
  map_add' d e := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    congr 1; ring

theorem fineToG3_fine (m : Mode) : fineToG3 (fine m) = g3 m := rfl

theorem g3ToCoarse_g3 (m : Mode) : g3ToCoarse (g3 m) = coarse m := by
  cases m <;> simp [g3ToCoarse, g3, coarse, Mode.tcDeg, Mode.tbDeg, Mode.tdeg]

theorem g3_le_coarse (d : ℤ × ℤ × ℤ) : gPiece g3 d ≤ gPiece coarse (g3ToCoarse d) := by
  have h := gPiece_le_map g3 g3ToCoarse d
  simpa only [g3ToCoarse_g3] using h

theorem fine_le_g3 (d : ℤ × ℤ × ℤ × ℤ) : gPiece fine d ≤ gPiece g3 (fineToG3 d) := by
  have h := gPiece_le_map fine fineToG3 d
  simpa only [fineToG3_fine] using h

theorem gdeg_g3_eq (s : ExteriorMonomial) : gdeg g3 s = fineToG3 (gdeg fine s) := by
  simp only [gdeg, map_sum, fineToG3_fine]

theorem gdeg_g3s (s : ExteriorMonomial) :
    gdeg g3s s = ((gdeg g3 s).1, (gdeg g3 s).2.2, (gdeg g3 s).2.1) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [gdeg, g3, g3s, Prod.fst_sum, Prod.snd_sum]

theorem mem_g3s_iff {u : Cochain} {n a b : ℤ} : u ∈ gPiece g3s (n, a, b) ↔ u ∈ gPiece g3 (n, b, a) := by
  rw [mem_gPiece_iff, mem_gPiece_iff]
  refine forall₂_congr fun s _ => ?_
  rw [gdeg_g3s]
  constructor
  · intro h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)
  · intro h
    rw [h]

theorem swap_mem_g3 {u : Cochain} {n a b : ℤ} (hu : u ∈ gPiece g3 (n, a, b)) :
    swap u ∈ gPiece g3 (n, b, a) := by
  rw [← mem_g3s_iff]
  apply algHom_mem_gPiece' g3 g3s swap _ hu
  intro m
  rw [swap_generator]
  cases m with
  | c j a =>
    show generator (.b (j + 1) a) ∈ _
    convert generator_mem_gPiece g3s (.b (j + 1) a) using 2
    simp [g3, g3s, Mode.tcDeg, Mode.tbDeg]
  | b j a =>
    cases j with
    | zero => exact generator_mem_gPiece g3s _
    | succ j =>
      show generator (.c j a) ∈ _
      convert generator_mem_gPiece g3s (.c j a) using 2
      simp [g3, g3s, Mode.tcDeg, Mode.tbDeg]

theorem dC_mem_g3 (d : ℤ × ℤ × ℤ) (u : Cochain) (hu : u ∈ gPiece g3 d) :
    dC u ∈ gPiece g3 (d + (1, 0, 0)) :=
  extendDerivation_mem_gPiece g3 dCGen _ (map_gen_mem fine g3 fineToG3 fineToG3_fine
    dCGen_mem_fine) hu

theorem dZ_mem_g3 (d : ℤ × ℤ × ℤ) (u : Cochain) (hu : u ∈ gPiece g3 d) :
    dZ u ∈ gPiece g3 (d + (1, 0, 0)) :=
  extendDerivation_mem_gPiece g3 dZGen _ (map_gen_mem fine g3 fineToG3 fineToG3_fine
    dZGen_mem_fine) hu

theorem colorActionOn_mem_g3 (P : Mode → Bool) (e : Fin 3) (d : ℤ × ℤ × ℤ) (u : Cochain)
    (hu : u ∈ gPiece g3 d) : colorActionOn P e u ∈ gPiece g3 d := by
  have := extendDerivation_mem_gPiece g3 (fun m => if P m then colorGenerator e m else 0) 0
    (fun m => by
      have h := map_gen_mem fine g3 fineToG3 fineToG3_fine (δ := 0)
        (f := fun m => if P m then colorGenerator e m else 0) (fun m => by
          simp only [add_zero]
          split_ifs
          · exact colorGenerator_mem_fine e m
          · exact (gPiece _ _).zero_mem) m
      simpa using h) hu
  rw [add_zero] at this
  exact this

theorem gProj_g3_V00 {u : Cochain} (hu : u ∈ V00) (d : ℤ × ℤ × ℤ) : gProj g3 d u ∈ V00 :=
  V00_of_comm (gProj g3 d)
    (fun e v => (gProj_comm_zero g3 _ (colorActionOn_mem_g3 _ e) d v).symm)
    (fun e v => (gProj_comm_zero g3 _ (colorActionOn_mem_g3 _ e) d v).symm)
    (fun e v => (gProj_comm_zero g3 _ (colorActionOn_mem_g3 _ e) d v).symm) hu

/-! ## Bounds -/

/-- At most three `b₀` modes: `B ≤ T_b + 3`. -/
theorem bCount_le_tb (t : ExteriorMonomial) : (gdeg fine t).2.1 ≤ (gdeg fine t).2.2.2 + 3 := by
  simp only [gdeg, Prod.snd_sum, Prod.fst_sum, fine]
  have hpt : ∀ m ∈ t, ((m.bCount : ℕ) : ℤ) ≤ m.tbDeg + (if m.isB0 then 1 else 0) := by
    intro m _
    cases m with
    | c j a => simp [Mode.bCount, Mode.tbDeg, Mode.isB0]
    | b j a => cases j <;> simp [Mode.bCount, Mode.tbDeg, Mode.isB0]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  gcongr
  rw [Finset.sum_boole]
  have hsub : t.filter (fun m => m.isB0 = true) ⊆
      (Finset.univ : Finset (Fin 3)).image (fun a => Mode.b 0 a) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_image]
    cases m with
    | c j a => simp [Mode.isB0] at hm
    | b j a =>
      cases j with
      | zero => exact ⟨a, Finset.mem_univ _, rfl⟩
      | succ j => simp [Mode.isB0] at hm
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  simp only [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

theorem eq_zero_of_bCount_large {u : Cochain} {n j tc tb : ℤ} (hu : u ∈ gPiece fine (n, j, tc, tb))
    (hj : tb + 3 < j) : u = 0 := by
  ext t
  by_contra h
  have ht : t ∈ u.support := Finsupp.mem_support_iff.mpr h
  have hd := (mem_gPiece_iff fine).mp hu t ht
  have := bCount_le_tb t
  rw [hd] at this
  simp only at this
  omega

theorem bCount_nonneg (t : ExteriorMonomial) : 0 ≤ (gdeg fine t).2.1 := by
  simp only [gdeg, Prod.snd_sum, Prod.fst_sum, fine]
  exact Finset.sum_nonneg fun m _ => Int.natCast_nonneg _

/-! ## `d_c`-exactness in `V00` -/

theorem gdeg_fine_pureB_tc {s : ExteriorMonomial} (hs : ∀ m ∈ s, m.isB = true) :
    (gdeg fine s).2.2.1 = 0 := by
  simp only [gdeg, Prod.snd_sum, Prod.fst_sum]
  apply Finset.sum_eq_zero
  intro m hm
  have := hs m hm
  cases m with
  | b j a => rfl
  | c j a => simp [Mode.isB] at this

theorem q_primitive_pureC {N S : ℤ} (hS : S ≠ 0) {u : Cochain} (hu : u ∈ relativeCycles)
    (hud : u ∈ cochainPiece (N, 0, S)) :
    ∃ w ∈ relativeInvariants, w ∈ cochainPiece (N - 1, 0, S) ∧ u = q w := by
  rcases lt_or_ge N 0 with hN | hN
  · refine ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩
    rw [map_zero]
    ext t
    by_contra h
    have ht : t ∈ u.support := Finsupp.mem_support_iff.mpr h
    have := hud ht
    simp only [Set.mem_setOf_eq, monomialDegree, Prod.mk.injEq] at this
    omega
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M := ⟨N.toNat, (Int.toNat_of_nonneg hN).symm⟩
    exact q_exact_pureC hS hu hud

/-- Casimir pieces of fixed `(B, T_c, T_b)`. -/
def fineSplit (P : Mode → Bool) (hP : ColorStable P) (i tc tb : ℤ) : CasimirSplit Cochain where
  W k := gPiece fine (k, i, tc, tb)
  fin _ := finiteDimensional_fine _
  L := colorActionOn P
  L_mem a _ _ hv := colorActionOn_mem_fine P a hv
  action := isColorAction_colorActionOn hP

theorem Deformation.CasimirSplit.Ω_comm (C : CasimirSplit Cochain) (M : Cochain →ₗ[ℂ] Cochain)
    (hM : ∀ a v, M (C.L a v) = C.L a (M v)) (v : Cochain) : M (C.Ω v) = C.Ω (M v) := by
  simp only [CasimirSplit.Ω_apply, map_sum, hM]

theorem dC_fine_shift {k i tc tb : ℤ} {v : Cochain} (hv : v ∈ gPiece fine (k - 1, i, tc, tb)) :
    dC v ∈ gPiece fine (k, i, tc, tb) := by
  have := dC_mem_fine hv
  convert this using 2
  simp

theorem dC_mul_bmonomial (u : Cochain) {s : ExteriorMonomial} (hs : ∀ m ∈ s, m.isB = true) :
    dC (u * Finsupp.single s 1) = dC u * Finsupp.single s 1 :=
  extendDerivation_mul_bmonomial_odd dCGen isOddDer_dC dCGen_of_isB u hs

theorem LC_mul_bmonomial (e : Fin 3) (u : Cochain) {s : ExteriorMonomial}
    (hs : ∀ m ∈ s, m.isB = true) : LC e (u * Finsupp.single s 1) = LC e u * Finsupp.single s 1 :=
  extendDerivation_mul_bmonomial_even _ (isEvenDer_colorActionOn _ e)
    (fun m hm => by simp [((Mode.isC_eq_false_iff m).mpr hm)]) u hs

/-- **`d_c`-exactness on `V00` in positive `T_c`.** -/
theorem dC_exact_fine {n i tc tb : ℤ} (htc : tc ≠ 0) {x : Cochain} (hx : x ∈ V00)
    (hxd : x ∈ gPiece fine (n, i, tc, tb)) (hdx : dC x = 0) :
    ∃ y ∈ V00, y ∈ gPiece fine (n - 1, i, tc, tb) ∧ x = dC y := by
  set D : ℤ × ℤ × ℤ × ℤ := (n, i, tc, tb) with hDdef
  -- pure-`c` primitives of the coefficients
  have hcoef : ∀ s : ExteriorMonomial, ∃ w : Cochain, w ∈ pureIn Mode.isC ∧
      (∀ e, LC e w = 0) ∧ w ∈ gPiece fine (D - gdeg fine s - (1, 0, 0, 0)) ∧
      dC w = coefB s x := by
    intro s
    by_cases hxs : coefB s x = 0
    · exact ⟨0, (pureIn _).zero_mem, fun e => map_zero _, (gPiece _ _).zero_mem,
        by rw [map_zero, hxs]⟩
    have hs : ∀ m ∈ s, m.isB = true := by
      by_contra hs
      apply hxs
      apply coefB_eq_zero
      intro t _ h
      exact hs (h ▸ bPart_isB t)
    set xs := coefB s x with hxsdef
    have hpure : xs ∈ pureIn Mode.isC := coefB_mem_pureC s x
    have hdeg : xs ∈ gPiece fine (D - gdeg fine s) := coefB_mem_fine hxd s
    have htc' : (D - gdeg fine s).2.2.1 = tc := by
      simp only [hDdef, Prod.snd_sub, Prod.fst_sub, gdeg_fine_pureB_tc hs, sub_zero]
    have hcp : xs ∈ cochainPiece ((D - gdeg fine s).1, 0, tc) := by
      have := pureC_mem_cochainPiece hpure hdeg
      rwa [htc'] at this
    have hLC : ∀ e, LC e xs = 0 := fun e => by
      rw [hxsdef, ← coefB_LC, (mem_V00.mp hx e).1, map_zero]
    have hcyc : xs ∈ relativeCycles := by
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [relativeInvariants, Submodule.mem_iInf]
        intro e
        rw [LinearMap.mem_ker, ← colorActionOn_eq_of_pure (P := Mode.isC) (fun _ h => h) e hpure]
        exact hLC e
      · rw [LinearMap.mem_ker, ← dC_eq_q_of_pureC hpure, hxsdef, ← coefB_dC, hdx, map_zero]
    obtain ⟨w, hwinv, hwd, hwq⟩ := q_primitive_pureC htc hcyc hcp
    obtain ⟨hwpure, hwfine⟩ := pureC_of_cochainPiece hwd
    -- the degree of `xs` is pure-`c`
    obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr hxs
    have hgt := (mem_gPiece_iff fine).mp hdeg t ht
    rw [gdeg_fine_pureC (mem_pureIn_iff.mp hpure t ht)] at hgt
    refine ⟨w, hwpure, fun e => ?_, ?_, ?_⟩
    · rw [colorActionOn_eq_of_pure (P := Mode.isC) (fun _ h => h) e hwpure]
      exact (Submodule.mem_iInf _).mp hwinv e
    · convert hwfine using 2
      rw [← hgt] at htc' ⊢
      simp only at htc'
      rw [← htc']
      simp
    · rw [dC_eq_q_of_pureC hwpure, ← hwq]
  choose w hwpure hwLC hwdeg hwd using hcoef
  set I := x.support.image bPart
  set y := ∑ s ∈ I, w s * Finsupp.single s 1 with hydef
  have hy_dC : dC y = x := by
    rw [hydef, map_sum]
    rw [Finset.sum_congr rfl (fun s hs => dC_mul_bmonomial (w s) (isB_of_mem_image hs))]
    simp only [hwd]
    exact sum_coefB x I (bPart_mem_image x)
  have hy_LC : ∀ e, LC e y = 0 := by
    intro e
    rw [hydef, map_sum]
    apply Finset.sum_eq_zero
    intro s hs
    rw [LC_mul_bmonomial e (w s) (isB_of_mem_image hs), hwLC, zero_mul]
  have hy_deg : y ∈ gPiece fine (n - 1, i, tc, tb) := by
    rw [hydef]
    apply Submodule.sum_mem
    intro s _
    have := mul_mem_gPiece fine (hwdeg s) (single_mem_gPiece fine s 1)
    rw [show D - gdeg fine s - (1, 0, 0, 0) + gdeg fine s = D - (1, 0, 0, 0) by abel] at this
    convert this using 2
    simp [hDdef]
  -- restore `L^Z`-invariance
  let C₁ := fineSplit Mode.isZ colorStable_isZ i tc tb
  obtain ⟨y₁, hy₁, hΩ₁, hM₁, hE₁⟩ := C₁.exists_ker_preimage (fun e => LC e)
    (fun j _ _ hv => colorActionOn_mem_fine _ j hv)
    (fun j v => C₁.Ω_comm (LC j) (fun a w => LC_LZ j a w) v)
    dC (n := n - 1) (m := n) (fun hv => dC_fine_shift hv)
    (fun v => C₁.Ω_comm dC (fun a w => dC_LZ a w) v) hy_deg hy_LC
    (by
      rw [hy_dC, CasimirSplit.Ω_apply]
      apply Finset.sum_eq_zero
      intro a _
      change LZ a (LZ a x) = 0
      rw [(mem_V00.mp hx a).2.1, map_zero])
  have hZ₁ : ∀ a, LZ a y₁ = 0 := C₁.L_eq_zero_of_Ω hy₁ hΩ₁
  -- restore `L^{B₀}`-invariance
  let C₂ := fineSplit Mode.isB0 colorStable_isB0 i tc tb
  obtain ⟨y₂, hy₂, hΩ₂, hM₂, hE₂⟩ := C₂.exists_ker_preimage
    (Sum.elim (fun e => LC e) (fun e => LZ e))
    (fun j _ _ hv => by cases j <;> exact colorActionOn_mem_fine _ _ hv)
    (fun j v => by
      cases j with
      | inl j => exact C₂.Ω_comm (LC j) (fun a w => LC_LB0 j a w) v
      | inr j => exact C₂.Ω_comm (LZ j) (fun a w => LZ_LB0 j a w) v)
    dC (n := n - 1) (m := n) (fun hv => dC_fine_shift hv)
    (fun v => C₂.Ω_comm dC (fun a w => dC_LB0 a w) v) hy₁
    (fun j => by cases j with
      | inl j => exact hM₁ j
      | inr j => exact hZ₁ j)
    (by
      rw [hE₁, hy_dC, CasimirSplit.Ω_apply]
      apply Finset.sum_eq_zero
      intro a _
      change LB0 a (LB0 a x) = 0
      rw [(mem_V00.mp hx a).2.2, map_zero])
  have hB₂ : ∀ a, LB0 a y₂ = 0 := C₂.L_eq_zero_of_Ω hy₂ hΩ₂
  refine ⟨y₂, mem_V00.mpr fun e => ⟨hM₂ (.inl e), hM₂ (.inr e), hB₂ e⟩, hy₂, ?_⟩
  rw [hE₂, hE₁, hy_dC]

/-! ## The staircase for `d_c + d_Z` -/

/-- The staircase over the `b`-count, at fixed `(T_c, T_b)`. -/
def kStair (tc tb : ℤ) : Staircase ℂ Cochain where
  P i n := V00 ⊓ gPiece fine (n, (i : ℤ), tc, tb)
  Q := dC
  δ := dZ
  A i n := (V00 ⊓ gPiece fine (n - 1, (i : ℤ), tc, tb)).map dC
  Q_mem {i n x} hx := ⟨dC_V00 hx.1, by
    have := dC_mem_fine hx.2
    convert this using 2
    simp⟩
  δ_mem {i n x} hx := ⟨dZ_V00 hx.1, by
    have := dZ_mem_fine hx.2
    convert this using 2
    simp⟩
  QQ _ := dC_dC _
  δδ _ := dZ_dZ _
  Qδ _ := dC_dZ_anticomm _
  indep i n := disjoint_of_le_ker fine (d := (n, (i : ℤ), tc, tb)) inf_le_right
    (iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker]
      apply gProj_of_mem_ne fine _ hy.2
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
  A_le i n := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    refine ⟨dC_V00 hy.1, ?_⟩
    exact dC_fine_shift hy.2
  A_cycle {i n x} hx := by
    obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hx
    exact dC_dC y
  bdry {i n x} hx := Submodule.mem_map.mpr ⟨x, by simpa using hx, rfl⟩
  A_δ {i n x} hx := by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨-dZ y, ⟨Submodule.neg_mem _ (dZ_V00 hy.1), ?_⟩, ?_⟩
    · apply Submodule.neg_mem
      have := dZ_mem_fine hy.2
      convert this using 2
      simp
    · rw [map_neg, neg_eq_iff_eq_neg]
      exact eq_neg_of_add_eq_zero_left (dC_dZ_anticomm y)
  exact {i n x} hx _ := by
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hx
    exact ⟨0, Submodule.zero_mem _, c, hc, by rw [map_zero, zero_add]⟩

theorem kStair_D (tc tb : ℤ) (v : Cochain) : (kStair tc tb).D v = dC v + dZ v := rfl

/-- **Künneth at positive `T_c`.** -/
theorem kunneth_tc {n tc tb : ℤ} (htc : tc ≠ 0) {z : Cochain} (hz : z ∈ V00)
    (hzd : z ∈ gPiece g3 (n, tc, tb)) (hD : dC z + dZ z = 0) :
    ∃ w ∈ V00, w ∈ gPiece g3 (n - 1, tc, tb) ∧ z = dC w + dZ w := by
  set S := kStair tc tb
  have hIH : ∀ K, S.IH K := fun K i _ n x hx hQ => by
    obtain ⟨y, hy, hyd, rfl⟩ := dC_exact_fine htc hx.1 hx.2 hQ
    exact Submodule.mem_map.mpr ⟨y, ⟨hy, hyd⟩, rfl⟩
  have hF : S.F (tb.toNat + 4) n = ⊥ := by
    refine eq_bot_iff.mpr (iSup₂_le fun j hj => ?_)
    intro v hv
    exact (Submodule.mem_bot ℂ).mpr (eq_zero_of_bCount_large hv.2 (by omega))
  have hz0 : z ∈ S.F 0 n := by
    rw [← sum_gProj fine z]
    refine Submodule.sum_mem _ fun d hd => ?_
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
    have h3 : gdeg g3 t = (n, tc, tb) := (mem_gPiece_iff g3).mp hzd t ht
    rw [gdeg_g3_eq] at h3
    have hB := bCount_nonneg t
    apply S.mem_F_of_mem_P (Nat.zero_le ((gdeg fine t).2.1.toNat))
    refine ⟨gProj_fine_V00 hz _, ?_⟩
    simp only [fineToG3, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq] at h3
    have key : (n, (((gdeg fine t).2.1.toNat : ℕ) : ℤ), tc, tb) = gdeg fine t :=
      Prod.ext h3.1.symm (Prod.ext (Int.toNat_of_nonneg hB) (Prod.ext h3.2.1.symm h3.2.2.symm))
    rw [key]
    exact gProj_mem fine _ z
  obtain ⟨w, hw, hzw⟩ := S.assembly (hIH _) hF hz0 hD
  have hle : S.F 0 (n - 1) ≤ V00 ⊓ gPiece g3 (n - 1, tc, tb) :=
    iSup₂_le fun j _ => inf_le_inf_left _ (fine_le_g3 _)
  exact ⟨w, (hle hw).1, (hle hw).2, hzw⟩

/-- **Künneth**: `d_c + d_Z` is exact on `V00` in positive `T`. -/
theorem kunneth {n T : ℤ} (hT : T ≠ 0) {z : Cochain} (hz : z ∈ V00)
    (hzd : z ∈ gPiece coarse (n, T)) (hD : dC z + dZ z = 0) :
    ∃ w ∈ V00, w ∈ gPiece coarse (n - 1, T) ∧ z = dC w + dZ w := by
  have hcomp : ∀ d : ℤ × ℤ × ℤ, ∃ w ∈ V00, w ∈ gPiece coarse (n - 1, T) ∧
      gProj g3 d z = dC w + dZ w := by
    intro d
    by_cases h0 : gProj g3 d z = 0
    · exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, by rw [h0, map_zero, map_zero,
        add_zero]⟩
    have hzd3 : gProj g3 d z ∈ gPiece g3 d := gProj_mem g3 d z
    have hzdc : gProj g3 d z ∈ gPiece coarse (n, T) := gProj_mem_of_mem g3 coarse hzd d
    have hdc : g3ToCoarse d = (n, T) := by
      by_contra hne
      exact h0 (eq_zero_of_mem_ne coarse (g3_le_coarse d hzd3) hzdc hne)
    obtain ⟨n', tc, tb⟩ := d
    simp only [g3ToCoarse, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq] at hdc
    obtain ⟨rfl, htT⟩ := hdc
    have hzdV : gProj g3 (n', tc, tb) z ∈ V00 := gProj_g3_V00 hz _
    have hDzd : dC (gProj g3 (n', tc, tb) z) + dZ (gProj g3 (n', tc, tb) z) = 0 := by
      have := congrArg (gProj g3 ((n', tc, tb) + (1, 0, 0))) hD
      rwa [map_add, gProj_comm g3 dC (1, 0, 0) dC_mem_g3, gProj_comm g3 dZ (1, 0, 0) dZ_mem_g3,
        map_zero] at this
    by_cases htc : tc = 0
    · subst htc
      have htb : tb ≠ 0 := by omega
      obtain ⟨w', hw'V, hw'd, hw'⟩ := kunneth_tc htb (swap_V00 hzdV) (swap_mem_g3 hzd3)
        (by rw [← swap_dZ, ← swap_dC, ← map_add, add_comm, hDzd, map_zero])
      refine ⟨swap w', swap_V00 hw'V, ?_, ?_⟩
      · have := g3_le_coarse _ (swap_mem_g3 hw'd)
        convert this using 2
        simp [g3ToCoarse, htT]
      · rw [← swap_swap (gProj g3 _ z), hw', map_add, swap_dC, swap_dZ, add_comm]
    · obtain ⟨w, hwV, hwd, hw⟩ := kunneth_tc htc hzdV hzd3 hDzd
      refine ⟨w, hwV, ?_, hw⟩
      have := g3_le_coarse _ hwd
      convert this using 2
      simp [g3ToCoarse, htT]
  choose w hwV hwd hw using hcomp
  refine ⟨∑ d ∈ z.support.image (gdeg g3), w d, Submodule.sum_mem _ fun d _ => hwV d,
    Submodule.sum_mem _ fun d _ => hwd d, ?_⟩
  conv_lhs => rw [← sum_gProj g3 z]
  rw [map_sum, map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => hw d

end KhanSL2
