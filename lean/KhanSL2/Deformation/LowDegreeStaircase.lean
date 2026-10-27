module

public import KhanSL2.Deformation.SplitMap
public import KhanSL2.Deformation.SourceHomotopy
public import KhanSL2.Chains.Psi

@[expose] public section

/-!
# The two staircases of paper Prop. 5.3 (blueprint `prop:lowdegrees`)

For `ℓ ∈ {0, 1}`, parity `ε` and offset `s₀`, the staircase `lowStair` has pieces
`P i n = (invariant cochains of degree (n + ε, 2i + ε, s₀ + (2 - ℓ) i))`, differential `Q`,
deformation `δ_ℓ`, and distinguished cycles `A i n` = the cocycles whose class lies in `φ(A_d)`
(`goodCycles`). Its energy `(1 + ℓ) S - B = (1 + ℓ) s₀ - ε` is constant; when it is nonzero,
the source contraction gives the `exact` field and the total acyclicity (`totalOne_exact`,
`totalZero_exact`) gives `DExact`.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-! ## `δᴬ` is homogeneous -/

namespace Source

open SourcePresentation

theorem deltaA_degree {ℓ : ℕ} (hℓ : ℓ ≤ 1) {d : Degree} {a : Source} (ha : a ∈ piece d) :
    deltaA ℓ hℓ a ∈ piece (d + deltaShift ℓ) := by
  obtain ⟨e, he, rfl⟩ := ha
  induction he with
  | zero d => rw [mk_zero, map_zero]; exact Submodule.zero_mem _
  | scalar r =>
    change deltaA ℓ hℓ (algebraMap ℂ Source r) ∈ _
    rw [deltaA_algebraMap]; exact Submodule.zero_mem _
  | x i =>
    change deltaA ℓ hℓ (X i) ∈ _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hℓ with rfl | rfl
    · rw [deltaA_zero_X]
      apply Submodule.smul_mem
      convert Y_mem (i + 1) using 2
      simp only [deltaShift, Prod.mk_add_mk]
      refine Prod.ext (by norm_num) (Prod.ext (by norm_num) ?_)
      push_cast; ring
    · rw [deltaA_one_X]
      apply Submodule.smul_mem
      convert Y_mem i using 2
      simp only [deltaShift, Prod.mk_add_mk]
      refine Prod.ext (by norm_num) (Prod.ext (by norm_num) ?_)
      push_cast; ring
  | y i => change deltaA ℓ hℓ (Y i) ∈ _; rw [deltaA_Y]; exact Submodule.zero_mem _
  | add _ _ ha hb =>
    rw [mk_add, map_add]
    exact Submodule.add_mem _ ha hb
  | @mul d e a b ha' hb' ha hb =>
    rw [mk_mul, deltaA_mul]
    refine Submodule.add_mem _ ?_ ?_
    · have := mul_mem ha ⟨b, hb', rfl⟩
      convert this using 2
      abel
    · have hpa : parity (mk a) ∈ piece d := by
        rw [parity_of_mem ⟨a, ha', rfl⟩]
        exact Submodule.smul_mem _ _ ⟨a, ha', rfl⟩
      have := mul_mem hpa hb
      convert this using 2
      abel

end Source

/-! ## Vanishing pieces -/

/-- Each generator has weight at least one and `b`-count at most one. -/
theorem card_le_weight (s : ExteriorMonomial) : (s.card : ℤ) ≤ (monomialDegree s).2.2 := by
  simp only [monomialDegree]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  exact_mod_cast Finset.sum_le_sum fun m _ => by cases m <;> simp [Mode.weight]

theorem bCount_le_card (s : ExteriorMonomial) : (monomialDegree s).2.1 ≤ (s.card : ℤ) := by
  simp only [monomialDegree]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  exact_mod_cast Finset.sum_le_sum fun m _ => by cases m <;> simp [Mode.bCount]

theorem bCount_nonneg' (s : ExteriorMonomial) : 0 ≤ (monomialDegree s).2.1 := by
  simp only [monomialDegree]; positivity

theorem Mode.energyOne_ge (m : Mode) : 1 ≤ m.energyOne := by
  cases m <;> simp only [Mode.energyOne, Mode.weight, Mode.bCount] <;> push_cast <;> omega

/-- Every generator has energy `2S - B ≥ 1`. -/
theorem card_le_energy (s : ExteriorMonomial) :
    (s.card : ℤ) ≤ 2 * (monomialDegree s).2.2 - (monomialDegree s).2.1 := by
  rw [← monomialEnergyOne_eq, monomialEnergyOne, Finset.card_eq_sum_ones, Nat.cast_sum]
  exact Finset.sum_le_sum fun m _ => by simpa using Mode.energyOne_ge m

/-- All generators except the three `b₀ᵃ` have `T = S - B ≥ 1`. -/
theorem card_le_T_add_three (s : ExteriorMonomial) :
    (s.card : ℤ) ≤ (monomialDegree s).2.2 - (monomialDegree s).2.1 + 3 := by
  have hsplit : (s.card : ℤ) = ((s.filter fun m => m.isB0 = true).card : ℤ) +
      ((s.filter fun m => ¬ m.isB0 = true).card : ℤ) := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
  have hb0 : (s.filter fun m => m.isB0 = true).card ≤ 3 := by
    have hsub : s.filter (fun m => m.isB0 = true) ⊆
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
    simpa using this
  have hT : ((s.filter fun m => ¬ m.isB0 = true).card : ℤ) ≤
      (monomialDegree s).2.2 - (monomialDegree s).2.1 := by
    simp only [monomialDegree]
    push_cast
    rw [← Finset.sum_sub_distrib, Finset.card_eq_sum_ones, Nat.cast_sum,
      ← Finset.sum_filter_add_sum_filter_not s (fun m => m.isB0 = true)
        (fun m => (m.weight : ℤ) - m.bCount)]
    have h1 : 0 ≤ ∑ m ∈ s.filter (fun m => m.isB0 = true), ((m.weight : ℤ) - m.bCount) :=
      Finset.sum_nonneg fun m _ => by
        cases m <;> simp only [Mode.weight, Mode.bCount] <;> push_cast <;> omega
    have h2 : ∑ m ∈ s.filter (fun m => ¬ m.isB0 = true), ((1 : ℕ) : ℤ) ≤
        ∑ m ∈ s.filter (fun m => ¬ m.isB0 = true), ((m.weight : ℤ) - m.bCount) :=
      Finset.sum_le_sum fun m hm => by
        rw [Finset.mem_filter] at hm
        cases m with
        | c j a => simp [Mode.weight, Mode.bCount]
        | b j a =>
          cases j with
          | zero => simp [Mode.isB0] at hm
          | succ j => simp [Mode.weight, Mode.bCount]
    linarith
  rw [hsplit]
  have : ((s.filter fun m => m.isB0 = true).card : ℤ) ≤ 3 := by exact_mod_cast hb0
  linarith

theorem cochainPiece_eq_bot_of {d : Degree}
    (h : ∀ s : ExteriorMonomial, monomialDegree s = d → False) : cochainPiece d = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Submodule.mem_bot]
  ext s
  by_contra hs
  exact h s (hu (Finsupp.mem_support_iff.mpr hs))

theorem source_piece_eq_bot {d : Degree} (hd : cochainPiece d = ⊥) : Source.piece d = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  apply phi_injective
  have h : phi a ∈ cohomologyPiece d := phi_degree ha
  have hc : cohomologyPiece d = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    have : (y : Cochain) = 0 := by
      have := hy
      simp only [Submodule.mem_comap, Submodule.coe_subtype, hd, Submodule.mem_bot] at this
      exact this
    rw [Submodule.mem_bot]
    have hy0 : y = 0 := Subtype.ext this
    rw [hy0, map_zero]
  rw [hc, Submodule.mem_bot] at h
  rw [h, map_zero]

/-! ## Good cycles -/

/-- Cocycles of degree `d` whose class lies in `φ(A_d)`. -/
def goodCycles (d : Degree) : Submodule ℂ Cochain where
  carrier := {u | u ∈ cochainPiece d ∧ ∃ hu : u ∈ relativeCycles, ∃ a ∈ Source.piece d,
    phi a = classOf u hu}
  zero_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _, 0, Submodule.zero_mem _, by
    rw [map_zero]; rfl⟩
  add_mem' := by
    rintro u v ⟨hud, hu, a, ha, hau⟩ ⟨hvd, hv, b, hb, hbv⟩
    refine ⟨Submodule.add_mem _ hud hvd, Submodule.add_mem _ hu hv, a + b,
      Submodule.add_mem _ ha hb, ?_⟩
    rw [map_add, hau, hbv, classOf_add']
  smul_mem' := by
    rintro r u ⟨hud, hu, a, ha, hau⟩
    refine ⟨Submodule.smul_mem _ r hud, Submodule.smul_mem _ r hu, r • a,
      Submodule.smul_mem _ r ha, ?_⟩
    rw [map_smul, hau, classOf_smul']

theorem mem_goodCycles {d : Degree} {u : Cochain} :
    u ∈ goodCycles d ↔ u ∈ cochainPiece d ∧ ∃ hu : u ∈ relativeCycles, ∃ a ∈ Source.piece d,
      phi a = classOf u hu := Iff.rfl

/-- Every homogeneous invariant cocycle of degree `d` is good. -/
def Surj (d : Degree) : Prop :=
  ∀ u (hu : u ∈ relativeCycles), u ∈ cochainPiece d → ∃ a ∈ Source.piece d, phi a = classOf u hu

theorem good_of_surj {d : Degree} (h : Surj d) {u : Cochain} (hu : u ∈ relativeCycles)
    (hud : u ∈ cochainPiece d) : u ∈ goodCycles d := ⟨hud, hu, h u hu hud⟩

theorem surj_of_bot {d : Degree} (hd : cochainPiece d = ⊥) : Surj d := by
  intro u hu hud
  rw [hd, Submodule.mem_bot] at hud
  subst hud
  exact ⟨0, Submodule.zero_mem _, by rw [map_zero]; rfl⟩

theorem boundary_good {d : Degree} {v : Cochain} (hv : v ∈ relativeInvariants)
    (hvd : q v ∈ cochainPiece d) : q v ∈ goodCycles d := by
  have hc : q v ∈ relativeCycles := ⟨invariant_q hv, by
    change q (q v) = 0; exact q_square_zero v⟩
  refine ⟨hvd, hc, 0, Submodule.zero_mem _, ?_⟩
  rw [map_zero, eq_comm, classOf_eq_zero_iff]
  exact ⟨v, hv, rfl⟩

/-! ## The staircase -/

/-- The degree of the piece `P i n`. -/
def degOf (ℓ ε : ℕ) (s₀ : ℤ) (i : ℕ) (n : ℤ) : Degree :=
  (n + ε, 2 * (i : ℤ) + ε, s₀ + (2 - (ℓ : ℤ)) * i)

theorem degOf_q (ℓ ε : ℕ) (s₀ : ℤ) (i : ℕ) (n : ℤ) :
    degOf ℓ ε s₀ i n + (1, 0, 0) = degOf ℓ ε s₀ i (n + 1) := by
  simp only [degOf, Prod.mk_add_mk, add_zero]
  congr 1; ring

theorem degOf_delta (ℓ ε : ℕ) (s₀ : ℤ) (i : ℕ) (n : ℤ) :
    degOf ℓ ε s₀ i n + deltaShift ℓ = degOf ℓ ε s₀ (i + 1) (n + 1) := by
  simp only [degOf, deltaShift, Prod.mk_add_mk]
  push_cast
  refine Prod.ext (by ring) (Prod.ext (by ring) (by ring))

theorem energyOf_degOf {ℓ : ℕ} (hℓ : ℓ ≤ 1) (ε : ℕ) (s₀ : ℤ) (i : ℕ) (n : ℤ) :
    Source.energyOf ℓ (degOf ℓ ε s₀ i n) = (1 + ℓ) * s₀ - ε := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hℓ with rfl | rfl <;>
    simp only [Source.energyOf, degOf] <;> push_cast <;> ring

theorem classOf_sub' (u v : Cochain) (hu : u ∈ relativeCycles) (hv : v ∈ relativeCycles)
    (huv : u - v ∈ relativeCycles) : classOf (u - v) huv = classOf u hu - classOf v hv := by
  change Submodule.Quotient.mk (p := relativeBoundaries) (⟨u - v, huv⟩ : CycleSpace) =
    Submodule.Quotient.mk (p := relativeBoundaries) (⟨u, hu⟩ : CycleSpace) -
      Submodule.Quotient.mk (p := relativeBoundaries) (⟨v, hv⟩ : CycleSpace)
  rw [← Submodule.Quotient.mk_sub]
  rfl

/-- The `exact` field: modulo boundaries, `δ̄`-closed good cycles are `δ` of good cycles. -/
theorem lowStair_exact {ℓ : ℕ} (hℓ : ℓ ≤ 1) {ε : ℕ} (hε : ε ≤ 1) {s₀ : ℤ}
    (hE : (1 + (ℓ : ℤ)) * s₀ - ε ≠ 0)
    {i : ℕ} {n : ℤ} {x : Cochain} (hx : x ∈ goodCycles (degOf ℓ ε s₀ i n))
    (hy : ∃ y ∈ relativeInvariants ⊓ cochainPiece (degOf ℓ ε s₀ (i + 1) n), delta ℓ x = q y) :
    ∃ x' ∈ goodCycles (degOf ℓ ε s₀ (i - 1) (n - 1)),
      ∃ c ∈ relativeInvariants ⊓ cochainPiece (degOf ℓ ε s₀ i (n - 1)), x = delta ℓ x' + q c := by
  obtain ⟨hxd, hx, a, ha, hax⟩ := hx
  obtain ⟨y, hyP, hxy⟩ := hy
  have hδ : deltaBar ℓ hℓ (phi a) = 0 := by
    rw [hax, deltaBar_classOf, classOf_eq_zero_iff]
    exact ⟨y, hyP.1, hxy.symm⟩
  obtain ⟨a', ha', haa'⟩ := Source.phi_deltaBar_exact hℓ (by
    rw [energyOf_degOf hℓ]; exact_mod_cast hE) ha hδ
  have key : ∃ x' ∈ goodCycles (degOf ℓ ε s₀ (i - 1) (n - 1)),
      delta ℓ x' ∈ cochainPiece (degOf ℓ ε s₀ i n) ∧
        ∃ hx' : delta ℓ x' ∈ relativeCycles, classOf (delta ℓ x') hx' = phi a := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have hbot : cochainPiece (degOf ℓ ε s₀ 0 n - deltaShift ℓ) = ⊥ :=
        cochainPiece_eq_bot_of fun s hs => by
          have := bCount_nonneg' s
          rw [hs] at this
          simp only [degOf, deltaShift, Prod.snd_sub, Prod.fst_sub] at this
          omega
      have ha0 : a' = 0 := by
        have := source_piece_eq_bot hbot ▸ ha'
        exact (Submodule.mem_bot ℂ).mp this
      have hc0 : (delta ℓ 0 : Cochain) ∈ relativeCycles := by
        rw [map_zero]; exact Submodule.zero_mem _
      refine ⟨0, Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _, hc0, ?_⟩
      rw [haa', ha0, map_zero phi, map_zero (deltaBar ℓ hℓ), classOf_eq_zero_iff]
      exact ⟨0, Submodule.zero_mem _, by rw [map_zero, map_zero]⟩
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hdeg : degOf ℓ ε s₀ (k + 1) n - deltaShift ℓ = degOf ℓ ε s₀ k (n - 1) := by
        rw [sub_eq_iff_eq_add, degOf_delta, sub_add_cancel]
      rw [hdeg] at ha'
      obtain ⟨⟨x', hx'⟩, hx'd, hcls⟩ := phi_degree ha'
      refine ⟨x', ⟨hx'd, hx', a', ha', hcls.symm⟩, ?_, delta_mem_cycles hℓ hx', ?_⟩
      · have := delta_degree hℓ hx'd
        rwa [degOf_delta, sub_add_cancel] at this
      · rw [haa', ← deltaBar_classOf ℓ hℓ x' hx']
        exact congrArg (deltaBar ℓ hℓ) hcls
  obtain ⟨x', hx'good, hδd, hδc, hcls⟩ := key
  have hdiff : x - delta ℓ x' ∈ relativeCycles := Submodule.sub_mem _ hx hδc
  have hzero : classOf (x - delta ℓ x') hdiff = 0 := by
    rw [classOf_sub' x (delta ℓ x') hx hδc hdiff, hcls, hax, sub_self]
  obtain ⟨c, hc, hcd, hcx⟩ :=
    exists_homogeneous_primitive hdiff (Submodule.sub_mem _ hxd hδd) hzero
  refine ⟨x', hx'good, c, ⟨hc, ?_⟩, ?_⟩
  · rwa [show degOf ℓ ε s₀ i n - (1, 0, 0) = degOf ℓ ε s₀ i (n - 1) by
      rw [sub_eq_iff_eq_add, degOf_q, sub_add_cancel]] at hcd
  · rw [← hcx]; abel

/-- **The staircase of paper Prop. 5.3** for `δ_ℓ`. -/
def lowStair (ℓ : ℕ) (hℓ : ℓ ≤ 1) (ε : ℕ) (hε : ε ≤ 1) (s₀ : ℤ)
    (hE : (1 + (ℓ : ℤ)) * s₀ - ε ≠ 0) :
    Staircase ℂ Cochain where
  P i n := relativeInvariants ⊓ cochainPiece (degOf ℓ ε s₀ i n)
  Q := q
  δ := delta ℓ
  A i n := goodCycles (degOf ℓ ε s₀ i n)
  Q_mem {i n x} hx := ⟨invariant_q hx.1, by rw [← degOf_q]; exact q_degree hx.2⟩
  δ_mem {i n x} hx := ⟨invariant_delta hℓ hx.1, by rw [← degOf_delta]; exact delta_degree hℓ hx.2⟩
  QQ _ := q_square_zero _
  δδ _ := delta_delta hℓ _
  Qδ hx := by rw [q_delta_anticomm hℓ hx.1, neg_add_cancel]
  indep i n := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hker : (⨆ j, ⨆ (_ : i + 1 ≤ j), relativeInvariants ⊓ cochainPiece (degOf ℓ ε s₀ j n)) ≤
        LinearMap.ker (cochainProjection (degOf ℓ ε s₀ i n)) :=
      iSup₂_le fun j hj y hy => by
        rw [LinearMap.mem_ker]
        apply cochainProjection_of_mem_ne _ hy.2
        intro h
        simp only [degOf, Prod.mk.injEq] at h
        omega
    have := hker hx'
    rwa [LinearMap.mem_ker, cochainProjection_of_mem hx.2] at this
  A_le i n x hx := by
    obtain ⟨hxd, hx, -⟩ := hx
    exact Submodule.mem_inf.mpr ⟨hx.1, hxd⟩
  A_cycle {i n x} hx := by
    obtain ⟨-, hx, -⟩ := hx
    exact hx.2
  bdry {i n x} hx := boundary_good hx.1 (by rw [← degOf_q]; exact q_degree hx.2)
  A_δ {i n x} hx := by
    obtain ⟨hxd, hx, a, ha, hax⟩ := hx
    refine ⟨by rw [← degOf_delta]; exact delta_degree hℓ hxd, delta_mem_cycles hℓ hx,
      deltaA ℓ hℓ a, by rw [← degOf_delta]; exact Source.deltaA_degree hℓ ha, ?_⟩
    rw [phi_deltaA, hax]
    rfl
  exact hx hy := lowStair_exact hℓ hε hE hx hy

end KhanSL2
