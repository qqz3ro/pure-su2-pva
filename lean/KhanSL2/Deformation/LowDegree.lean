module

public import KhanSL2.Deformation.LowDegreeStaircase
public import KhanSL2.Conditional.Coefficients

@[expose] public section

/-!
# The low-degree step (paper Prop. 5.3, blueprint `prop:lowdegrees`)

* `lowStair_DExact_one`, `lowStair_DExact_zero`: the total differentials `D₁`, `D₀` are exact on
  the staircase pieces (from `totalOne_exact` and `totalZero_exact`);
* `surj_zero`: `𝒩_B^0 = 0` (bottom edge of the `D₁` staircase);
* `surj_one`: `𝒩_B^1 = 0`, by induction on spin: `δ₁` is injective modulo `φ(A)` and `δ₀` is
  surjective onto the cycles two spins higher;
* `psi_injective_iff_surj`: injectivity of `ψ` is surjectivity of `φ` onto each cohomology piece;
* **`lowDegreeStep : Conditional.LowDegreeStep`**.
-/

noncomputable section

namespace KhanSL2

open Deformation

/-! ## The CE grading as a generator grading -/

/-- The degree `(1, B, S)` of a generator. -/
def degMode (m : Mode) : Degree := (1, (m.bCount : ℤ), (m.weight : ℤ))

theorem gdeg_degMode (s : ExteriorMonomial) : gdeg degMode s = monomialDegree s := by
  simp only [gdeg, degMode, monomialDegree]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem gdeg_degMode_fun : gdeg degMode = monomialDegree := funext gdeg_degMode

theorem cochainPiece_eq_gPiece (d : Degree) : cochainPiece d = gPiece degMode d := by
  rw [gPiece, gdeg_degMode_fun]; rfl

theorem cochainProjection_eq_gProj (d : Degree) : cochainProjection d = gProj degMode d := by
  rw [gProj, gdeg_degMode_fun]; rfl

theorem sum_cochainProjection (v : Cochain) :
    ∑ d ∈ v.support.image monomialDegree, cochainProjection d v = v := by
  have := sum_gProj degMode v
  rw [gdeg_degMode_fun] at this
  simpa only [cochainProjection_eq_gProj] using this

/-- `(B, S) ↦ (cochain degree, S - B)`. -/
def degToCoarse : Degree →+ ℤ × ℤ where
  toFun d := (d.1, d.2.2 - d.2.1)
  map_zero' := rfl
  map_add' d e := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    congr 1; ring

theorem degToCoarse_degMode (m : Mode) : degToCoarse (degMode m) = coarse m := by
  cases m <;> simp [degToCoarse, degMode, coarse, Mode.tdeg, Mode.weight, Mode.bCount]

theorem cochainPiece_le_coarse (d : Degree) :
    cochainPiece d ≤ gPiece coarse (d.1, d.2.2 - d.2.1) := by
  rw [cochainPiece_eq_gPiece]
  have h := gPiece_le_map degMode degToCoarse d
  have he : (fun m => degToCoarse (degMode m)) = coarse := funext degToCoarse_degMode
  rw [he] at h
  exact h

theorem gdeg_coarse_eq (s : ExteriorMonomial) : gdeg coarse s = degToCoarse (monomialDegree s) := by
  rw [← gdeg_degMode, gdeg, gdeg, map_sum]
  simp only [degToCoarse_degMode]

/-- The parity of the `b`-count. -/
def gPar (m : Mode) : ZMod 2 := ((m.bCount : ℤ) : ZMod 2)

/-- `(N, B, S) ↦ B mod 2`. -/
def degToPar : Degree →+ ZMod 2 :=
  (Int.castAddHom (ZMod 2)).comp ((AddMonoidHom.fst ℤ ℤ).comp (AddMonoidHom.snd ℤ (ℤ × ℤ)))

theorem degToPar_apply (d : Degree) : degToPar d = ((d.2.1 : ℤ) : ZMod 2) := rfl

theorem degToPar_degMode (m : Mode) : degToPar (degMode m) = gPar m := rfl

theorem cochainPiece_le_par (d : Degree) :
    cochainPiece d ≤ gPiece gPar ((d.2.1 : ℤ) : ZMod 2) := by
  rw [cochainPiece_eq_gPiece]
  have h := gPiece_le_map degMode degToPar d
  exact h

theorem gdeg_gPar_eq (s : ExteriorMonomial) : gdeg gPar s = degToPar (monomialDegree s) := by
  rw [← gdeg_degMode, gdeg, gdeg, map_sum]
  rfl

theorem q_mem_par {e : ZMod 2} {u : Cochain} (hu : u ∈ gPiece gPar e) : q u ∈ gPiece gPar e := by
  show extendDerivation qGenerator u ∈ _
  have := extendDerivation_mem_gPiece gPar qGenerator (degToPar (1, 0, 0))
    (map_gen_mem degMode gPar degToPar degToPar_degMode (fun m => by
      rw [← cochainPiece_eq_gPiece]
      convert qGenerator_degree m using 2
      simp only [degMode, Prod.mk_add_mk, add_zero]
      norm_num)) hu
  have h0 : degToPar (1, 0, 0) = 0 := by rw [degToPar_apply]; simp
  rwa [h0, add_zero] at this

theorem delta_mem_par {ℓ : ℕ} (hℓ : ℓ ≤ 1) {e : ZMod 2} {u : Cochain} (hu : u ∈ gPiece gPar e) :
    delta ℓ u ∈ gPiece gPar e := by
  have := extendDerivation_mem_gPiece gPar (deltaGenerator ℓ) (degToPar (deltaShift ℓ))
    (map_gen_mem degMode gPar degToPar degToPar_degMode (fun m => by
      rw [← cochainPiece_eq_gPiece]; exact deltaGenerator_degree hℓ m)) hu
  have h2 : degToPar (deltaShift ℓ) = 0 := by
    rw [degToPar_apply]; simp only [deltaShift]; decide
  rwa [h2, add_zero] at this

theorem colorAction_mem_par (a : Fin 3) {e : ZMod 2} {u : Cochain} (hu : u ∈ gPiece gPar e) :
    colorAction a u ∈ gPiece gPar e := by
  have := extendDerivation_mem_gPiece gPar (colorGenerator a) (degToPar 0)
    (map_gen_mem degMode gPar degToPar degToPar_degMode (fun m => by
      rw [← cochainPiece_eq_gPiece, add_zero]; exact colorGenerator_degree a m)) hu
  rwa [map_zero, add_zero] at this

/-! ## Pieces of the staircase -/

section Stair

variable {ℓ : ℕ} (hℓ : ℓ ≤ 1) {ε : ℕ} (hε : ε ≤ 1) {s₀ : ℤ} (hE : (1 + (ℓ : ℤ)) * s₀ - ε ≠ 0)

theorem lowStair_low : (lowStair ℓ hℓ ε hε s₀ hE).Low := by
  intro i n hn
  change relativeInvariants ⊓ cochainPiece (degOf ℓ ε s₀ i n) = ⊥
  rw [cochainPiece_eq_bot_of fun s hs => by
    have h1 := bCount_le_card s
    have h2 : (monomialDegree s).1 = (s.card : ℤ) := rfl
    rw [hs] at h1 h2
    simp only [degOf] at h1 h2
    omega, inf_bot_eq]

theorem lowStair_IH {I : ℕ} (hd : ∀ d : Degree, d.2.1 < 2 * (I : ℤ) + ε → Surj d) :
    (lowStair ℓ hℓ ε hε s₀ hE).IH I := by
  intro i hi n x hx hQx
  exact good_of_surj (hd _ (by simp only [degOf]; omega)) ⟨hx.1, hQx⟩ hx.2

theorem lowStair_F_le (n : ℤ) :
    (lowStair ℓ hℓ ε hε s₀ hE).F 0 n ≤ relativeInvariants :=
  iSup₂_le fun _ _ => inf_le_left

theorem lowStair_F_mem_of {n : ℤ} {v : Cochain} (hv : v ∈ relativeInvariants)
    (hdeg : ∀ s ∈ v.support, ∃ i : ℕ, monomialDegree s = degOf ℓ ε s₀ i n) :
    v ∈ (lowStair ℓ hℓ ε hε s₀ hE).F 0 n := by
  rw [← sum_cochainProjection v]
  refine Submodule.sum_mem _ fun d hd => ?_
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨i, hi⟩ := hdeg t ht
  apply Staircase.mem_F_of_mem_P _ (Nat.zero_le i)
  refine ⟨cochainProjection_invariant _ hv, ?_⟩
  rw [hi]
  exact cochainProjection_mem _ _

theorem lowStair_F_degrees {n : ℤ} {v : Cochain} (hv : v ∈ (lowStair ℓ hℓ ε hε s₀ hE).F 0 n) :
    v ∈ ⨆ i : ℕ, cochainPiece (degOf ℓ ε s₀ i n) :=
  (iSup₂_le fun j _ => inf_le_right.trans (le_iSup (fun i : ℕ => cochainPiece (degOf ℓ ε s₀ i n)) j))
    hv

end Stair

/-! ## Total exactness on the staircases -/

theorem lowStair_DExact_one {ε : ℕ} (hε : ε ≤ 1) {s₀ : ℤ} (hE : (1 + ((1 : ℕ) : ℤ)) * s₀ - ε ≠ 0)
    (n : ℤ) : (lowStair 1 le_rfl ε hε s₀ hE).DExact n := by
  intro z hz hDz
  set St := lowStair 1 le_rfl ε hε s₀ hE
  have hzinv := lowStair_F_le le_rfl hε hE n hz
  set E : ℤ := 2 * s₀ - ε with hEdef
  have hE' : E ≠ 0 := by rw [hEdef]; simpa using hE
  rcases lt_or_ge (n + ε) 0 with hneg | hnn
  · -- negative cochain degree: nothing there
    have hz0 : z = 0 := by
      have hbot : (⨆ i : ℕ, cochainPiece (degOf 1 ε s₀ i n)) = ⊥ :=
        eq_bot_iff.mpr (iSup_le fun i => by
          rw [cochainPiece_eq_bot_of fun s hs => by
            have := (congrArg Prod.fst hs)
            simp only [degOf, monomialDegree] at this
            omega])
      have := lowStair_F_degrees le_rfl hε hE hz
      rwa [hbot, Submodule.mem_bot] at this
    exact ⟨0, Submodule.zero_mem _, by rw [hz0, map_zero]⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = n + ε := ⟨(n + ε).toNat, Int.toNat_of_nonneg hnn⟩
  have hzE : z ∈ energyOnePiece N E := by
    have hle : (⨆ i : ℕ, cochainPiece (degOf 1 ε s₀ i n)) ≤ energyOnePiece N E :=
      iSup_le fun i => by
        have := cochainPiece_le_energyOnePiece N (2 * (i : ℤ) + ε) (s₀ + (2 - 1) * i)
        convert this using 2
        · simp only [degOf, hN, Nat.cast_one]
        · rw [hEdef]; ring
    exact hle (lowStair_F_degrees le_rfl hε hE hz)
  obtain ⟨w, hw, hwE, hzw⟩ := totalOne_exact hE' hzinv hzE hDz
  refine ⟨w, lowStair_F_mem_of le_rfl hε hE hw fun s hs => ?_, hzw⟩
  have hsE := hwE (Finsupp.mem_support_iff.mpr (Finsupp.mem_support_iff.mp hs))
  simp only [Set.mem_setOf_eq] at hsE
  obtain ⟨hcard, hen⟩ := hsE
  rw [monomialEnergyOne_eq] at hen
  have hb := bCount_nonneg' s
  -- the empty monomial has energy zero
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · exfalso
    rw [hN0, Nat.zero_sub] at hcard
    have := card_le_energy s
    rw [Finset.card_eq_zero.mp hcard] at hen
    simp [monomialDegree] at hen
    exact hE' hen.symm
  set B' := (monomialDegree s).2.1
  set S' := (monomialDegree s).2.2
  refine ⟨((B' - ε) / 2).toNat, ?_⟩
  have hc : (monomialDegree s).1 = (s.card : ℤ) := rfl
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [degOf]
    rw [hc, hcard]
    push_cast [Nat.cast_sub hNpos]
    omega
  · simp only [degOf]
    omega
  · simp only [degOf]
    omega

theorem lowStair_DExact_zero {ε : ℕ} (hε : ε ≤ 1) {s₀ : ℤ}
    (hE : (1 + ((0 : ℕ) : ℤ)) * s₀ - ε ≠ 0) (n : ℤ) :
    (lowStair 0 (Nat.zero_le 1) ε hε s₀ hE).DExact n := by
  intro z hz hDz
  have hzinv := lowStair_F_le (Nat.zero_le 1) hε hE n hz
  set T : ℤ := s₀ - ε with hTdef
  have hT : T ≠ 0 := by rw [hTdef]; simpa using hE
  have hzdeg := lowStair_F_degrees (Nat.zero_le 1) hε hE hz
  have hzc : z ∈ gPiece coarse (n + ε, T) :=
    (iSup_le fun i => (cochainPiece_le_coarse _).trans (by
      simp only [degOf]
      rw [show s₀ + (2 - ((0 : ℕ) : ℤ)) * i - (2 * i + ε) = T by rw [hTdef]; push_cast; ring])) hzdeg
  have hzp : z ∈ gPiece gPar ((ε : ℤ) : ZMod 2) :=
    (iSup_le fun i => (cochainPiece_le_par _).trans (by
      simp only [degOf]
      rw [show ((2 * (i : ℤ) + ε : ℤ) : ZMod 2) = ((ε : ℤ) : ZMod 2) by
        push_cast; rw [show (2 : ZMod 2) = 0 from rfl]; ring])) hzdeg
  have hinv : ∀ e, colorAction e z = 0 := fun e =>
    (Submodule.mem_iInf _).mp hzinv e
  obtain ⟨w, hwc, hwinv, hzw⟩ := totalZero_exact hT hinv hzc hDz
  set w' := gProj gPar ((ε : ℤ) : ZMod 2) w
  have hcomm (E : Cochain →ₗ[ℂ] Cochain) (hE : ∀ e u, u ∈ gPiece gPar e → E u ∈ gPiece gPar e) :
      gProj gPar ((ε : ℤ) : ZMod 2) (E w) = E w' := gProj_comm_zero gPar E hE _ w
  have hzw' : z = q w' + delta 0 w' := by
    rw [← gProj_of_mem gPar hzp, hzw, map_add, hcomm q (fun _ _ h => q_mem_par h),
      hcomm (delta 0) (fun _ _ h => delta_mem_par (Nat.zero_le 1) h)]
  have hw'inv : w' ∈ relativeInvariants := by
    rw [relativeInvariants, Submodule.mem_iInf]
    intro e
    rw [LinearMap.mem_ker, ← hcomm (colorAction e) (fun _ _ h => colorAction_mem_par e h),
      hwinv e, map_zero]
  refine ⟨w', lowStair_F_mem_of (Nat.zero_le 1) hε hE hw'inv fun s hs => ?_, hzw'⟩
  have hsc := (mem_gPiece_iff coarse).mp (gProj_mem_of_mem gPar coarse hwc _) s hs
  have hsp := (mem_gPiece_iff gPar).mp (gProj_mem gPar _ w) s hs
  rw [gdeg_coarse_eq] at hsc
  rw [gdeg_gPar_eq, degToPar_apply] at hsp
  have hb := bCount_nonneg' s
  have hcard : (monomialDegree s).1 = (s.card : ℤ) := rfl
  set B' := (monomialDegree s).2.1
  set S' := (monomialDegree s).2.2
  simp only [degToCoarse, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq] at hsc
  have hp := hsp
  have hpar : B' % 2 = (ε : ℤ) % 2 := by
    have := (ZMod.intCast_eq_intCast_iff' B' (ε : ℤ) 2).mp hp
    exact_mod_cast this
  refine ⟨((B' - ε) / 2).toNat, ?_⟩
  rw [show monomialDegree s = ((monomialDegree s).1, B', S') from rfl]
  simp only [degOf, Prod.mk.injEq]
  push_cast
  omega

/-! ## `𝒩_B^0 = 0` and `𝒩_B^1 = 0` -/

theorem cochainPiece_bot_of_energy {d : Degree} (h : 2 * d.2.2 - d.2.1 < d.1) :
    cochainPiece d = ⊥ :=
  cochainPiece_eq_bot_of fun s hs => by
    have := card_le_energy s
    rw [hs] at this
    exact absurd this (by have : (monomialDegree s).1 = (s.card : ℤ) := rfl; rw [hs] at this; omega)

/-- **`𝒩_B^0 = 0`.** -/
theorem surj_zero {B : ℕ} (hB : 0 < B) (hd : ∀ d : Degree, d.2.1 < B → Surj d) (S : ℤ) :
    Surj ((B : ℤ), (B : ℤ), S) := by
  by_cases hE0 : 2 * S - B < B
  · exact surj_of_bot (cochainPiece_bot_of_energy hE0)
  intro u hu hud
  set ε := B % 2 with hεdef
  set I := B / 2 with hIdef
  have hε : ε ≤ 1 := by omega
  have hBI : (B : ℤ) = 2 * I + ε := by omega
  have hE : (1 + ((1 : ℕ) : ℤ)) * (S - I) - ε ≠ 0 := by push_cast; omega
  set St := lowStair 1 le_rfl ε hε (S - I) hE
  have hdeg : degOf 1 ε (S - I) I (2 * I) = ((B : ℤ), (B : ℤ), S) := by
    simp only [degOf, Prod.mk.injEq]; push_cast; omega
  have hx : u ∈ St.P I (2 * I) := ⟨hu.1, by change u ∈ cochainPiece (degOf _ _ _ _ _); rwa [hdeg]⟩
  have := St.bottom (lowStair_low le_rfl hε hE)
    (lowStair_IH le_rfl hε hE (fun d hd' => hd d (by omega))) (lowStair_DExact_one hε hE _) hx hu.2
  obtain ⟨-, hu', a, ha, hau⟩ := this
  change a ∈ Source.piece (degOf 1 ε (S - I) I (2 * I)) at ha
  rw [hdeg] at ha
  exact ⟨a, ha, hau⟩

theorem cochainPiece_bot_of_weight {d : Degree} (h : d.2.2 < d.1) : cochainPiece d = ⊥ :=
  cochainPiece_eq_bot_of fun s hs => by
    have := card_le_weight s
    have h1 : (monomialDegree s).1 = (s.card : ℤ) := rfl
    rw [hs] at this h1
    omega

theorem cochainPiece_bot_of_T {d : Degree} (h : d.2.2 - d.2.1 + 3 < d.1) : cochainPiece d = ⊥ :=
  cochainPiece_eq_bot_of fun s hs => by
    have := card_le_T_add_three s
    have h1 : (monomialDegree s).1 = (s.card : ℤ) := rfl
    rw [hs] at this h1
    omega

/-- **`𝒩_B^1 = 0`**, by induction on spin. -/
theorem surj_one {B : ℕ} (hB : 1 < B) (hd : ∀ d : Degree, d.2.1 < B → Surj d) :
    ∀ k : ℕ, ∀ S : ℤ, S ≤ k → Surj ((B : ℤ) + 1, (B : ℤ), S) := by
  intro k
  induction k with
  | zero =>
    intro S hS
    exact surj_of_bot (cochainPiece_bot_of_weight (by simp only; omega))
  | succ k ih =>
    intro S hS u hu hud
    by_contra hbad
    have hgood : u ∉ goodCycles ((B : ℤ) + 1, (B : ℤ), S) := fun h => hbad h.2.2
    set ε := B % 2 with hεdef
    set I := B / 2 with hIdef
    have hε : ε ≤ 1 := by omega
    have hBI : (B : ℤ) = 2 * I + ε := by omega
    by_cases hE0 : 2 * S - B < B + 1
    · exact hbad (surj_of_bot (cochainPiece_bot_of_energy (by simp only; omega)) u hu hud)
    -- the `δ₁` staircase
    have hE1 : (1 + ((1 : ℕ) : ℤ)) * (S - I) - ε ≠ 0 := by push_cast; omega
    set St1 := lowStair 1 le_rfl ε hε (S - I) hE1
    have hdeg1 : degOf 1 ε (S - I) I (2 * I + 1) = ((B : ℤ) + 1, (B : ℤ), S) := by
      simp only [degOf, Prod.mk.injEq]; push_cast; omega
    have hdeg2 : degOf 1 ε (S - I) (I + 1) (2 * I + 1 + 1) = ((B : ℤ) + 2, (B : ℤ) + 2, S + 1) := by
      simp only [degOf, Prod.mk.injEq]; push_cast; omega
    have hx1 : u ∈ St1.P I (2 * I + 1) :=
      ⟨hu.1, by change u ∈ cochainPiece (degOf _ _ _ _ _); rwa [hdeg1]⟩
    have hy_bad : delta 1 u ∉ goodCycles ((B : ℤ) + 2, (B : ℤ) + 2, S + 1) := by
      intro hy
      apply hgood
      have := St1.shift_injective (lowStair_low le_rfl hε hE1)
        (lowStair_IH le_rfl hε hE1 (fun d hd' => hd d (by omega)))
        (lowStair_DExact_one hε hE1 _) hx1 hu.2
        (by change delta 1 u ∈ goodCycles (degOf _ _ _ _ _); rwa [hdeg2])
      change u ∈ goodCycles (degOf _ _ _ _ _) at this
      rwa [hdeg1] at this
    have hyc : delta 1 u ∈ relativeCycles := delta_mem_cycles le_rfl hu
    have hyd : delta 1 u ∈ cochainPiece ((B : ℤ) + 2, (B : ℤ) + 2, S + 1) := by
      rw [← hdeg2, ← degOf_delta, hdeg1]
      exact delta_degree le_rfl hud
    -- `T = 0` has no room
    by_cases hT0 : S - B - 1 = 0
    · apply hy_bad
      have hbot := cochainPiece_bot_of_T (d := ((B : ℤ) + 2, (B : ℤ) + 2, S + 1)) (by
        simp only; omega)
      exact good_of_surj (surj_of_bot hbot) hyc hyd
    -- the `δ₀` staircase
    have hE0' : (1 + ((0 : ℕ) : ℤ)) * (S - 2 * I - 1) - ε ≠ 0 := by push_cast; omega
    set St0 := lowStair 0 (Nat.zero_le 1) ε hε (S - 2 * I - 1) hE0'
    have hdeg3 : degOf 0 ε (S - 2 * I - 1) (I + 1) (2 * I + 1 + 1) =
        ((B : ℤ) + 2, (B : ℤ) + 2, S + 1) := by
      simp only [degOf, Prod.mk.injEq]; push_cast; omega
    have hdeg4 : degOf 0 ε (S - 2 * I - 1) I (2 * I + 1) = ((B : ℤ) + 1, (B : ℤ), S - 1) := by
      simp only [degOf, Prod.mk.injEq]; push_cast; omega
    have hy0 : delta 1 u ∈ St0.P (I + 1) (2 * I + 1 + 1) :=
      ⟨hyc.1, by change delta 1 u ∈ cochainPiece (degOf _ _ _ _ _); rwa [hdeg3]⟩
    obtain ⟨x, hx, hqx, hyx⟩ := St0.shift_surjective (lowStair_low (Nat.zero_le 1) hε hE0')
      (lowStair_IH (Nat.zero_le 1) hε hE0' (fun d hd' => hd d (by omega)))
      (lowStair_DExact_zero hε hE0' _) hy0 hyc.2
    have hxd : x ∈ cochainPiece ((B : ℤ) + 1, (B : ℤ), S - 1) := by
      have := hx.2; change x ∈ cochainPiece (degOf _ _ _ _ _) at this; rwa [hdeg4] at this
    have hxgood : x ∈ St0.A I (2 * I + 1) := by
      change x ∈ goodCycles (degOf _ _ _ _ _)
      rw [hdeg4]
      exact good_of_surj (ih (S - 1) (by omega)) ⟨hx.1, hqx⟩ hxd
    have := St0.A_δ hxgood
    change delta 0 x ∈ goodCycles (degOf _ _ _ _ _) at this
    rw [hdeg3] at this
    apply hy_bad
    rw [hyx]
    exact this

/-! ## From cohomology to `ψ` -/

theorem surj_iff_phiPiece (d : Degree) : Surj d ↔ Function.Surjective (phiPiece d) := by
  constructor
  · rintro h ⟨c, hc⟩
    obtain ⟨y, hy, rfl⟩ := hc
    obtain ⟨a, ha, hay⟩ := h y y.property hy
    exact ⟨⟨a, ha⟩, Subtype.ext hay⟩
  · intro h u hu hud
    obtain ⟨⟨a, ha⟩, hay⟩ := h ⟨classOf u hu, ⟨⟨u, hu⟩, hud, rfl⟩⟩
    exact ⟨a, ha, congrArg Subtype.val hay⟩

/-- Dimension count: a surjection `ψ : K → A^∨`, with `K^∨ ≅ C` and an injection `φ : A → C`,
is injective iff `φ` is surjective. -/
theorem injective_iff_surjective_of_dual {K C A : Type*} [AddCommGroup K] [Module ℂ K]
    [FiniteDimensional ℂ K] [AddCommGroup C] [Module ℂ C] [AddCommGroup A] [Module ℂ A]
    (dict : C ≃ₗ[ℂ] Module.Dual ℂ K) (φ : A →ₗ[ℂ] C) (hφ : Function.Injective φ)
    (ψ : K →ₗ[ℂ] Module.Dual ℂ A) (hψ : Function.Surjective ψ) :
    Function.Injective ψ ↔ Function.Surjective φ := by
  have hC : FiniteDimensional ℂ C := LinearEquiv.finiteDimensional dict.symm
  have hA : FiniteDimensional ℂ A := Module.Finite.of_injective φ hφ
  have hrankC : Module.finrank ℂ C = Module.finrank ℂ K := by
    rw [dict.finrank_eq, Subspace.dual_finrank_eq]
  constructor
  · intro hinj
    have hrank : Module.finrank ℂ K = Module.finrank ℂ A := by
      rw [(LinearEquiv.ofBijective ψ ⟨hinj, hψ⟩).finrank_eq, Subspace.dual_finrank_eq]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hrank.symm.trans hrankC.symm)).mp hφ
  · intro hsurj
    have hrank : Module.finrank ℂ A = Module.finrank ℂ C :=
      (LinearEquiv.ofBijective φ ⟨hφ, hsurj⟩).finrank_eq
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq, hrank, hrankC])).mpr hψ

theorem psiK_injective_iff (p B : ℕ) (S : ℤ) :
    Function.Injective (Current.psiK p B S) ↔ Surj (Current.kDegree p B S) :=
  (injective_iff_surjective_of_dual (Current.dictionary p B S) (phiPiece _)
    (phiPiece_injective _) (Current.psiK p B S) (Current.psiK_surjective p B S)).trans
      (surj_iff_phiPiece _).symm

set_option maxHeartbeats 2000000 in
-- unfolding the assembled comparison map is expensive
theorem psi_injective_iff_psiK (B p : ℕ) :
    Function.Injective (Conditional.psi B p) ↔ ∀ S : ℤ, Function.Injective (Current.psiK p B S) := by
  refine (Conditional.psi_injective_iff B p).trans ?_
  rw [Modules.psiB_eq_sourceDualEquiv_comp_psiTotal, LinearMap.coe_comp, LinearEquiv.coe_coe,
    EquivLike.comp_injective]
  exact DirectSum.lmap_injective (fun S : ℤ => Current.psiK p B S)

theorem psi_injective_iff_surj (B p : ℕ) :
    Function.Injective (Conditional.psi B p) ↔ ∀ S : ℤ, Surj (Current.kDegree p B S) :=
  (psi_injective_iff_psiK B p).trans (forall_congr' fun S => psiK_injective_iff p B S)

/-! ## The low-degree step -/

/-- **Paper Prop. 5.3**: the low-degree step of the induction is a theorem. -/
theorem lowDegreeStep : Conditional.LowDegreeStep := by
  intro B hB he p hp hpB
  rw [psi_injective_iff_surj]
  have hd : ∀ d : Degree, d.2.1 < B → Surj d := by
    rintro ⟨N, b, S⟩ hb
    simp only at hb
    by_cases hbad : b < 0 ∨ N < b
    · apply surj_of_bot
      apply cochainPiece_eq_bot_of
      intro s hs
      have h1 := bCount_nonneg' s
      have h2 := bCount_le_card s
      have h3 : (monomialDegree s).1 = (s.card : ℤ) := rfl
      rw [hs] at h1 h2 h3
      simp only at h1 h2 h3
      omega
    push Not at hbad
    have hk : Current.kDegree (N - b).toNat b.toNat S = (N, b, S) := by
      simp only [Current.kDegree]
      refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp only <;> omega
    rw [← hk]
    exact (psi_injective_iff_surj b.toNat (N - b).toNat).mp (he b.toNat (by omega) _) S
  intro S
  interval_cases p
  · have : Current.kDegree 0 B S = ((B : ℤ), (B : ℤ), S) := by simp [Current.kDegree]
    rw [this]
    exact surj_zero hB hd S
  · have : Current.kDegree 1 B S = ((B : ℤ) + 1, (B : ℤ), S) := by simp [Current.kDegree]
    rw [this]
    exact surj_one hpB hd S.toNat S (Int.self_le_toNat S)

end KhanSL2
