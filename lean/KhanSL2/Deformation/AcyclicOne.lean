module

public import KhanSL2.Deformation.RelabelOne
public import KhanSL2.BGGBridge.TrivialCoefficients

@[expose] public section

/-!
# Acyclicity of `D₁` at positive energy (blueprint `cor:D1acyclic`, paper Lemma 5.1(ii))

The energy of a generator is `E = 2S - B` (`Mode.energyOne`): `E(b_j) = 2j + 1`,
`E(c_n) = 2n`. The relabelling `ρ` turns energy into spin and lands in the pure-`c` cochains,
whose invariant `Q`-cohomology is the `B = 0` cohomology, zero in positive spin
(`BGGBridge.cohomology_B_zero`). Hence:

* `q_exact_pureC`: an invariant `Q`-cocycle of degree `(N, 0, S)` with `S ≠ 0` is `Q` of an
  invariant cochain of degree `(N - 1, 0, S)`;
* `totalOne_exact`: an invariant `D₁`-cocycle of total degree `N` and energy `e ≠ 0` is `D₁` of
  an invariant cochain of total degree `N - 1` and energy `e`.
-/

noncomputable section

namespace KhanSL2

/-! ## Exactness of the `B = 0` complex -/

theorem classOf_eq_zero_of_piece_eq_bot {d : Degree} (hd : cohomologyPiece d = ⊥) {u : Cochain}
    (hu : u ∈ relativeCycles) (hud : u ∈ cochainPiece d) : classOf u hu = 0 := by
  have h : classOf u hu ∈ cohomologyPiece d := ⟨⟨u, hu⟩, hud, rfl⟩
  rwa [hd, Submodule.mem_bot] at h

/-- A homogeneous invariant cocycle whose class vanishes is the boundary of a homogeneous
invariant cochain. -/
theorem exists_homogeneous_primitive {d : Degree} {u : Cochain} (hu : u ∈ relativeCycles)
    (hud : u ∈ cochainPiece d) (h0 : classOf u hu = 0) :
    ∃ w ∈ relativeInvariants, w ∈ cochainPiece (d - (1, 0, 0)) ∧ u = q w := by
  obtain ⟨v, hv, hqv⟩ := (classOf_eq_zero_iff u hu).mp h0
  refine ⟨cochainProjection (d - (1, 0, 0)) v, cochainProjection_invariant _ hv,
    cochainProjection_mem _ _, ?_⟩
  rw [← cochainProjection_q, sub_add_cancel, hqv, cochainProjection_of_mem hud]

/-- **`B = 0` exactness.** In positive spin, invariant pure-`c` cocycles are boundaries of
invariant pure-`c` cochains of the same spin. -/
theorem q_exact_pureC {N : ℕ} {S : ℤ} (hS : S ≠ 0) {u : Cochain} (hu : u ∈ relativeCycles)
    (hud : u ∈ cochainPiece ((N : ℤ), 0, S)) :
    ∃ w ∈ relativeInvariants, w ∈ cochainPiece ((N : ℤ) - 1, 0, S) ∧ u = q w := by
  have hd : cohomologyPiece (Current.kDegree N 0 S) = ⊥ :=
    BGGBridge.cohomology_B_zero.1 N S (fun h => hS h.2)
  have hk : Current.kDegree N 0 S = ((N : ℤ), 0, S) := by
    simp [Current.kDegree]
  rw [hk] at hd
  obtain ⟨w, hw, hwd, rfl⟩ := exists_homogeneous_primitive hu hud
    (classOf_eq_zero_of_piece_eq_bot hd hu hud)
  refine ⟨w, hw, ?_, rfl⟩
  convert hwd using 2
  simp

/-! ## Energy -/

/-- The energy `E = 2S - B` of a generator. -/
def Mode.energyOne (m : Mode) : ℤ := 2 * (m.weight : ℤ) - m.bCount

def monomialEnergyOne (s : ExteriorMonomial) : ℤ := ∑ m ∈ s, m.energyOne

/-- Cochains of total degree `N` and energy `e`. -/
def energyOnePiece (N : ℕ) (e : ℤ) : Submodule ℂ Cochain :=
  Finsupp.supported ℂ ℂ {s | s.card = N ∧ monomialEnergyOne s = e}

theorem monomialEnergyOne_eq (s : ExteriorMonomial) :
    monomialEnergyOne s = 2 * (monomialDegree s).2.2 - (monomialDegree s).2.1 := by
  simp only [monomialEnergyOne, Mode.energyOne, monomialDegree, Finset.sum_sub_distrib,
    Finset.mul_sum, Nat.cast_sum]

theorem cochainPiece_le_energyOnePiece (N : ℕ) (B S : ℤ) :
    cochainPiece ((N : ℤ), B, S) ≤ energyOnePiece N (2 * S - B) := by
  intro u hu s hs
  have h := hu hs
  simp only [monomialDegree, Prod.mk.injEq] at h
  refine ⟨by exact_mod_cast h.1, ?_⟩
  rw [monomialEnergyOne_eq]
  simp only [monomialDegree, h.2.1, h.2.2]

/-! ## The relabelling on energy pieces -/

theorem relabelOneMode_weight (m : Mode) : ((relabelOneMode m).weight : ℤ) = m.energyOne := by
  cases m <;> simp [relabelOneMode, Mode.weight, Mode.energyOne, Mode.bCount] <;> ring

theorem relabelOneMode_bCount (m : Mode) : (relabelOneMode m).bCount = 0 := by
  cases m <;> rfl

theorem relabelOne_apply (u : Cochain) :
    relabelOne u = Finsupp.mapDomain (Finset.map relabelOneEmb) u := rfl

theorem monomialDegree_map_relabelOne (s : ExteriorMonomial) :
    monomialDegree (s.map relabelOneEmb) = ((s.card : ℤ), 0, monomialEnergyOne s) := by
  simp only [monomialDegree, Finset.card_map, Finset.sum_map, relabelOneEmb,
    Function.Embedding.coeFn_mk, relabelOneMode_bCount, Finset.sum_const_zero, Nat.cast_zero,
    Nat.cast_sum, relabelOneMode_weight, monomialEnergyOne]

theorem relabelOne_mem_piece {N : ℕ} {e : ℤ} {u : Cochain} (hu : u ∈ energyOnePiece N e) :
    relabelOne u ∈ cochainPiece ((N : ℤ), 0, e) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
  have h := hu hs
  rw [Set.mem_setOf_eq] at h ⊢
  rw [monomialDegree_map_relabelOne, h.1, h.2]

/-- A left inverse of `relabelOneMode` on `c`-modes. -/
def relabelOneInv : Mode → Mode
  | .b j a => .b j a
  | .c k a => if k % 2 = 0 then .b (k / 2) a else .c (k / 2) a

theorem relabelOneMode_inv {m : Mode} (hm : m.bCount = 0) :
    relabelOneMode (relabelOneInv m) = m := by
  cases m with
  | b j a => simp [Mode.bCount] at hm
  | c k a =>
    simp only [relabelOneInv]
    split_ifs with h
    · simp only [relabelOneMode, Mode.c.injEq, and_true]; omega
    · simp only [relabelOneMode, Mode.c.injEq, and_true]; omega

theorem map_image_relabelOneInv {t : ExteriorMonomial} (ht : ∀ m ∈ t, m.bCount = 0) :
    (t.image relabelOneInv).map relabelOneEmb = t := by
  ext x
  simp only [Finset.mem_map, Finset.mem_image, relabelOneEmb, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rwa [relabelOneMode_inv (ht z hz)]
  · intro hx
    exact ⟨relabelOneInv x, ⟨x, hx, rfl⟩, relabelOneMode_inv (ht x hx)⟩

theorem bCount_eq_zero_of_mem {s : ExteriorMonomial} (hs : (monomialDegree s).2.1 = 0)
    {m : Mode} (hm : m ∈ s) : m.bCount = 0 := by
  simp only [monomialDegree, Nat.cast_eq_zero, Finset.sum_eq_zero_iff] at hs
  exact hs m hm

/-- Every pure-`c` cochain is `ρ` of a cochain of the corresponding energy. -/
theorem exists_relabelOne_eq {N : ℕ} {S : ℤ} {u : Cochain}
    (hu : u ∈ cochainPiece ((N : ℤ), 0, S)) :
    ∃ w ∈ energyOnePiece N S, relabelOne w = u := by
  have hinj : Function.Injective (Finset.map relabelOneEmb) := Finset.map_injective _
  have hrange : (u.support : Set ExteriorMonomial) ⊆ Set.range (Finset.map relabelOneEmb) := by
    intro t ht
    have hd := hu ht
    refine ⟨t.image relabelOneInv, map_image_relabelOneInv fun m hm => ?_⟩
    exact bCount_eq_zero_of_mem (by rw [hd]) hm
  refine ⟨Finsupp.comapDomain (Finset.map relabelOneEmb) u hinj.injOn, ?_, ?_⟩
  · intro s hs
    have hs' : s.map relabelOneEmb ∈ u.support := by
      simpa [Finsupp.comapDomain_apply, Finsupp.mem_support_iff] using hs
    have hd := hu hs'
    rw [Set.mem_setOf_eq, monomialDegree_map_relabelOne] at hd
    simp only [Prod.mk.injEq] at hd
    exact ⟨by exact_mod_cast hd.1, hd.2.2⟩
  · rw [relabelOne_apply]
    exact Finsupp.mapDomain_comapDomain _ hinj u hrange

/-! ## `ρ` and the colour action -/

theorem relabelOne_colorGenerator (a : Fin 3) (m : Mode) :
    relabelOne (colorGenerator a m) = colorGenerator a (relabelOneMode m) := by
  cases m <;>
    simp [colorGenerator, map_sum, map_smul, relabelOne_generator, relabelOneMode,
      Mode.color, Mode.recolor]

theorem relabelOne_colorAction (a : Fin 3) (u : Cochain) :
    relabelOne (colorAction a u) = colorAction a (relabelOne u) :=
  FiniteExterior.reindex_extendDerivation Mode.code Mode.code relabelOneEmb
    (fun a b => relabelOneMode_code_lt a b) _ _ (fun m => relabelOne_colorGenerator a m) u

theorem relabelOne_mem_invariants_iff (u : Cochain) :
    relabelOne u ∈ relativeInvariants ↔ u ∈ relativeInvariants := by
  simp only [mem_relativeInvariants_iff, ← relabelOne_colorAction]
  constructor
  · intro h a
    exact relabelOne_injective (by rw [h a, map_zero])
  · intro h a
    rw [h a, map_zero]

/-! ## Acyclicity -/

/-- **`D₁` is exact at nonzero energy** on invariant cochains (blueprint `cor:D1acyclic`). -/
theorem totalOne_exact {N : ℕ} {e : ℤ} (he : e ≠ 0) {z : Cochain}
    (hz : z ∈ relativeInvariants) (hzd : z ∈ energyOnePiece N e) (hD : totalOne z = 0) :
    ∃ w ∈ relativeInvariants, w ∈ energyOnePiece (N - 1) e ∧ z = totalOne w := by
  have hcyc : relabelOne z ∈ relativeCycles :=
    ⟨(relabelOne_mem_invariants_iff z).mpr hz,
      show q (relabelOne z) = 0 by rw [← relabelOne_totalOne, hD, map_zero]⟩
  obtain ⟨w', hw', hw'd, hzw'⟩ := q_exact_pureC he hcyc (relabelOne_mem_piece hzd)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- in total degree zero only the empty monomial occurs, of energy zero
    have hz0 : z = 0 := by
      ext s
      by_contra hs
      have h := hzd (Finsupp.mem_support_iff.mpr hs)
      rw [Set.mem_setOf_eq, Finset.card_eq_zero] at h
      obtain ⟨rfl, he'⟩ := h
      exact he (by rw [← he']; rfl)
    exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, by rw [hz0, map_zero]⟩
  · have hw'd' : w' ∈ cochainPiece (((N - 1 : ℕ) : ℤ), 0, e) := by
      rwa [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    obtain ⟨w, hw, hρw⟩ := exists_relabelOne_eq hw'd'
    refine ⟨w, (relabelOne_mem_invariants_iff w).mp (hρw ▸ hw'), hw, ?_⟩
    apply relabelOne_injective
    rw [relabelOne_totalOne, hρw, ← hzw']

end KhanSL2
