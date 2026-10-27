module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The staircase lemma (blueprint `lem:staircase`, replaces the spectral sequences of §5)

A module `V` carries pieces `P i n`: `i` is the filtration index (in §5, the coefficient degree is
`B = 2i + ε`) and `n` is the total degree, shifted so that `P i n = 0` for `n < 2i`. There are two
operators of total degree one, `Q : P i n → P i (n+1)` and `δ : P i n → P (i+1) (n+1)`, with
`Q² = δ² = Qδ + δQ = 0`. A subspace `A i n` of `Q`-cycles contains the `Q`-boundaries, is
`δ`-stable, and is `δ̄`-exact: modulo boundaries, a `δ̄`-closed element of `A` is `δ` of an element
of `A`.

`IH(I)` says that every `Q`-cycle in a level `i < I` lies in `A`. With `D = Q + δ`:

* `push`: a chain whose `D`-image starts at level `k + 1` can be modified by a `D`-boundary so
  that it starts at level `k`, provided `k ≤ I`;
* `bottom` (`cor:bottom`): if `D` is exact in total degree `2I`, every `Q`-cycle in `P I (2I)`
  lies in `A`;
* `shift_injective`, `shift_surjective` (`cor:shift`): if `D` is exact in total degree `2I+1`
  (resp. `2I+2`), then `δ̄ : P I (2I+1) → P (I+1) (2I+2)` is injective modulo `A`
  (resp. every `Q`-cycle in `P (I+1) (2I+2)` is `δ` of a `Q`-cycle in `P I (2I+1)`).

These are the edge arguments of paper Prop. 5.3, with all filtrations finite.
-/

noncomputable section

namespace KhanSL2.Deformation

/-- The data of the staircase lemma (blueprint `def:staircase`). -/
structure Staircase (R V : Type*) [Ring R] [AddCommGroup V] [Module R V] where
  /-- The piece of filtration level `i` and (shifted) total degree `n`. -/
  P : ℕ → ℤ → Submodule R V
  /-- The differential preserving the filtration level. -/
  Q : V →ₗ[R] V
  /-- The deformation, raising the filtration level by one. -/
  δ : V →ₗ[R] V
  /-- The distinguished `Q`-cycles. -/
  A : ℕ → ℤ → Submodule R V
  Q_mem : ∀ {i n x}, x ∈ P i n → Q x ∈ P i (n + 1)
  δ_mem : ∀ {i n x}, x ∈ P i n → δ x ∈ P (i + 1) (n + 1)
  QQ : ∀ {i n x}, x ∈ P i n → Q (Q x) = 0
  δδ : ∀ {i n x}, x ∈ P i n → δ (δ x) = 0
  Qδ : ∀ {i n x}, x ∈ P i n → Q (δ x) + δ (Q x) = 0
  indep : ∀ i n, Disjoint (P i n) (⨆ j, ⨆ (_ : i + 1 ≤ j), P j n)
  A_le : ∀ i n, A i n ≤ P i n
  A_cycle : ∀ {i n x}, x ∈ A i n → Q x = 0
  bdry : ∀ {i n x}, x ∈ P i n → Q x ∈ A i (n + 1)
  A_δ : ∀ {i n x}, x ∈ A i n → δ x ∈ A (i + 1) (n + 1)
  exact : ∀ {i n x}, x ∈ A i n → (∃ y ∈ P (i + 1) n, δ x = Q y) →
    ∃ a ∈ A (i - 1) (n - 1), ∃ c ∈ P i (n - 1), x = δ a + Q c

namespace Staircase

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (S : Staircase R V)

/-- The filtration: everything in levels `≥ k`, in total degree `n`. -/
def F (k : ℕ) (n : ℤ) : Submodule R V := ⨆ j, ⨆ (_ : k ≤ j), S.P j n

/-- The total differential. -/
def D : V →ₗ[R] V := S.Q + S.δ

theorem D_apply (x : V) : S.D x = S.Q x + S.δ x := rfl

/-- The induction hypothesis `IH(I)`: in every level below `I`, all `Q`-cycles lie in `A`. -/
def IH (I : ℕ) : Prop := ∀ i < I, ∀ n x, x ∈ S.P i n → S.Q x = 0 → x ∈ S.A i n

/-- `D` is exact in total degree `n`. -/
def DExact (n : ℤ) : Prop := ∀ z ∈ S.F 0 n, S.D z = 0 → ∃ w ∈ S.F 0 (n - 1), z = S.D w

theorem P_le_F {k j : ℕ} {n : ℤ} (h : k ≤ j) : S.P j n ≤ S.F k n :=
  le_iSup₂_of_le (f := fun j (_ : k ≤ j) => S.P j n) j h le_rfl

theorem mem_F_of_mem_P {k j : ℕ} {n : ℤ} (h : k ≤ j) {x : V} (hx : x ∈ S.P j n) :
    x ∈ S.F k n := S.P_le_F h hx

theorem F_anti {k k' : ℕ} {n : ℤ} (h : k ≤ k') : S.F k' n ≤ S.F k n :=
  iSup₂_le fun _ hj => S.P_le_F (h.trans hj)

theorem F_eq_sup (k : ℕ) (n : ℤ) : S.F k n = S.P k n ⊔ S.F (k + 1) n := by
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    rcases hj.eq_or_lt with rfl | h
    · exact le_sup_left
    · exact le_sup_of_le_right (S.P_le_F h)
  · exact sup_le (S.P_le_F le_rfl) (S.F_anti (Nat.le_succ k))

theorem exists_split {k : ℕ} {n : ℤ} {x : V} (hx : x ∈ S.F k n) :
    ∃ y ∈ S.P k n, ∃ z ∈ S.F (k + 1) n, x = y + z := by
  rw [F_eq_sup] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  exact ⟨y, hy, z, hz, rfl⟩

/-- The pieces vanish below the diagonal `n = 2i`. -/
def Low : Prop := ∀ (i : ℕ) (n : ℤ), n < 2 * (i : ℤ) → S.P i n = ⊥

theorem F_eq_bot (hlow : S.Low) {k : ℕ} {n : ℤ} (h : n < 2 * (k : ℤ)) : S.F k n = ⊥ := by
  refine eq_bot_iff.mpr (iSup₂_le fun j hj => ?_)
  rw [hlow j n (by
    have : (k : ℤ) ≤ j := by exact_mod_cast hj
    linarith)]

theorem eq_zero_of_mem_P_of_mem_F {i : ℕ} {n : ℤ} {x : V} (hP : x ∈ S.P i n)
    (hF : x ∈ S.F (i + 1) n) : x = 0 :=
  (Submodule.disjoint_def.mp (S.indep i n)) x hP hF

theorem Q_mem_F {k : ℕ} {n : ℤ} {x : V} (hx : x ∈ S.F k n) : S.Q x ∈ S.F k (n + 1) := by
  have h : S.F k n ≤ (S.F k (n + 1)).comap S.Q :=
    iSup₂_le fun _ hj _ hy => S.P_le_F hj (S.Q_mem hy)
  exact h hx

theorem δ_mem_F {k : ℕ} {n : ℤ} {x : V} (hx : x ∈ S.F k n) : S.δ x ∈ S.F (k + 1) (n + 1) := by
  have h : S.F k n ≤ (S.F (k + 1) (n + 1)).comap S.δ :=
    iSup₂_le fun _ hj _ hy => S.P_le_F (Nat.succ_le_succ hj) (S.δ_mem hy)
  exact h hx

theorem D_mem_F {k : ℕ} {n : ℤ} {x : V} (hx : x ∈ S.F k n) : S.D x ∈ S.F k (n + 1) :=
  Submodule.add_mem _ (S.Q_mem_F hx) (S.F_anti (Nat.le_succ k) (S.δ_mem_F hx))

theorem D_D {k : ℕ} {n : ℤ} {x : V} (hx : x ∈ S.F k n) : S.D (S.D x) = 0 := by
  have h : S.F k n ≤ LinearMap.ker (S.D ∘ₗ S.D) := by
    refine iSup₂_le fun j _ y hy => ?_
    change S.D (S.D y) = 0
    calc S.D (S.D y) = S.Q (S.Q y) + S.δ (S.δ y) + (S.Q (S.δ y) + S.δ (S.Q y)) := by
          simp only [D_apply, map_add]; abel
      _ = 0 := by rw [S.QQ hy, S.δδ hy, S.Qδ hy, add_zero, add_zero]
  exact h hx

theorem mem_F_zero {i : ℕ} {n : ℤ} {x : V} (hx : x ∈ S.P i n) : x ∈ S.F 0 n :=
  S.P_le_F (Nat.zero_le i) hx

/-- One step of the push: a chain starting at level `j < k` can be moved to start at `j + 1`. -/
theorem push_step {I : ℕ} (hIH : S.IH I) {n : ℤ} {k j : ℕ} (hk : k ≤ I) (hj : j < k)
    {z : V} (hz : z ∈ S.F j n) (hDz : S.D z ∈ S.F (k + 1) (n + 1)) :
    ∃ u ∈ S.F 0 (n - 1), z - S.D u ∈ S.F (j + 1) n := by
  obtain ⟨x, hx, z'', hz'', rfl⟩ := S.exists_split hz
  obtain ⟨y, hy, w, hw, rfl⟩ := S.exists_split hz''
  have hD : S.D (x + (y + w)) = S.Q x + (S.δ x + S.Q y + S.δ y + S.D w) := by
    simp only [D_apply, map_add]
    abel
  have hDj1 : S.D (x + (y + w)) ∈ S.F (j + 1) (n + 1) := S.F_anti (by omega) hDz
  have hDj2 : S.D (x + (y + w)) ∈ S.F (j + 2) (n + 1) := S.F_anti (by omega) hDz
  -- the rest after `Q x` lies in level `j + 1`
  have hδx : S.δ x ∈ S.F (j + 1) (n + 1) := S.mem_F_of_mem_P le_rfl (S.δ_mem hx)
  have hQy : S.Q y ∈ S.F (j + 1) (n + 1) := S.mem_F_of_mem_P le_rfl (S.Q_mem hy)
  have hδy : S.δ y ∈ S.F (j + 2) (n + 1) := S.mem_F_of_mem_P le_rfl (S.δ_mem hy)
  have hDw : S.D w ∈ S.F (j + 2) (n + 1) := S.D_mem_F hw
  have hQx0 : S.Q x = 0 := by
    apply S.eq_zero_of_mem_P_of_mem_F (S.Q_mem hx)
    have hrest : S.δ x + S.Q y + S.δ y + S.D w ∈ S.F (j + 1) (n + 1) :=
      Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ hδx hQy)
        (S.F_anti (Nat.le_succ _) hδy)) (S.F_anti (Nat.le_succ _) hDw)
    have := Submodule.sub_mem _ hDj1 hrest
    rwa [hD, add_sub_cancel_right] at this
  have hδxQy : S.δ x + S.Q y = 0 := by
    apply S.eq_zero_of_mem_P_of_mem_F (Submodule.add_mem _ (S.δ_mem hx) (S.Q_mem hy))
    have := Submodule.sub_mem _ hDj2 (Submodule.add_mem _ hδy hDw)
    rw [hD, hQx0, zero_add] at this
    convert this using 1
    abel
  have hxA : x ∈ S.A j n := hIH j (by omega) n x hx hQx0
  obtain ⟨a, ha, c, hc, hxac⟩ := S.exact hxA ⟨-y, Submodule.neg_mem _ hy, by
    rw [map_neg, ← add_eq_zero_iff_eq_neg.mp hδxQy]⟩
  refine ⟨a + c, Submodule.add_mem _ (S.mem_F_zero (S.A_le _ _ ha)) (S.mem_F_zero hc), ?_⟩
  have hQa : S.Q a = 0 := S.A_cycle ha
  have heq : x + (y + w) - S.D (a + c) = (y + w) - S.δ c := by
    rw [hxac]
    simp only [D_apply, map_add, hQa]
    abel
  rw [heq]
  have hδc := S.δ_mem hc
  rw [sub_add_cancel] at hδc
  exact Submodule.sub_mem _ hz'' (S.mem_F_of_mem_P le_rfl hδc)

/-- **The staircase push** (blueprint `lem:staircase`). -/
theorem push {I : ℕ} (hIH : S.IH I) {n : ℤ} {k : ℕ} (hk : k ≤ I) {z : V}
    (hz : z ∈ S.F 0 n) (hDz : S.D z ∈ S.F (k + 1) (n + 1)) :
    ∃ u ∈ S.F 0 (n - 1), z - S.D u ∈ S.F k n := by
  have key : ∀ j ≤ k, ∃ u ∈ S.F 0 (n - 1), z - S.D u ∈ S.F j n := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨0, Submodule.zero_mem _, by simpa using hz⟩
    | succ j ih =>
      intro hj
      obtain ⟨u, hu, hzu⟩ := ih (by omega)
      have hD' : S.D (z - S.D u) = S.D z := by
        rw [map_sub, S.D_D hu, sub_zero]
      obtain ⟨u', hu', hzu'⟩ := S.push_step hIH hk (by omega) hzu (hD' ▸ hDz)
      refine ⟨u + u', Submodule.add_mem _ hu hu', ?_⟩
      rw [map_add, ← sub_sub]
      exact hzu'
  exact key k le_rfl

/-- **Bottom edge** (blueprint `cor:bottom`). -/
theorem bottom (hlow : S.Low) {I : ℕ} (hIH : S.IH I) (hD : S.DExact (2 * I)) {x : V}
    (hx : x ∈ S.P I (2 * I)) (hQx : S.Q x = 0) : x ∈ S.A I (2 * I) := by
  have hδx : S.δ x = 0 := by
    have h := S.δ_mem hx
    rwa [hlow (I + 1) _ (by push_cast; linarith), Submodule.mem_bot] at h
  obtain ⟨w, hw, rfl⟩ := hD x (S.mem_F_zero hx) (by rw [D_apply, hQx, hδx, add_zero])
  rcases Nat.eq_zero_or_pos I with rfl | hI
  · have hw0 : w = 0 := by
      rw [S.F_eq_bot hlow (by norm_num)] at hw
      exact (Submodule.mem_bot R).mp hw
    rw [hw0, map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨u, hu, hwu⟩ := S.push hIH (k := I - 1) (by omega) hw (by
      rw [show I - 1 + 1 = I by omega, show (2 * (I : ℤ) - 1 + 1) = 2 * I by ring]
      exact S.mem_F_of_mem_P le_rfl hx)
    -- `w - D u` lies in the single level `I - 1`
    have hlev : w - S.D u ∈ S.P (I - 1) (2 * I - 1) := by
      obtain ⟨y, hy, z, hz, hyz⟩ := S.exists_split hwu
      rw [S.F_eq_bot hlow (by push_cast [show I - 1 + 1 = I by omega]; linarith)] at hz
      rw [hyz, (Submodule.mem_bot R).mp hz, add_zero]
      exact hy
    have hDw : S.D (w - S.D u) = S.D w := by rw [map_sub, S.D_D hu, sub_zero]
    set w' := w - S.D u
    have hQw' : S.Q w' = 0 := by
      apply S.eq_zero_of_mem_P_of_mem_F (by
        have := S.Q_mem hlev
        rwa [show (2 * (I : ℤ) - 1 + 1) = 2 * I by ring] at this)
      rw [show I - 1 + 1 = I by omega]
      have h1 : S.Q w' = S.D w - S.δ w' := by rw [← hDw, D_apply, add_sub_cancel_right]
      rw [h1]
      refine Submodule.sub_mem _ (S.mem_F_of_mem_P le_rfl hx) (S.mem_F_of_mem_P le_rfl ?_)
      have := S.δ_mem hlev
      rwa [show I - 1 + 1 = I by omega, show (2 * (I : ℤ) - 1 + 1) = 2 * I by ring] at this
    have hw'A : w' ∈ S.A (I - 1) (2 * I - 1) := hIH (I - 1) (by omega) _ w' hlev hQw'
    have hx' : S.D w = S.δ w' := by rw [← hDw, D_apply, hQw', zero_add]
    rw [hx']
    have := S.A_δ hw'A
    rwa [show I - 1 + 1 = I by omega, show (2 * (I : ℤ) - 1 + 1) = 2 * I by ring] at this

/-- **Shift isomorphism, injectivity** (blueprint `cor:shift`): a `Q`-cycle in `P I (2I+1)` whose
`δ`-image lies in `A` lies in `A`. -/
theorem shift_injective (hlow : S.Low) {I : ℕ} (hIH : S.IH I) (hD : S.DExact (2 * I + 1)) {x : V}
    (hx : x ∈ S.P I (2 * I + 1)) (hQx : S.Q x = 0) (hδx : S.δ x ∈ S.A (I + 1) (2 * I + 1 + 1)) :
    x ∈ S.A I (2 * I + 1) := by
  -- `δ x` is `δ̄`-closed in `A`, hence `δ x = δ β` with `β ∈ A`
  have hlow' : S.P (I + 1) (2 * I + 1) = ⊥ := hlow _ _ (by push_cast; linarith)
  obtain ⟨β, hβ, c, hc, hδβ⟩ := S.exact hδx ⟨0, Submodule.zero_mem _, by
    rw [S.δδ hx, map_zero]⟩
  rw [show (2 * (I : ℤ) + 1 + 1 - 1) = 2 * I + 1 by ring] at hβ hc
  rw [show I + 1 - 1 = I by omega] at hβ
  rw [hlow', Submodule.mem_bot] at hc
  rw [hc, map_zero, add_zero] at hδβ
  set x' := x - β
  have hx' : x' ∈ S.P I (2 * I + 1) := Submodule.sub_mem _ hx (S.A_le _ _ hβ)
  have hDx' : S.D x' = 0 := by
    simp only [x', D_apply, map_sub, hQx, S.A_cycle hβ, hδβ, sub_self, add_zero]
  obtain ⟨w, hw, hxw⟩ := hD x' (S.mem_F_zero hx') hDx'
  rw [show (2 * (I : ℤ) + 1 - 1) = 2 * I by ring] at hw
  suffices hx'A : x' ∈ S.A I (2 * I + 1) by
    have := Submodule.add_mem _ hx'A hβ
    rwa [sub_add_cancel] at this
  rcases Nat.eq_zero_or_pos I with rfl | hI
  · -- level zero: `w` lies in `P 0 0`, so `x' = Q w`
    have hw0 : w ∈ S.P 0 0 := by
      obtain ⟨y, hy, z, hz, hyz⟩ := S.exists_split hw
      rw [S.F_eq_bot hlow (by norm_num)] at hz
      rw [hyz, (Submodule.mem_bot R).mp hz, add_zero]
      simpa using hy
    have hδw : S.δ w = 0 := by
      have h := S.δ_mem hw0
      rwa [hlow _ _ (by norm_num), Submodule.mem_bot] at h
    rw [hxw, D_apply, hδw, add_zero]
    simpa using S.bdry hw0
  · obtain ⟨u, hu, hwu⟩ := S.push hIH (k := I - 1) (by omega) hw (by
      rw [show I - 1 + 1 = I by omega, ← hxw]
      exact S.mem_F_of_mem_P le_rfl hx')
    have hDw : S.D (w - S.D u) = x' := by rw [map_sub, S.D_D hu, sub_zero, hxw]
    obtain ⟨w1, hw1, r, hr, hw1r⟩ := S.exists_split hwu
    rw [show I - 1 + 1 = I by omega] at hr
    obtain ⟨w2, hw2, r', hr', hw2r'⟩ := S.exists_split hr
    rw [S.F_eq_bot hlow (by push_cast; linarith), Submodule.mem_bot] at hr'
    rw [hr', add_zero] at hw2r'
    rw [hw1r, hw2r'] at hDw
    have hδw2 : S.δ w2 = 0 := by
      have h := S.δ_mem hw2
      rwa [hlow _ _ (by push_cast; linarith), Submodule.mem_bot] at h
    have hsplit : x' = S.Q w1 + (S.δ w1 + S.Q w2) := by
      rw [← hDw]
      simp only [D_apply, map_add, hδw2]
      abel
    have hQw1m : S.Q w1 ∈ S.P (I - 1) (2 * I + 1) := S.Q_mem hw1
    have hδw1m : S.δ w1 ∈ S.P I (2 * I + 1) := by
      have h := S.δ_mem hw1
      rwa [show I - 1 + 1 = I by omega] at h
    have hQw2m : S.Q w2 ∈ S.P I (2 * I + 1) := S.Q_mem hw2
    have hQw1 : S.Q w1 = 0 := by
      apply S.eq_zero_of_mem_P_of_mem_F hQw1m
      rw [show I - 1 + 1 = I by omega]
      have : S.Q w1 = x' - (S.δ w1 + S.Q w2) := by rw [hsplit, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (S.mem_F_of_mem_P le_rfl hx')
        (Submodule.add_mem _ (S.mem_F_of_mem_P le_rfl hδw1m) (S.mem_F_of_mem_P le_rfl hQw2m))
    have hw1A : w1 ∈ S.A (I - 1) (2 * I) := hIH (I - 1) (by omega) _ w1 hw1 hQw1
    rw [hsplit, hQw1, zero_add]
    refine Submodule.add_mem _ ?_ (S.bdry hw2)
    have := S.A_δ hw1A
    rwa [show I - 1 + 1 = I by omega] at this

/-- **Shift isomorphism, surjectivity** (blueprint `cor:shift`): every `Q`-cycle in
`P (I+1) (2I+2)` is `δ` of a `Q`-cycle in `P I (2I+1)`. -/
theorem shift_surjective (hlow : S.Low) {I : ℕ} (hIH : S.IH I) (hD : S.DExact (2 * I + 1 + 1)) {y : V}
    (hy : y ∈ S.P (I + 1) (2 * I + 1 + 1)) (hQy : S.Q y = 0) :
    ∃ x ∈ S.P I (2 * I + 1), S.Q x = 0 ∧ y = S.δ x := by
  have hδy : S.δ y = 0 := by
    have h := S.δ_mem hy
    rwa [hlow _ _ (by push_cast; linarith), Submodule.mem_bot] at h
  obtain ⟨w, hw, hyw⟩ := hD y (S.mem_F_zero hy) (by rw [D_apply, hQy, hδy, add_zero])
  rw [show (2 * (I : ℤ) + 1 + 1 - 1) = 2 * I + 1 by ring] at hw
  obtain ⟨u, hu, hwu⟩ := S.push hIH (k := I) le_rfl hw (by
    rw [← hyw, show (2 * (I : ℤ) + 1 + 1) = 2 * I + 1 + 1 by ring]
    exact S.mem_F_of_mem_P le_rfl hy)
  have hlev : w - S.D u ∈ S.P I (2 * I + 1) := by
    obtain ⟨y', hy', z, hz, hyz⟩ := S.exists_split hwu
    rw [S.F_eq_bot hlow (by push_cast; linarith), Submodule.mem_bot] at hz
    rw [hyz, hz, add_zero]
    exact hy'
  have hDw : S.D (w - S.D u) = y := by rw [map_sub, S.D_D hu, sub_zero, hyw]
  set x := w - S.D u
  have hQx : S.Q x = 0 := by
    apply S.eq_zero_of_mem_P_of_mem_F (S.Q_mem hlev)
    have : S.Q x = y - S.δ x := by rw [← hDw, D_apply, add_sub_cancel_right]
    rw [this]
    exact Submodule.sub_mem _ (S.mem_F_of_mem_P le_rfl hy) (S.mem_F_of_mem_P le_rfl (S.δ_mem hlev))
  exact ⟨x, hlev, hQx, by rw [← hDw, D_apply, hQx, zero_add]⟩

/-- **Acyclic assembly.** If `Q` is exact in every level below `K`, and nothing lives at levels
`≥ K` in total degree `n`, then `D` is exact in total degree `n`. Here `A` should be the
`Q`-boundaries. -/
theorem assembly {K : ℕ} (hIH : S.IH K) {n : ℤ} (hF : S.F K n = ⊥) {z : V} (hz : z ∈ S.F 0 n)
    (hDz : S.D z = 0) : ∃ w ∈ S.F 0 (n - 1), z = S.D w := by
  obtain ⟨u, hu, hzu⟩ := S.push hIH le_rfl hz (by rw [hDz]; exact Submodule.zero_mem _)
  rw [hF, Submodule.mem_bot, sub_eq_zero] at hzu
  exact ⟨u, hu, hzu⟩

end Staircase

end KhanSL2.Deformation
