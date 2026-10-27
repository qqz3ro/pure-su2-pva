module

public import KhanSL2.StrongMacdonald.HermLap
public import Mathlib.Data.Finset.Finsupp

@[expose] public section

/-!
# The loop-weight and σ-degree gradings

The diagonal derivations `diagDer wσ wψ` scale every monomial by the total weight of its
generators. Two of them grade `W` compatibly with the Laplacian:

* `Wt`, the loop weight, `σ^a(-k) ↦ k`, `ψ^a(-(i+1)) ↦ i + 1`;
* `Sd`, the σ-degree.

Both commute with `∂̄`, `∂̄†` and the constant action `Y_c`, and their joint eigenspaces
`piece w s` are finite-dimensional.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace KhanSL2.StrongMacdonald

open AddMonoidAlgebra (single)

/-! ## Diagonal derivations -/

/-- The even derivation scaling `σ_g` by `wσ g` and `ψ_n` by `wψ n`. -/
def diagDer (wσ : SMode → ℕ) (wψ : PMode → ℕ) : Module.End ℂ W :=
  mkDer (fun g => (wσ g : ℂ) • sig g) (fun n => (wψ n : ℂ) • psi n)

/-- The weight of the monomial `σ^e ψ_t`. -/
def diagVal (wσ : SMode → ℕ) (wψ : PMode → ℕ) (e : Exp) (t : Finset PMode) : ℕ :=
  (e.sum fun g k => k * wσ g) + ∑ n ∈ t, wψ n

section Diag

variable (wσ : SMode → ℕ) (wψ : PMode → ℕ)

theorem homDer_diagDer : HomDer 0 (diagDer wσ wψ) :=
  mkDer_homDer _ _ (fun g => (isPar_sig g).smul _) (fun n => (isPar_psi n).smul _)

theorem diagDer_sig (g : SMode) : diagDer wσ wψ (sig g) = (wσ g : ℂ) • sig g := mkDer_sig _ _ _

theorem diagDer_psi (n : PMode) : diagDer wσ wψ (psi n) = (wψ n : ℂ) • psi n := mkDer_psi _ _ _

theorem sig_mul_dS_mono (g : SMode) (e : Exp) (t : Finset PMode) :
    sig g * dS g (mono e t) = (e g : ℂ) • mono e t := by
  rw [dS_mono, mul_smul_comm, sig_mul_mono]
  by_cases he : e g = 0
  · rw [he]; simp
  · have hle : Finsupp.single g 1 ≤ e := by
      rw [Finsupp.single_le_iff]; omega
    rw [add_tsub_cancel_of_le hle]

theorem psi_mul_iP_mono (n : PMode) (e : Exp) (t : Finset PMode) :
    psi n * iP n (mono e t) = if n ∈ t then mono e t else 0 := by
  rw [iP_mono]
  split
  · rename_i hn
    rw [mul_smul_comm, psi_mul_mono, if_neg (Finset.notMem_erase n t),
      FiniteExterior.position_erase_self, Finset.insert_erase hn, smul_smul, ← pow_add,
      ← two_mul, pow_mul]
    simp
  · rw [mul_zero]

theorem diagDer_mono (e : Exp) (t : Finset PMode) :
    diagDer wσ wψ (mono e t) = (diagVal wσ wψ e t : ℂ) • mono e t := by
  rw [diagDer, mkDer_mono_eq _ _ e t e.support subset_rfl t subset_rfl]
  have h1 : ∀ g ∈ e.support, (wσ g : ℂ) • sig g * dS g (mono e t) =
      ((e g * wσ g : ℕ) : ℂ) • mono e t := fun g _ => by
    rw [smul_mul_assoc, sig_mul_dS_mono, smul_smul, Nat.cast_mul, mul_comm]
  have h2 : ∀ n ∈ t, (wψ n : ℂ) • psi n * iP n (mono e t) = (wψ n : ℂ) • mono e t :=
    fun n hn => by rw [smul_mul_assoc, psi_mul_iP_mono, if_pos hn]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.sum_smul, ← Finset.sum_smul,
    ← add_smul, diagVal, Finsupp.sum]
  push_cast
  rfl

theorem coefW_diagDer (x : W) (e : Exp) (t : Finset PMode) :
    coefW (diagDer wσ wψ x) e t = (diagVal wσ wψ e t : ℂ) * coefW x e t := by
  refine mono_induction
    (P := fun x => coefW (diagDer wσ wψ x) e t = (diagVal wσ wψ e t : ℂ) * coefW x e t)
    ?_ ?_ ?_ ?_ x
  · simp
  · intro x y hx hy
    rw [map_add, coefW_add, coefW_add, hx, hy, mul_add]
  · intro c x hx
    rw [map_smul, coefW_smul, coefW_smul, hx, mul_left_comm]
  · intro e' t'
    rw [diagDer_mono, coefW_smul, coefW_mono]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · simp

theorem isAdj_diagDer : IsAdj (diagDer wσ wψ) (diagDer wσ wψ) := by
  apply isAdj_of_mono
  intro e s e' s'
  rw [diagDer_mono, diagDer_mono, herm_smul_left, herm_smul_right, herm_mono_left,
    Complex.conj_natCast, coefW_mono]
  split
  · rename_i h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp

end Diag

/-! ## Eigenvectors -/

/-- `x` is an eigenvector of `D` with eigenvalue `v` (possibly `x = 0`). -/
def IsEig (D : Module.End ℂ W) (v : ℂ) (x : W) : Prop := D x = v • x

theorem IsEig.zero (D : Module.End ℂ W) (v : ℂ) : IsEig D v 0 := by
  simp [IsEig]

theorem IsEig.add {D : Module.End ℂ W} {v : ℂ} {x y : W} (hx : IsEig D v x) (hy : IsEig D v y) :
    IsEig D v (x + y) := by
  unfold IsEig at *
  rw [map_add, hx, hy, smul_add]

theorem IsEig.smul {D : Module.End ℂ W} {v : ℂ} {x : W} (r : ℂ) (hx : IsEig D v x) :
    IsEig D v (r • x) := by
  unfold IsEig at *
  rw [map_smul, hx, smul_comm]

theorem IsEig.sum {D : Module.End ℂ W} {v : ℂ} {ι : Type*} (s : Finset ι) (x : ι → W)
    (hx : ∀ i ∈ s, IsEig D v (x i)) : IsEig D v (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsEig.zero D v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hx a (Finset.mem_insert_self a s)).add (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

theorem IsEig.mul {D : Module.End ℂ W} (hD : IsDer 0 D) {v v' : ℂ} {x y : W}
    (hx : IsEig D v x) (hy : IsEig D v' y) : IsEig D (v + v') (x * y) := by
  unfold IsEig at *
  rw [hD x y, Function.iterate_zero, id_eq, hx, hy, smul_mul_assoc, mul_smul_comm, add_smul]

theorem IsEig.congr {D : Module.End ℂ W} {v v' : ℂ} {x : W} (hx : IsEig D v x) (h : v = v') :
    IsEig D v' x := h ▸ hx

/-- A homogeneous derivation `A` commutes with an even derivation `B` as soon as `B` acts on
each generator and on its `A`-image by the same scalar. -/
theorem comm_of_eig {p : ℕ} {A B : Module.End ℂ W} (hA : HomDer p A) (hB : HomDer 0 B)
    (h : ∀ g : Gen, ∃ v, IsEig B v g.elt ∧ IsEig B v (A g.elt)) : B * A = A * B := by
  have h0 := (hA.comm_even hB).isDer.ext (IsDer.zero p) fun g => by
    obtain ⟨v, h1, h2⟩ := h g
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply]
    rw [h1, map_smul, h2, sub_self]
  exact (sub_eq_zero.mp h0).symm

/-- Commutation transfers to adjoints. -/
theorem comm_of_adj_pair {A A' B B' : Module.End ℂ W} (hA : IsAdj A A') (hB : IsAdj B B')
    (h : A * B = B * A) : B' * A' = A' * B' := by
  have h1 := hA.comp hB
  have h2 := hB.comp hA
  rw [h] at h1
  exact h1.unique h2

/-! ## Loop weight and σ-degree -/

/-- The loop weight: `σ^a(-k)` has weight `k`, `ψ^a(-(i+1))` has weight `i + 1`. -/
def Wt : Module.End ℂ W := diagDer (fun g => g.index) (fun n => n.index + 1)

/-- The σ-degree. -/
def Sd : Module.End ℂ W := diagDer (fun _ => 1) (fun _ => 0)

theorem homDer_Wt : HomDer 0 Wt := homDer_diagDer _ _
theorem homDer_Sd : HomDer 0 Sd := homDer_diagDer _ _

theorem isAdj_Wt : IsAdj Wt Wt := isAdj_diagDer _ _
theorem isAdj_Sd : IsAdj Sd Sd := isAdj_diagDer _ _

@[simp] theorem Wt_sigOf (k : ℕ) (c : Fin 3) : Wt (sigOf k c) = (k : ℂ) • sigOf k c :=
  diagDer_sig _ _ _

@[simp] theorem Wt_psiOf (i : ℕ) (c : Fin 3) : Wt (psiOf i c) = ((i : ℂ) + 1) • psiOf i c := by
  rw [psiOf, Wt, diagDer_psi]
  push_cast
  rfl

@[simp] theorem Sd_sigOf (k : ℕ) (c : Fin 3) : Sd (sigOf k c) = sigOf k c := by
  rw [sigOf, Sd, diagDer_sig, Nat.cast_one, one_smul]

@[simp] theorem Sd_psiOf (i : ℕ) (c : Fin 3) : Sd (psiOf i c) = 0 := by
  rw [psiOf, Sd, diagDer_psi, Nat.cast_zero, zero_smul]

theorem eig_Wt_sigOf (k : ℕ) (c : Fin 3) : IsEig Wt (k : ℂ) (sigOf k c) := Wt_sigOf k c
theorem eig_Wt_psiOf (i : ℕ) (c : Fin 3) : IsEig Wt ((i : ℂ) + 1) (psiOf i c) := Wt_psiOf i c
theorem eig_Sd_sigOf (k : ℕ) (c : Fin 3) : IsEig Sd 1 (sigOf k c) := by
  simp [IsEig]
theorem eig_Sd_psiOf (i : ℕ) (c : Fin 3) : IsEig Sd 0 (psiOf i c) := by
  simp [IsEig]

theorem weight_cast {j k : ℕ} (hj : j < k) : (j : ℂ) + 1 + ((k - 1 - j : ℕ) : ℂ) = k := by
  rw [← Nat.cast_add_one, ← Nat.cast_add]
  congr 1
  omega

theorem weight_cast' {j k : ℕ} (hj : j < k) :
    (j : ℂ) + 1 + (((k - 1 - j : ℕ) : ℂ) + 1) = (k : ℂ) + 1 := by
  rw [← add_assoc, weight_cast hj]

theorem Wt_comm_dbar : Wt * dbar = dbar * Wt := by
  refine comm_of_eig homDer_dbar homDer_Wt fun g => ?_
  cases g with
  | s g =>
    obtain ⟨k, b⟩ := g
    refine ⟨(k : ℂ), eig_Wt_sigOf k b, ?_⟩
    show IsEig Wt (k : ℂ) (dbar (sigOf k b))
    rw [dbar_sigOf]
    refine IsEig.sum _ _ fun j hj => IsEig.sum _ _ fun a _ => IsEig.sum _ _ fun c _ => ?_
    exact (((eig_Wt_psiOf j a).mul homDer_Wt.isDer (eig_Wt_sigOf _ c)).congr
      (weight_cast (Finset.mem_range.mp hj))).smul _
  | p n =>
    obtain ⟨k, b⟩ := n
    refine ⟨(k : ℂ) + 1, eig_Wt_psiOf k b, ?_⟩
    show IsEig Wt ((k : ℂ) + 1) (dbar (psiOf k b))
    rw [dbar_psiOf]
    refine (IsEig.sum _ _ fun j hj => IsEig.sum _ _ fun a _ => IsEig.sum _ _ fun c _ => ?_).smul _
    exact (((eig_Wt_psiOf j a).mul homDer_Wt.isDer (eig_Wt_psiOf _ c)).congr
      (weight_cast' (Finset.mem_range.mp hj))).smul _

theorem Sd_comm_dbar : Sd * dbar = dbar * Sd := by
  refine comm_of_eig homDer_dbar homDer_Sd fun g => ?_
  cases g with
  | s g =>
    obtain ⟨k, b⟩ := g
    refine ⟨1, eig_Sd_sigOf k b, ?_⟩
    show IsEig Sd 1 (dbar (sigOf k b))
    rw [dbar_sigOf]
    refine IsEig.sum _ _ fun j _ => IsEig.sum _ _ fun a _ => IsEig.sum _ _ fun c _ => ?_
    exact (((eig_Sd_psiOf j a).mul homDer_Sd.isDer (eig_Sd_sigOf _ c)).congr (zero_add 1)).smul _
  | p n =>
    obtain ⟨k, b⟩ := n
    refine ⟨0, eig_Sd_psiOf k b, ?_⟩
    show IsEig Sd 0 (dbar (psiOf k b))
    rw [dbar_psiOf]
    refine (IsEig.sum _ _ fun j _ => IsEig.sum _ _ fun a _ => IsEig.sum _ _ fun c _ => ?_).smul _
    exact (((eig_Sd_psiOf j a).mul homDer_Sd.isDer (eig_Sd_psiOf _ c)).congr (add_zero 0)).smul _

theorem Wt_comm_Y (c : Fin 3) : Wt * Y c = Y c * Wt := by
  refine comm_of_eig (homDer_Y c) homDer_Wt fun g => ?_
  cases g with
  | s g =>
    obtain ⟨k, b⟩ := g
    refine ⟨(k : ℂ), eig_Wt_sigOf k b, ?_⟩
    show IsEig Wt (k : ℂ) (Y c (sigOf k b))
    rw [show Y c (sigOf k b) = ∑ d, epsilon c b d • sigOf k d by simp [Y]]
    exact IsEig.sum _ _ fun d _ => (eig_Wt_sigOf k d).smul _
  | p n =>
    obtain ⟨k, b⟩ := n
    refine ⟨(k : ℂ) + 1, eig_Wt_psiOf k b, ?_⟩
    show IsEig Wt ((k : ℂ) + 1) (Y c (psiOf k b))
    rw [show Y c (psiOf k b) = ∑ d, epsilon c b d • psiOf k d by simp [Y]]
    exact IsEig.sum _ _ fun d _ => (eig_Wt_psiOf k d).smul _

theorem Sd_comm_Y (c : Fin 3) : Sd * Y c = Y c * Sd := by
  refine comm_of_eig (homDer_Y c) homDer_Sd fun g => ?_
  cases g with
  | s g =>
    obtain ⟨k, b⟩ := g
    refine ⟨1, eig_Sd_sigOf k b, ?_⟩
    show IsEig Sd 1 (Y c (sigOf k b))
    rw [show Y c (sigOf k b) = ∑ d, epsilon c b d • sigOf k d by simp [Y]]
    exact IsEig.sum _ _ fun d _ => (eig_Sd_sigOf k d).smul _
  | p n =>
    obtain ⟨k, b⟩ := n
    refine ⟨0, eig_Sd_psiOf k b, ?_⟩
    show IsEig Sd 0 (Y c (psiOf k b))
    rw [show Y c (psiOf k b) = ∑ d, epsilon c b d • psiOf k d by simp [Y]]
    exact IsEig.sum _ _ fun d _ => (eig_Sd_psiOf k d).smul _

theorem Wt_comm_dbarDag : Wt * dbarDag = dbarDag * Wt :=
  (comm_of_adj_pair isAdj_Wt isAdj_dbar Wt_comm_dbar).symm

theorem Sd_comm_dbarDag : Sd * dbarDag = dbarDag * Sd :=
  (comm_of_adj_pair isAdj_Sd isAdj_dbar Sd_comm_dbar).symm

/-! ## Graded pieces -/

/-- The loop weight of a monomial. -/
abbrev wtVal (e : Exp) (t : Finset PMode) : ℕ :=
  diagVal (fun g => g.index) (fun n => n.index + 1) e t

/-- The σ-degree of a monomial. -/
abbrev sdVal (e : Exp) (t : Finset PMode) : ℕ := diagVal (fun _ => 1) (fun _ => 0) e t

/-- The joint eigenspace of loop weight `w` and σ-degree `s`. -/
def piece (w s : ℕ) : Submodule ℂ W where
  carrier := {x | Wt x = (w : ℂ) • x ∧ Sd x = (s : ℂ) • x}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [map_add, hx1, hy1, smul_add], by rw [map_add, hx2, hy2, smul_add]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro r x ⟨hx1, hx2⟩
    exact ⟨by rw [map_smul, hx1, smul_comm], by rw [map_smul, hx2, smul_comm]⟩

theorem mem_piece {w s : ℕ} {x : W} :
    x ∈ piece w s ↔ Wt x = (w : ℂ) • x ∧ Sd x = (s : ℂ) • x := Iff.rfl

theorem mapsTo_piece {P : Module.End ℂ W} (h1 : Wt * P = P * Wt) (h2 : Sd * P = P * Sd)
    {w s : ℕ} {x : W} (hx : x ∈ piece w s) : P x ∈ piece w s := by
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [← Module.End.mul_apply, h1, Module.End.mul_apply, hx1, map_smul]
  · rw [← Module.End.mul_apply, h2, Module.End.mul_apply, hx2, map_smul]

theorem mono_mem_piece (e : Exp) (t : Finset PMode) :
    mono e t ∈ piece (diagVal (fun g => g.index) (fun n => n.index + 1) e t)
      (diagVal (fun _ => 1) (fun _ => 0) e t) :=
  ⟨diagDer_mono _ _ e t, diagDer_mono _ _ e t⟩

/-- The even modes of index at most `w`. -/
def smodesLe (w : ℕ) : Finset SMode :=
  (Finset.range (w + 1) ×ˢ Finset.univ).image fun p => ⟨p.1, p.2⟩

/-- The odd modes of index less than `w`. -/
def pmodesLt (w : ℕ) : Finset PMode :=
  (Finset.range w ×ˢ Finset.univ).image fun p => ⟨p.1, p.2⟩

/-- A finite set containing all `(e, t)` of loop weight `w` and σ-degree `s`. -/
def gradeSupp (w s : ℕ) : Finset (Exp × Finset PMode) :=
  ((smodesLe w).finsupp fun _ => Finset.range (s + 1)) ×ˢ (pmodesLt w).powerset

theorem le_finsupp_sum (e : Exp) (f : SMode → ℕ) {g : SMode} (hg : g ∈ e.support) :
    e g * f g ≤ e.sum fun g k => k * f g :=
  Finset.single_le_sum (f := fun g => e g * f g) (fun _ _ => Nat.zero_le _) hg

theorem mem_gradeSupp {w s : ℕ} {e : Exp} {t : Finset PMode} (hw : wtVal e t = w)
    (hs : sdVal e t = s) : (e, t) ∈ gradeSupp w s := by
  unfold wtVal sdVal diagVal at *
  dsimp only at hw hs ⊢
  simp only [Finset.sum_const_zero, add_zero, mul_one] at hs
  rw [gradeSupp, Finset.mem_product, Finset.mem_finsupp_iff, Finset.mem_powerset]
  refine ⟨⟨fun g hg => ?_, fun g _ => ?_⟩, fun n hn => ?_⟩
  · have h1 := le_finsupp_sum e (fun g => g.index) hg
    have h2 : 0 < e g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
    have h3 : g.index ≤ e g * g.index := Nat.le_mul_of_pos_left _ h2
    rw [smodesLe, Finset.mem_image]
    exact ⟨(g.index, g.color), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_univ _⟩, rfl⟩
  · show e g ∈ Finset.range (s + 1)
    rw [Finset.mem_range]
    by_cases hg : g ∈ e.support
    · have h1 := le_finsupp_sum e (fun _ => 1) hg
      simp only [mul_one] at h1
      omega
    · rw [Finsupp.notMem_support_iff.mp hg]; omega
  · have h1 : n.index + 1 ≤ ∑ n ∈ t, (n.index + 1) :=
      Finset.single_le_sum (f := fun n : PMode => n.index + 1) (fun _ _ => Nat.zero_le _) hn
    rw [pmodesLt, Finset.mem_image]
    exact ⟨(n.index, n.color), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_univ _⟩, rfl⟩

theorem eq_zero_of_coefW {x : W} (h : ∀ e t, coefW x e t = 0) : x = 0 := by
  apply AddMonoidAlgebra.coeff_injective
  ext e t
  simpa [coefW] using h e t

theorem coefW_eq_zero_of_mem_piece {w s : ℕ} {x : W} (hx : x ∈ piece w s) {e : Exp}
    {t : Finset PMode} (he : (e, t) ∉ gradeSupp w s) : coefW x e t = 0 := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 := coefW_diagDer (fun g => g.index) (fun n => n.index + 1) x e t
  have h2 := coefW_diagDer (fun _ => 1) (fun _ => 0) x e t
  rw [show diagDer (fun g => g.index) (fun n => n.index + 1) x = Wt x from rfl, hx1,
    coefW_smul] at h1
  rw [show diagDer (fun _ => 1) (fun _ => 0) x = Sd x from rfl, hx2, coefW_smul] at h2
  by_contra hne
  have hw : wtVal e t = w := by
    have := mul_right_cancel₀ hne h1
    exact_mod_cast this.symm
  have hs : sdVal e t = s := by
    have := mul_right_cancel₀ hne h2
    exact_mod_cast this.symm
  exact he (mem_gradeSupp hw hs)

/-- Coordinates on the finite support of a graded piece. -/
def pieceCoord (w s : ℕ) : piece w s →ₗ[ℂ] (gradeSupp w s → ℂ) where
  toFun x p := coefW (x : W) p.1.1 p.1.2
  map_add' x y := by funext p; simp
  map_smul' r x := by funext p; simp

theorem pieceCoord_injective (w s : ℕ) : Function.Injective (pieceCoord w s) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  apply eq_zero_of_coefW
  intro e t
  by_cases he : (e, t) ∈ gradeSupp w s
  · exact congrFun hx ⟨(e, t), he⟩
  · exact coefW_eq_zero_of_mem_piece x.2 he

instance finiteDimensional_piece (w s : ℕ) : FiniteDimensional ℂ (piece w s) :=
  FiniteDimensional.of_injective (pieceCoord w s) (pieceCoord_injective w s)

end KhanSL2.StrongMacdonald
