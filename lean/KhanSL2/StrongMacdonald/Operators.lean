module

public import KhanSL2.StrongMacdonald.HomDer
public import KhanSL2.StrongMacdonald.Local
public import KhanSL2.CEDerivationBasics

@[expose] public section

/-!
# The operators of the Fishel–Grojnowski–Teleman Laplacian for `𝔰𝔩₂`

Real compact basis `[L_a, L_b] = Σ_c ε_abc L_c`. Index conventions:
`sigOf k c = σ^c(-k)` (`k ≥ 0`) and `psiOf i c = ψ^c(-(i+1))`.

The metric is `⟨σ|σ⟩ = 1` (Bargmann on monomials) and `⟨ψ^c(-k)|ψ^c(-k)⟩ = 1/k`.
The `...Dag` operators are the explicit adjoints for this metric; adjointness itself is
proved separately.

* `Rlow a m`, `Rup a m`: coadjoint action of `z^{±m} L_a` on the even variables.
* `adLow a m`, `adUp a m`: the same on the odd variables.
* `adUpDag a m`, `adLowDag a m`: adjoints of `adUp`, `adLow`.
* `dUp a m`: the odd derivation `σ^b(-k) ↦ Σ ε_abc ψ^c(-(k+m))`; `dUpDag` its adjoint.
* `dbar`: the Koszul differential `Σ_{a,m≥1} ψ^a(-m) (R_a(m) + ½ ad_a(m))`.

The loop-degree families are indexed by `i = m - 1 ≥ 0`.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

def sigOf (k : ℕ) (c : Fin 3) : W := sig ⟨k, c⟩
def psiOf (i : ℕ) (c : Fin 3) : W := psi ⟨i, c⟩

/-! ## Even derivations -/

def Rlow (a : Fin 3) (m : ℕ) : Module.End ℂ W :=
  mkDer (fun g => if m ≤ g.index then ∑ c, epsilon a g.color c • sigOf (g.index - m) c else 0)
    (fun _ => 0)

def Rup (a : Fin 3) (m : ℕ) : Module.End ℂ W :=
  mkDer (fun g => ∑ c, epsilon a g.color c • sigOf (g.index + m) c) (fun _ => 0)

def adLow (a : Fin 3) (m : ℕ) : Module.End ℂ W :=
  mkDer (fun _ => 0)
    (fun n => if m ≤ n.index then ∑ c, epsilon a n.color c • psiOf (n.index - m) c else 0)

def adUp (a : Fin 3) (m : ℕ) : Module.End ℂ W :=
  mkDer (fun _ => 0) (fun n => ∑ c, epsilon a n.color c • psiOf (n.index + m) c)

def adUpDag (a : Fin 3) (m : ℕ) : Module.End ℂ W :=
  mkDer (fun _ => 0)
    (fun n => if m ≤ n.index then
      ∑ b, (epsilon a b n.color * (((n.index + 1 - m : ℕ) : ℂ) / ((n.index : ℂ) + 1))) •
        psiOf (n.index - m) b else 0)

def adLowDag (a : Fin 3) (m : ℕ) : Module.End ℂ W :=
  mkDer (fun _ => 0)
    (fun n => ∑ b, (epsilon a b n.color * (((n.index + 1 + m : ℕ) : ℂ) / ((n.index : ℂ) + 1))) •
      psiOf (n.index + m) b)

/-! ## Odd derivations -/

/-- `σ^b(-k) ↦ Σ_c ε_abc ψ^c(-(k+m))`, for `m ≥ 1`. -/
def dUp (a : Fin 3) (m : ℕ) : Module.End ℂ W :=
  mkDer (fun g => ∑ c, epsilon a g.color c • psiOf (g.index + m - 1) c) (fun _ => 0)

def dUpDag (a : Fin 3) (m : ℕ) : Module.End ℂ W :=
  mkDer (fun _ => 0)
    (fun n => if m ≤ n.index + 1 then
      ∑ b, (epsilon a b n.color * (1 / ((n.index : ℂ) + 1))) • sigOf (n.index + 1 - m) b else 0)

/-! ## The Koszul differential -/

def dbarSig (g : SMode) : W :=
  ∑ m ∈ Finset.range g.index, ∑ a, ∑ c,
    epsilon a g.color c • (psiOf m a * sigOf (g.index - 1 - m) c)

def dbarPsi (n : PMode) : W :=
  (1 / 2 : ℂ) • ∑ m ∈ Finset.range n.index, ∑ a, ∑ c,
    epsilon a n.color c • (psiOf m a * psiOf (n.index - 1 - m) c)

def dbar : Module.End ℂ W := mkDer dbarSig dbarPsi

/-! ## Homogeneity -/

theorem isPar_sigOf (k : ℕ) (c : Fin 3) : IsPar 0 (sigOf k c) := isPar_sig _
theorem isPar_psiOf (i : ℕ) (c : Fin 3) : IsPar 1 (psiOf i c) := isPar_psi _

theorem isPar_sum_smul {q : ℕ} {ι : Type*} (s : Finset ι) (r : ι → ℂ) (x : ι → W)
    (hx : ∀ i, IsPar q (x i)) : IsPar q (∑ i ∈ s, r i • x i) :=
  IsPar.sum s _ fun i _ => (hx i).smul (r i)

theorem isPar_ite {q : ℕ} (P : Prop) [Decidable P] {x : W} (hx : IsPar q x) :
    IsPar q (if P then x else 0) := by
  split
  · exact hx
  · exact IsPar.zero q

theorem homDer_Rlow (a : Fin 3) (m : ℕ) : HomDer 0 (Rlow a m) :=
  mkDer_homDer _ _ (fun _ => isPar_ite _ (isPar_sum_smul _ _ _ fun _ => isPar_sigOf _ _))
    (fun _ => IsPar.zero _)

theorem homDer_Rup (a : Fin 3) (m : ℕ) : HomDer 0 (Rup a m) :=
  mkDer_homDer _ _ (fun _ => isPar_sum_smul _ _ _ fun _ => isPar_sigOf _ _) (fun _ => IsPar.zero _)

theorem homDer_adLow (a : Fin 3) (m : ℕ) : HomDer 0 (adLow a m) :=
  mkDer_homDer _ _ (fun _ => IsPar.zero _)
    (fun _ => isPar_ite _ (isPar_sum_smul _ _ _ fun _ => isPar_psiOf _ _))

theorem homDer_adUp (a : Fin 3) (m : ℕ) : HomDer 0 (adUp a m) :=
  mkDer_homDer _ _ (fun _ => IsPar.zero _) (fun _ => isPar_sum_smul _ _ _ fun _ => isPar_psiOf _ _)

theorem homDer_adUpDag (a : Fin 3) (m : ℕ) : HomDer 0 (adUpDag a m) :=
  mkDer_homDer _ _ (fun _ => IsPar.zero _)
    (fun _ => isPar_ite _ (isPar_sum_smul _ _ _ fun _ => isPar_psiOf _ _))

theorem homDer_adLowDag (a : Fin 3) (m : ℕ) : HomDer 0 (adLowDag a m) :=
  mkDer_homDer _ _ (fun _ => IsPar.zero _) (fun _ => isPar_sum_smul _ _ _ fun _ => isPar_psiOf _ _)

theorem homDer_dUp (a : Fin 3) (m : ℕ) : HomDer 1 (dUp a m) :=
  mkDer_homDer _ _ (fun _ => isPar_sum_smul _ _ _ fun _ => isPar_psiOf _ _)
    (fun _ => IsPar.zero _)

theorem homDer_dUpDag (a : Fin 3) (m : ℕ) : HomDer 1 (dUpDag a m) :=
  mkDer_homDer _ _ (fun _ => IsPar.zero _)
    (fun _ => isPar_ite _ (isPar_sum_smul _ _ _ fun _ => (isPar_sigOf _ _).add_two))

theorem isPar_dbarSig (g : SMode) : IsPar 1 (dbarSig g) :=
  IsPar.sum _ _ fun _ _ => IsPar.sum _ _ fun _ _ => IsPar.sum _ _ fun _ _ =>
    (show IsPar (1 + 0) _ from (isPar_psiOf _ _).mul (isPar_sigOf _ _)).smul _

theorem isPar_dbarPsi (n : PMode) : IsPar 2 (dbarPsi n) :=
  (IsPar.sum _ _ fun _ _ => IsPar.sum _ _ fun _ _ => IsPar.sum _ _ fun _ _ =>
    (show IsPar (1 + 1) _ from (isPar_psiOf _ _).mul (isPar_psiOf _ _)).smul _).smul _

theorem homDer_dbar : HomDer 1 dbar := mkDer_homDer _ _ isPar_dbarSig isPar_dbarPsi

/-! ## Values on generators -/

section Values
variable (a b : Fin 3) (m k : ℕ)

@[simp] theorem Rlow_sigOf : Rlow a m (sigOf k b) =
    if m ≤ k then ∑ c, epsilon a b c • sigOf (k - m) c else 0 := mkDer_sig _ _ _
@[simp] theorem Rlow_psiOf : Rlow a m (psiOf k b) = 0 := mkDer_psi _ _ _
@[simp] theorem Rup_sigOf : Rup a m (sigOf k b) = ∑ c, epsilon a b c • sigOf (k + m) c :=
  mkDer_sig _ _ _
@[simp] theorem Rup_psiOf : Rup a m (psiOf k b) = 0 := mkDer_psi _ _ _
@[simp] theorem adLow_sigOf : adLow a m (sigOf k b) = 0 := mkDer_sig _ _ _
@[simp] theorem adLow_psiOf : adLow a m (psiOf k b) =
    if m ≤ k then ∑ c, epsilon a b c • psiOf (k - m) c else 0 := mkDer_psi _ _ _
@[simp] theorem adUp_sigOf : adUp a m (sigOf k b) = 0 := mkDer_sig _ _ _
@[simp] theorem adUp_psiOf : adUp a m (psiOf k b) = ∑ c, epsilon a b c • psiOf (k + m) c :=
  mkDer_psi _ _ _
@[simp] theorem adUpDag_sigOf : adUpDag a m (sigOf k b) = 0 := mkDer_sig _ _ _
@[simp] theorem adUpDag_psiOf : adUpDag a m (psiOf k b) =
    if m ≤ k then ∑ c, (epsilon a c b * (((k + 1 - m : ℕ) : ℂ) / ((k : ℂ) + 1))) •
      psiOf (k - m) c else 0 := mkDer_psi _ _ _
@[simp] theorem adLowDag_sigOf : adLowDag a m (sigOf k b) = 0 := mkDer_sig _ _ _
@[simp] theorem adLowDag_psiOf : adLowDag a m (psiOf k b) =
    ∑ c, (epsilon a c b * (((k + 1 + m : ℕ) : ℂ) / ((k : ℂ) + 1))) • psiOf (k + m) c :=
  mkDer_psi _ _ _
@[simp] theorem dUp_sigOf : dUp a m (sigOf k b) = ∑ c, epsilon a b c • psiOf (k + m - 1) c :=
  mkDer_sig _ _ _
@[simp] theorem dUp_psiOf : dUp a m (psiOf k b) = 0 := mkDer_psi _ _ _
@[simp] theorem dUpDag_sigOf : dUpDag a m (sigOf k b) = 0 := mkDer_sig _ _ _
@[simp] theorem dUpDag_psiOf : dUpDag a m (psiOf k b) =
    if m ≤ k + 1 then ∑ c, (epsilon a c b * (1 / ((k : ℂ) + 1))) • sigOf (k + 1 - m) c
    else 0 := mkDer_psi _ _ _
@[simp] theorem dbar_sigOf : dbar (sigOf k b) =
    ∑ j ∈ Finset.range k, ∑ a, ∑ c, epsilon a b c • (psiOf j a * sigOf (k - 1 - j) c) :=
  mkDer_sig _ _ _
@[simp] theorem dbar_psiOf : dbar (psiOf k b) =
    (1 / 2 : ℂ) • ∑ j ∈ Finset.range k, ∑ a, ∑ c,
      epsilon a b c • (psiOf j a * psiOf (k - 1 - j) c) := mkDer_psi _ _ _

end Values

/-! ## The loop-degree families -/

/-- Contraction with `ψ^a(-(i+1))`. -/
def iota (i : ℕ) (a : Fin 3) : Module.End ℂ W := iP ⟨i, a⟩

/-- The metric weight `1/m` of `ψ(-m)`, `m = i + 1`. -/
def lam (i : ℕ) : ℂ := 1 / ((i : ℂ) + 1)

/-- `T_a(m) = R_a(m) + ½ ad_a(m)`. -/
def T (i : ℕ) (a : Fin 3) : Module.End ℂ W := Rlow a (i + 1) + (1 / 2 : ℂ) • adLow a (i + 1)

/-- `T_a(m)^† = -R_a(-m) + ½ ad_a(m)^†`. -/
def Td (i : ℕ) (a : Fin 3) : Module.End ℂ W := -Rup a (i + 1) + (1 / 2 : ℂ) • adLowDag a (i + 1)

/-- The Lie derivative `L_a(m) = R_a(m) + ad_a(m)`. -/
def L (i : ℕ) (a : Fin 3) : Module.End ℂ W := Rlow a (i + 1) + adLow a (i + 1)

/-- `X_a(m) = R_a(m) - ad_a(-m)^†`. -/
def X (i : ℕ) (a : Fin 3) : Module.End ℂ W := Rlow a (i + 1) - adUpDag a (i + 1)

/-- `X_a(m)^† = -R_a(-m) - ad_a(-m)`. -/
def Xd (i : ℕ) (a : Fin 3) : Module.End ℂ W := -Rup a (i + 1) - adUp a (i + 1)

/-- `d_a(-m)`. -/
def dU (i : ℕ) (a : Fin 3) : Module.End ℂ W := dUp a (i + 1)

/-- `d_a(-m)^†`. -/
def dUd (i : ℕ) (a : Fin 3) : Module.End ℂ W := dUpDag a (i + 1)

/-- The total coadjoint action of `L_c`. -/
def Y (c : Fin 3) : Module.End ℂ W := Rlow c 0 + adLow c 0

theorem homDer_iota (i : ℕ) (a : Fin 3) : HomDer 1 (iota i a) := iP_homDer _
theorem homDer_T (i : ℕ) (a : Fin 3) : HomDer 0 (T i a) :=
  (homDer_Rlow _ _).add ((homDer_adLow _ _).smul _)
theorem homDer_Td (i : ℕ) (a : Fin 3) : HomDer 0 (Td i a) :=
  (homDer_Rup _ _).neg.add ((homDer_adLowDag _ _).smul _)
theorem homDer_L (i : ℕ) (a : Fin 3) : HomDer 0 (L i a) :=
  (homDer_Rlow _ _).add (homDer_adLow _ _)
theorem homDer_X (i : ℕ) (a : Fin 3) : HomDer 0 (X i a) :=
  (homDer_Rlow _ _).sub (homDer_adUpDag _ _)
theorem homDer_Xd (i : ℕ) (a : Fin 3) : HomDer 0 (Xd i a) :=
  (homDer_Rup _ _).neg.sub (homDer_adUp _ _)
theorem homDer_dU (i : ℕ) (a : Fin 3) : HomDer 1 (dU i a) := homDer_dUp _ _
theorem homDer_dUd (i : ℕ) (a : Fin 3) : HomDer 1 (dUd i a) := homDer_dUpDag _ _
theorem homDer_Y (c : Fin 3) : HomDer 0 (Y c) := (homDer_Rlow _ _).add (homDer_adLow _ _)

@[simp] theorem iota_sigOf (i k : ℕ) (a b : Fin 3) : iota i a (sigOf k b) = 0 := iP_sig _ _
@[simp] theorem iota_psiOf (i k : ℕ) (a b : Fin 3) :
    iota i a (psiOf k b) = if i = k ∧ a = b then 1 else 0 := by
  rw [iota, psiOf, iP_psi]
  congr 1
  apply propext
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-! ## Families that vanish on low modes -/

/-- The family kills every element generated by modes of index `< N` from `i = N` on. -/
def Kills (B : ℕ → Module.End ℂ W) : Prop := ∀ N i, N ≤ i → ∀ x, Low N x → B i x = 0

theorem Kills.evZero {B : ℕ → Module.End ℂ W} (h : Kills B) : EvZero B :=
  EvZero.of_low h

theorem Kills.mul_left {B : ℕ → Module.End ℂ W} (h : Kills B) (A : ℕ → Module.End ℂ W) :
    Kills (fun i => A i * B i) := fun N i hi x hx => by
  rw [Module.End.mul_apply, h N i hi x hx, map_zero]

theorem Kills.add {B C : ℕ → Module.End ℂ W} (hB : Kills B) (hC : Kills C) :
    Kills (fun i => B i + C i) := fun N i hi x hx => by
  rw [LinearMap.add_apply, hB N i hi x hx, hC N i hi x hx, add_zero]

theorem Kills.sub {B C : ℕ → Module.End ℂ W} (hB : Kills B) (hC : Kills C) :
    Kills (fun i => B i - C i) := fun N i hi x hx => by
  rw [LinearMap.sub_apply, hB N i hi x hx, hC N i hi x hx, sub_zero]

theorem Kills.smul {B : ℕ → Module.End ℂ W} (hB : Kills B) (r : ℕ → ℂ) :
    Kills (fun i => r i • B i) := fun N i hi x hx => by
  rw [LinearMap.smul_apply, hB N i hi x hx, smul_zero]

theorem Kills.neg {B : ℕ → Module.End ℂ W} (hB : Kills B) : Kills (fun i => -B i) :=
  fun N i hi x hx => by rw [LinearMap.neg_apply, hB N i hi x hx, neg_zero]

theorem Kills.sum {ι : Type*} (s : Finset ι) {B : ι → ℕ → Module.End ℂ W}
    (hB : ∀ j ∈ s, Kills (B j)) : Kills (fun i => ∑ j ∈ s, B j i) := fun N i hi x hx => by
  rw [LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun j hj => hB j hj N i hi x hx

theorem kills_of_homDer {p : ℕ} {B : ℕ → Module.End ℂ W} (hD : ∀ i, HomDer p (B i))
    (hσ : ∀ N i, N ≤ i → ∀ k b, k < N → B i (sigOf k b) = 0)
    (hψ : ∀ N i, N ≤ i → ∀ k b, k < N → B i (psiOf k b) = 0) : Kills B :=
  fun N i hi _ hx => (hD i).isDer.eq_zero_of_low (fun g hg => hσ N i hi g.index g.color hg)
    (fun m hm => hψ N i hi m.index m.color hm) hx

theorem kills_iota (a : Fin 3) : Kills (fun i => iota i a) :=
  kills_of_homDer (fun i => homDer_iota i a) (fun _ _ _ _ _ _ => by simp)
    (fun N i hi k b hk => by rw [iota_psiOf, if_neg (by omega)])

theorem kills_Rlow (a : Fin 3) : Kills (fun i => Rlow a (i + 1)) :=
  kills_of_homDer (fun i => homDer_Rlow a (i + 1))
    (fun N i hi k b hk => by rw [Rlow_sigOf, if_neg (by omega)]) (fun _ _ _ _ _ _ => by simp)

theorem kills_adLow (a : Fin 3) : Kills (fun i => adLow a (i + 1)) :=
  kills_of_homDer (fun i => homDer_adLow a (i + 1)) (fun _ _ _ _ _ _ => by simp)
    (fun N i hi k b hk => by rw [adLow_psiOf, if_neg (by omega)])

theorem kills_adUpDag (a : Fin 3) : Kills (fun i => adUpDag a (i + 1)) :=
  kills_of_homDer (fun i => homDer_adUpDag a (i + 1)) (fun _ _ _ _ _ _ => by simp)
    (fun N i hi k b hk => by rw [adUpDag_psiOf, if_neg (by omega)])

theorem kills_dUd (a : Fin 3) : Kills (fun i => dUd i a) :=
  kills_of_homDer (fun i => homDer_dUd i a) (fun _ _ _ _ _ _ => by simp [dUd])
    (fun N i hi k b hk => by rw [dUd, dUpDag_psiOf, if_neg (by omega)])

theorem kills_L (a : Fin 3) : Kills (fun i => L i a) := (kills_Rlow a).add (kills_adLow a)

theorem kills_X (a : Fin 3) : Kills (fun i => X i a) := (kills_Rlow a).sub (kills_adUpDag a)

end KhanSL2.StrongMacdonald
