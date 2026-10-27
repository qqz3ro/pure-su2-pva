module

public import KhanSL2.BGGBridge.Coefficients
public import KhanSL2.BGGBridge.ContractionOps
public import KhanSL2.BGG.PositiveTransferEquivariance
public import KhanSL2.BGG.PositiveTransferDegree
public import KhanSL2.BGG.PositiveTransferEnergy

@[expose] public section
set_option backward.isDefEq.respectTransparency false


/-!
# The BGG contraction with coefficients

For a module `N` over `𝔩 = 𝔰𝔩₂[z]`, base change along the right action of `U(𝔩₊)` turns
the BGG special contraction into a special contraction between:
* the CE chains `Λ𝔩₊ ⊗ N` with the base-changed free CE differential; and
* the harmonic chains `Harm ⊗ N`, where `Harm = ⊕_p V(2p)`.

All maps commute with the diagonal action of the constant `𝔰𝔩₂`, so the contraction descends
to `𝔰𝔩₂`-coinvariants. All maps also respect exterior degree; the homotopy raises it by one.
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.BGGBridge

open KhanSL2.BGG

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The additive group of harmonic chains, taken from the finitely supported functions rather
than from the exterior ring structure. The two agree definitionally, but this one unifies
cheaply with the additive monoid used by tensor products. -/
instance (priority := 2000) harmonicAddCommGroup : AddCommGroup PositiveCE.Harmonic :=
  @Submodule.addCommGroup ℂ PositiveCE.Cochain _ Finsupp.instAddCommGroup _ PositiveCE.Harmonic

variable (N : Type*) [AddCommGroup N] [Module ℂ N] [LieRingModule Current N]
  [LieModule ℂ Current N]

/-- CE chains `Λ𝔩₊ ⊗ N`, in the BGG exterior model. -/
abbrev ChainN := PositiveCE.Cochain ⊗[ℂ] N

/-- Harmonic chains `Harm ⊗ N`. -/
abbrev HarmN := PositiveCE.Harmonic ⊗[ℂ] N

/-- The base-changed free CE differential. -/
def dC : Module.End ℂ (ChainN N) := base (rightAction N) FreeCE.differential

/-- The base-changed BGG differential. -/
def dH : Module.End ℂ (HarmN N) := base (rightAction N) PositiveTransfer.differential

/-- The BGG contraction with coefficients in `N`. -/
def cN : TauCeti.LinearSpecialContraction (M := ChainN N) (N := HarmN N) (dC N) (dH N) :=
  baseContraction (rightAction N) PositiveTransfer.contraction

/-! ## The constant `𝔰𝔩₂` -/

/-- The diagonal constant action on chains. -/
def actC (x : G) : Module.End ℂ (ChainN N) :=
  diag (ColorRoot.positiveAction x) (LieModule.toEnd ℂ Current N (constant x))

/-- The diagonal constant action on harmonic chains. -/
def actH (x : G) : Module.End ℂ (HarmN N) :=
  diag (LieModule.toEnd ℂ G PositiveCE.Harmonic x) (LieModule.toEnd ℂ Current N (constant x))

theorem constantAction_eq_diag (x : G) (t : FreeCE.Chain) :
    FreeCE.constantAction x t = diag (positiveUEAction x) (ColorRoot.positiveAction x) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u ω => rw [FreeCE.constantAction_tmul, diag_tmul]
  | add s t hs ht => rw [map_add, hs, ht, map_add]

theorem harmonicAction_eq_diag (x : G) (t : PositiveTransfer.HarmonicChain) :
    positiveTensorAction PositiveCE.Harmonic x t =
      diag (positiveUEAction x) (LieModule.toEnd ℂ G PositiveCE.Harmonic x) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u ω => rw [positiveTensorAction_tmul, diag_tmul]; rfl
  | add s t hs ht => rw [map_add, hs, ht, map_add]

theorem compat (x : G) (u : PositiveEnveloping) (n : N) :
    LieModule.toEnd ℂ Current N (constant x) (ract (rightAction N) u n) -
        ract (rightAction N) u (LieModule.toEnd ℂ Current N (constant x) n) =
      ract (rightAction N) (positiveUEAction x u) n :=
  ract_constant N x u n

theorem dC_actC (x : G) (z : ChainN N) : dC N (actC N x z) = actC N x (dC N z) :=
  base_diag (rightAction N) (positiveUEAction_one x) (compat N x) FreeCE.differential
    (fun t => by
      rw [← constantAction_eq_diag, ← constantAction_eq_diag]
      exact FreeCE.differential_constantAction x t) z

theorem dH_actH (x : G) (z : HarmN N) : dH N (actH N x z) = actH N x (dH N z) :=
  base_diag (rightAction N) (positiveUEAction_one x) (compat N x) PositiveTransfer.differential
    (fun t => by
      rw [← harmonicAction_eq_diag, ← harmonicAction_eq_diag]
      exact PositiveTransfer.differential_constantAction x t) z

theorem incl_actH (x : G) (z : HarmN N) : (cN N).incl (actH N x z) = actC N x ((cN N).incl z) :=
  base_diag (rightAction N) (positiveUEAction_one x) (compat N x) PositiveTransfer.contraction.incl
    (fun t => by
      rw [← harmonicAction_eq_diag, ← constantAction_eq_diag]
      exact PositiveTransfer.contraction_incl_constantAction x t) z

theorem proj_actC (x : G) (z : ChainN N) : (cN N).proj (actC N x z) = actH N x ((cN N).proj z) :=
  base_diag (rightAction N) (positiveUEAction_one x) (compat N x) PositiveTransfer.contraction.proj
    (fun t => by
      rw [← constantAction_eq_diag, ← harmonicAction_eq_diag]
      exact PositiveTransfer.contraction_proj_constantAction x t) z

theorem homotopy_actC (x : G) (z : ChainN N) :
    (cN N).homotopy (actC N x z) = actC N x ((cN N).homotopy z) :=
  base_diag (rightAction N) (positiveUEAction_one x) (compat N x)
    PositiveTransfer.contraction.homotopy
    (fun t => by
      rw [← constantAction_eq_diag, ← constantAction_eq_diag]
      exact PositiveTransfer.contraction_homotopy_constantAction x t) z

/-! ## Coinvariants -/

/-- The `𝔰𝔩₂`-relations on chains. -/
def relC : Submodule ℂ (ChainN N) := ⨆ x : G, LinearMap.range (actC N x)

/-- The `𝔰𝔩₂`-relations on harmonic chains. -/
def relH : Submodule ℂ (HarmN N) := ⨆ x : G, LinearMap.range (actH N x)

theorem le_comap_of_commute {P Q : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q]
    [Module ℂ Q] (X : G → Module.End ℂ P) (Y : G → Module.End ℂ Q) (f : P →ₗ[ℂ] Q)
    (hf : ∀ x z, f (X x z) = Y x (f z)) :
    (⨆ x : G, LinearMap.range (X x)) ≤ (⨆ x : G, LinearMap.range (Y x)).comap f := by
  apply iSup_le
  rintro x _ ⟨z, rfl⟩
  rw [Submodule.mem_comap, hf]
  exact Submodule.mem_iSup_of_mem x ⟨f z, rfl⟩

theorem relC_le_dC : relC N ≤ (relC N).comap (dC N) := by
  unfold relC
  exact le_comap_of_commute (actC N) (actC N) (dC N) (dC_actC N)

theorem relH_le_dH : relH N ≤ (relH N).comap (dH N) := by
  unfold relH
  exact le_comap_of_commute (actH N) (actH N) (dH N) (dH_actH N)

theorem relH_le_incl : relH N ≤ (relC N).comap (cN N).incl := by
  unfold relH relC
  exact le_comap_of_commute (actH N) (actC N) (cN N).incl (incl_actH N)

theorem relC_le_proj : relC N ≤ (relH N).comap (cN N).proj := by
  unfold relH relC
  exact le_comap_of_commute (actC N) (actH N) (cN N).proj (proj_actC N)

theorem relC_le_homotopy : relC N ≤ (relC N).comap (cN N).homotopy := by
  unfold relC
  exact le_comap_of_commute (actC N) (actC N) (cN N).homotopy (homotopy_actC N)

/-- The CE differential on coinvariants. -/
def dCq : Module.End ℂ (ChainN N ⧸ relC N) := (relC N).mapQ (relC N) (dC N) (relC_le_dC N)

/-- The BGG differential on coinvariants. -/
def dHq : Module.End ℂ (HarmN N ⧸ relH N) := (relH N).mapQ (relH N) (dH N) (relH_le_dH N)

/-- The BGG contraction on coinvariants. -/
def qcN : TauCeti.LinearSpecialContraction (M := ChainN N ⧸ relC N) (N := HarmN N ⧸ relH N)
    (dCq N) (dHq N) :=
  quotContraction (cN N) (relC N) (relH N) (relC_le_dC N) (relH_le_dH N) (relH_le_incl N)
    (relC_le_proj N) (relC_le_homotopy N)

/-! ## Exterior degree -/

/-- Exterior degree `p` in the BGG exterior model. -/
def degC (p : ℕ) : Submodule ℂ PositiveCE.Cochain :=
  Finsupp.supported ℂ ℂ {s : Finset PositiveCE.Mode | s.card = p}

/-- Harmonic chains of degree `p`, a copy of `V(2p)`. -/
def degH (p : ℕ) : Submodule ℂ PositiveCE.Harmonic := (PositiveCE.harmonicDegree p).toSubmodule

theorem incl_mem_degree {p : ℕ} {z : HarmN N} (hz : z ∈ tensorLeft (degH p)) :
    (cN N).incl z ∈ tensorLeft (degC p) :=
  base_mem_tensorLeft (rightAction N) _ (fun _ ha => PositiveTransfer.contraction_incl_mem_degree
    (Submodule.tmul_mem_baseChange_of_mem 1 ha)) hz

theorem proj_mem_degree {p : ℕ} {z : ChainN N} (hz : z ∈ tensorLeft (degC p)) :
    (cN N).proj z ∈ tensorLeft (degH p) :=
  base_mem_tensorLeft (rightAction N) _ (fun _ ha => PositiveTransfer.contraction_proj_mem_degree
    (Submodule.tmul_mem_baseChange_of_mem 1 ha)) hz

theorem homotopy_mem_degree {p : ℕ} {z : ChainN N} (hz : z ∈ tensorLeft (degC p)) :
    (cN N).homotopy z ∈ tensorLeft (degC (p + 1)) :=
  base_mem_tensorLeft (rightAction N) _
    (fun _ ha => PositiveTransfer.contraction_homotopy_mem_degree
      (Submodule.tmul_mem_baseChange_of_mem 1 ha)) hz

theorem dH_mem_degree {p : ℕ} {z : HarmN N} (hz : z ∈ tensorLeft (degH (p + 1))) :
    dH N z ∈ tensorLeft (degH p) :=
  base_mem_tensorLeft (rightAction N) _ (fun _ ha => PositiveTransfer.differential_mem_degree
    (Submodule.tmul_mem_baseChange_of_mem 1 ha)) hz

end KhanSL2.BGGBridge
