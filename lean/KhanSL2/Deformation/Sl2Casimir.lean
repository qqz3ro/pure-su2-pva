module

public import KhanSL2.BGG.CasimirSplitting
public import TauCeti.Algebra.Lie.Submodule.Decomposition
public import KhanSL2.Deformation.Derivations
public import KhanSL2.BGG.FreeCEBasis
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

/-!
# Casimir splitting for an `sl₂` action given by three colour operators

Three operators `L₀, L₁, L₂` on a complex vector space with `[L_a, L_b] = Σ_c ε_{abc} L_c` define
an action of `𝔰𝔩₂` through the colour basis (`colorRep`). On a finite-dimensional space the colour
Casimir `Ω = Σ_a L_a²` (a nonzero multiple of the standard Casimir) satisfies
* `ker Ω ⊕ range Ω` (`casimir_isCompl`), by complete reducibility;
* `ker Ω` is the space of invariants (`casimir_ker`), because the Casimir is injective on every
  nontrivial irreducible module.
-/

noncomputable section

namespace KhanSL2.Deformation

open KhanSL2.BGG

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Three operators satisfying the colour-basis relations of `𝔰𝔩₂`. -/
def IsColorAction (L : Fin 3 → Module.End ℂ M) : Prop :=
  ∀ a b, L a * L b - L b * L a = ∑ c : Fin 3, epsilon a b c • L c

/-- The colour Casimir `Σ_a L_a²`. -/
def colorCasimir (L : Fin 3 → Module.End ℂ M) : Module.End ℂ M := ∑ a : Fin 3, L a * L a

/-- The linear map `x ↦ Σ_a x_a L_a` in colour coordinates. -/
def colorRepLinear (L : Fin 3 → Module.End ℂ M) : G →ₗ[ℂ] Module.End ℂ M :=
  ∑ a : Fin 3, (FreeCE.colorBasis.coord a).smulRight (L a)

theorem colorRepLinear_basis (L : Fin 3 → Module.End ℂ M) (a : Fin 3) :
    colorRepLinear L (FreeCE.colorBasis a) = L a := by
  simp only [colorRepLinear, LinearMap.sum_apply, LinearMap.smulRight_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem colorRep_map_lie {L : Fin 3 → Module.End ℂ M} (hL : IsColorAction L) (x y : G) :
    colorRepLinear L ⁅x, y⁆ = ⁅colorRepLinear L x, colorRepLinear L y⁆ := by
  let B₁ : G →ₗ[ℂ] G →ₗ[ℂ] Module.End ℂ M := LinearMap.mk₂ ℂ
    (fun x y => colorRepLinear L ⁅x, y⁆)
    (fun x₁ x₂ y => by rw [add_lie, map_add])
    (fun c x y => by rw [smul_lie, map_smul])
    (fun x y₁ y₂ => by rw [lie_add, map_add])
    (fun c x y => by rw [lie_smul, map_smul])
  let B₂ : G →ₗ[ℂ] G →ₗ[ℂ] Module.End ℂ M := LinearMap.mk₂ ℂ
    (fun x y => ⁅colorRepLinear L x, colorRepLinear L y⁆)
    (fun x₁ x₂ y => by rw [map_add, add_lie])
    (fun c x y => by rw [map_smul, smul_lie])
    (fun x y₁ y₂ => by rw [map_add, lie_add])
    (fun c x y => by rw [map_smul, lie_smul])
  have h : B₁ = B₂ := by
    apply LinearMap.ext_basis FreeCE.colorBasis FreeCE.colorBasis
    intro a b
    simp only [B₁, B₂, LinearMap.mk₂_apply, FreeCE.colorBasis_apply, MatrixSL2.color_bracket,
      map_sum, map_smul]
    simp only [← FreeCE.colorBasis_apply, colorRepLinear_basis, Ring.lie_def]
    exact (hL a b).symm
  exact LinearMap.congr_fun₂ h x y

/-- **The `𝔰𝔩₂` action** defined by colour operators. -/
def colorRep (L : Fin 3 → Module.End ℂ M) (hL : IsColorAction L) : G →ₗ⁅ℂ⁆ Module.End ℂ M where
  toLinearMap := colorRepLinear L
  map_lie' {x y} := colorRep_map_lie hL x y

theorem colorRep_color (L : Fin 3 → Module.End ℂ M) (hL : IsColorAction L) (a : Fin 3) :
    colorRep L hL (MatrixSL2.color a) = L a := by
  rw [← FreeCE.colorBasis_apply]
  exact colorRepLinear_basis L a

section Lie

variable (L : Fin 3 → Module.End ℂ M) (hL : IsColorAction L)
include hL

/-- The colour Casimir is `-1/2` times the standard Casimir of the induced action. -/
theorem colorCasimir_eq (u : M) :
    letI : LieRingModule G M := LieRingModule.compLieHom M (colorRep L hL)
    letI : LieModule ℂ G M := LieModule.compLieHom M (colorRep L hL)
    colorCasimir L u =
      (-1 / 2 : ℂ) • TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f M u := by
  let _ : LieRingModule G M := LieRingModule.compLieHom M (colorRep L hL)
  let _ : LieModule ℂ G M := LieModule.compLieHom M (colorRep L hL)
  have hact (a : Fin 3) (v : M) : ⁅MatrixSL2.color a, v⁆ = L a v := by
    change colorRep L hL (MatrixSL2.color a) v = L a v
    rw [colorRep_color]
  rw [← color_sum_lie_lie]
  simp only [colorCasimir, LinearMap.sum_apply, Module.End.mul_apply, hact]

/-- **Kernel and range of the colour Casimir are complementary.** -/
theorem casimir_isCompl [FiniteDimensional ℂ M] :
    IsCompl (LinearMap.ker (colorCasimir L)) (LinearMap.range (colorCasimir L)) := by
  let _ : LieRingModule G M := LieRingModule.compLieHom M (colorRep L hL)
  let _ : LieModule ℂ G M := LieModule.compLieHom M (colorRep L hL)
  have h := casimir_affine_isCompl_ker_range M 0 (-1 / 2 : ℂ)
  have heq : colorCasimir L = (0 : ℂ) • (LinearMap.id : Module.End ℂ M) +
      (-1 / 2 : ℂ) • TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f M := by
    apply LinearMap.ext
    intro u
    rw [colorCasimir_eq L hL u]
    simp
  rw [heq]
  exact h

/-- **The kernel of the colour Casimir consists of invariants.** -/
theorem casimir_ker [FiniteDimensional ℂ M] {v : M} (hv : colorCasimir L v = 0) (a : Fin 3) :
    L a v = 0 := by
  let _ : LieRingModule G M := LieRingModule.compLieHom M (colorRep L hL)
  let _ : LieModule ℂ G M := LieModule.compLieHom M (colorRep L hL)
  have hact (b : Fin 3) (w : M) : ⁅MatrixSL2.color b, w⁆ = L b w := by
    change colorRep L hL (MatrixSL2.color b) w = L b w
    rw [colorRep_color]
  have hcas : TauCeti.sl2CasimirHom rootSl2Triple rootSl2Triple_top M v = 0 := by
    rw [colorCasimir_eq L hL v] at hv
    rw [TauCeti.sl2CasimirHom_apply]
    exact (smul_eq_zero.mp hv).resolve_left (by norm_num)
  set K := (TauCeti.sl2CasimirHom rootSl2Triple rootSl2Triple_top M).ker
  have : ComplementedLattice (LieSubmodule ℂ G K) := ⟨TauCeti.exists_isCompl_sl_fin_two⟩
  obtain ⟨k, N, hint, hirr⟩ := TauCeti.exists_isInternal_isIrreducible ℂ G K
  -- every irreducible summand has trivial action
  have htriv (i : Fin k) (x : G) (w : N i) : ⁅x, w⁆ = 0 := by
    by_contra hne
    have hinj := TauCeti.sl2Casimir_injective (K := ℂ) (M := N i) (t := rootSl2Triple)
      rootSl2Triple_top ⟨x, w, hne⟩
    have hzero : ∀ z : N i, TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f (N i) z = 0 := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      rw [TauCeti.coe_sl2Casimir_lieSubmodule, TauCeti.coe_sl2Casimir_lieSubmodule]
      have hz := (z : K).property
      rw [LieModuleHom.mem_ker, TauCeti.sl2CasimirHom_apply] at hz
      simpa using hz
    apply hne
    have hw : w = 0 := hinj ((hzero w).trans (hzero 0).symm)
    rw [hw, lie_zero]
  -- hence every element of `K` is invariant
  have hK : ∀ (x : G) (w : K), ⁅x, w⁆ = 0 := by
    intro x w
    have hw : w ∈ ⨆ i, (N i).toSubmodule := by
      rw [hint.submodule_iSup_eq_top]; trivial
    exact Submodule.iSup_induction (fun i => (N i).toSubmodule) (motive := fun z => ⁅x, z⁆ = 0)
      hw (fun i z hz => congrArg Subtype.val (htriv i x ⟨z, hz⟩)) (lie_zero x)
      (fun z₁ z₂ h₁ h₂ => by rw [lie_add, h₁, h₂, add_zero])
  have := hK (MatrixSL2.color a) ⟨v, hcas⟩
  have h2 := congrArg Subtype.val this
  simp only [LieSubmodule.coe_bracket] at h2
  rwa [hact] at h2

end Lie

/-! ## Restriction to a stable subspace -/

/-- The restriction of three operators to a stable subspace. -/
def restrictL (L : Fin 3 → Module.End ℂ M) (W : Submodule ℂ M) (hW : ∀ a, ∀ v ∈ W, L a v ∈ W) :
    Fin 3 → Module.End ℂ W := fun a => (L a).restrict (hW a)

theorem IsColorAction.restrict {L : Fin 3 → Module.End ℂ M} (hL : IsColorAction L)
    (W : Submodule ℂ M) (hW : ∀ a, ∀ v ∈ W, L a v ∈ W) : IsColorAction (restrictL L W hW) := by
  intro a b
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have := LinearMap.congr_fun (hL a b) (v : M)
  simpa [restrictL, Module.End.mul_apply, LinearMap.restrict_apply] using this

theorem colorCasimir_restrict (L : Fin 3 → Module.End ℂ M) (W : Submodule ℂ M)
    (hW : ∀ a, ∀ v ∈ W, L a v ∈ W) (v : W) :
    (colorCasimir (restrictL L W hW) v : M) = colorCasimir L v := by
  simp [colorCasimir, restrictL, Module.End.mul_apply, LinearMap.restrict_apply]

end KhanSL2.Deformation
