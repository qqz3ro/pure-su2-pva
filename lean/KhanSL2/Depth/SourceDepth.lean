module

public import KhanSL2.Depth.SourceModules

@[expose] public section

/-!
# Depth of the source modules (paper Lemma 7.2, blueprint `lem:sourcedepth`)

For `B = r + 3s`, multiplication by `F_{r,s}` after the coordinate map `Φ` is an `R_B`-linear
isomorphism from the coefficient coordinates of `(A, W)` onto `J_{r,s}` (`srcEquivJ`). The
depth bound of `SourceCoords` therefore applies to `J_{r,s}`:
`depth_{P_B} J_{r,s} ≥ r + s - 1` for `s ≥ 1` (`depth_J_ge`), and hence
`depth_{P_B} J_{B,p} ≥ p` for `0 < p < B` (`depth_JB_ge`).
-/

noncomputable section

open MvPolynomial

namespace KhanSL2.Depth

variable (r s : ℕ)

/-- The coefficient coordinates as an `R_B`-module through `ν` (`B = r + 3s`). -/
def CoordMod (r s : ℕ) : Type := Src r s

instance : CommRing (CoordMod r s) := inferInstanceAs (CommRing (Src r s))

instance : Algebra (RB (r + 3 * s)) (CoordMod r s) := (nu r s).toRingHom.toAlgebra

theorem CoordMod.smul_def (c : RB (r + 3 * s)) (f : CoordMod r s) :
    c • f = (nu r s c : Src r s) * (show Src r s from f) := rfl

/-- `f ↦ F_{r,s} · Φ(f)`. -/
def toJ : CoordMod r s →ₗ[RB (r + 3 * s)] J (r + 3 * s) r s where
  toFun f := ⟨(Fpoly r s * coordToRoots r s f : ZW r s),
    ⟨coordToRoots r s f, (mem_symmBoth_iff_coordToRoots r s _).mpr ⟨f, rfl⟩, rfl⟩⟩
  map_add' f g := Subtype.ext (by
    change Fpoly r s * coordToRoots r s ((show Src r s from f) + (show Src r s from g)) =
      Fpoly r s * coordToRoots r s f + Fpoly r s * coordToRoots r s g
    rw [map_add, mul_add])
  map_smul' c f := Subtype.ext (by
    change Fpoly r s * coordToRoots r s ((nu r s c : Src r s) * (show Src r s from f)) =
      (nuStar (r + 3 * s) r s c : ZW r s) * (Fpoly r s * coordToRoots r s f)
    rw [map_mul, ← AlgHom.comp_apply, coordToRoots_comp_nu]
    ring)

theorem toJ_bijective : Function.Bijective (toJ r s) := by
  constructor
  · intro f g h
    exact coordToRoots_injective r s
      (mul_left_cancel₀ (Fpoly_ne_zero r s) (congrArg Subtype.val h))
  · rintro ⟨_, g, hg, hfg⟩
    obtain ⟨f, rfl⟩ := (mem_symmBoth_iff_coordToRoots r s g).mp hg
    exact ⟨f, Subtype.ext hfg.symm⟩

/-- **`J_{r,s}` is the coefficient-coordinate module** (`B = r + 3s`). -/
def srcEquivJ : CoordMod r s ≃ₗ[RB (r + 3 * s)] J (r + 3 * s) r s :=
  LinearEquiv.ofBijective (toJ r s) (toJ_bijective r s)

/-- **`J_{r,s}` is finite over `R_B`** (blueprint `lem:Jfinite`). -/
theorem J_finite : Module.Finite (RB (r + 3 * s)) (J (r + 3 * s) r s) :=
  have : Module.Finite (RB (r + 3 * s)) (CoordMod r s) :=
    @finite_nu r s (inferInstance : Algebra (RB (r + 3 * s)) (CoordMod r s)) rfl
  Module.Finite.equiv (srcEquivJ r s)

/-- **Depth of `J_{r,s}`**: for `B = r + 3s` with `s ≥ 1`, `depth_{P_B} J_{r,s} ≥ r + s - 1`. -/
theorem depth_J_ge (B r s : ℕ) (hB : B = r + 3 * s) (hs : 1 ≤ s) :
    ((r + s - 1 : ℕ) : ℕ∞) ≤ (collisionIdeal B).depth (ModuleCat.of (RB B) (J B r s)) := by
  subst hB
  rw [← Ideal.depth_eq_of_linearEquiv _ (srcEquivJ r s)]
  exact @depth_coord_ge r s hs (inferInstance : Algebra (RB (r + 3 * s)) (CoordMod r s)) rfl

/-- **Depth of the source modules (paper Lemma 7.2)**: for `0 < p < B`,
`depth_{P_B} J_{B,p} ≥ p`. -/
theorem depth_JB_ge (B p : ℕ) (_hp : 0 < p) (hpB : p < B) :
    (p : ℕ∞) ≤ (collisionIdeal B).depth (ModuleCat.of (RB B) (JB B p)) := by
  by_cases h : p ≤ B ∧ 3 ∣ B - p
  · have hJB : JB B p = J B p ((B - p) / 3) := if_pos h
    rw [hJB]
    obtain ⟨_, k, hk⟩ := h
    have hs : 1 ≤ (B - p) / 3 := by omega
    refine le_trans ?_ (depth_J_ge B p ((B - p) / 3) (by omega) hs)
    exact_mod_cast (by omega : p ≤ p + (B - p) / 3 - 1)
  · have hJB : JB B p = ⊥ := if_neg h
    rw [hJB]
    have : Subsingleton (⊥ : Submodule (RB B) (RootsMod B p ((B - p) / 3))) :=
      Submodule.subsingleton_iff_eq_bot.mpr rfl
    rw [depth_eq_top_of_subsingleton]
    exact le_top

end KhanSL2.Depth
