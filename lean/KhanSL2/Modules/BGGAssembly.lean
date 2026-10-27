module

public import KhanSL2.Modules.GradedAssembly
public import KhanSL2.BGGBridgeStatement

@[expose] public section

/-!
# Assembly of the BGG comparison over spin

The direct sum of the already proved coefficient-homology comparisons
identifies `KTotal B p` with the algebraic sum of the actual BGG homology
pieces. This is a complex-linear equivalence and preserves every spin
component.
-/

noncomputable section
open scoped DirectSum

namespace KhanSL2.Modules

/-- The actual BGG coefficient homology, assembled over spin. -/
abbrev BGGHomologyTotal (B p : ℕ) := ⨁ S : ℤ, BGGBridge.BGGHomology p B S

/-- Assemble the specified M2-to-BGG homology equivalences over spin. -/
def kTotalEquivBGG (B p : ℕ) : KTotal B p ≃ₗ[ℂ] BGGHomologyTotal B p :=
  DirectSum.congrLinearEquiv (fun S : ℤ => Current.kEquivBGGHomology p B S)

/-- Each component of the assembled equivalence is the actual bridge map. -/
@[simp] theorem kTotalEquivBGG_apply (B p : ℕ) (x : KTotal B p) (S : ℤ) :
    kTotalEquivBGG B p x S = Current.kEquivBGGHomology p B S (x S) := rfl

/-- The inverse is assembled from the inverses of the same bridge maps. -/
@[simp] theorem kTotalEquivBGG_symm_apply (B p : ℕ)
    (x : BGGHomologyTotal B p) (S : ℤ) :
    (kTotalEquivBGG B p).symm x S = (Current.kEquivBGGHomology p B S).symm (x S) := rfl

/-- Homogeneous inclusions commute with the assembled bridge. -/
@[simp] theorem kTotalEquivBGG_lof (B p : ℕ) (S : ℤ) (x : Current.K p B S) :
    kTotalEquivBGG B p (DirectSum.lof ℂ ℤ (fun T => Current.K p B T) S x) =
      DirectSum.lof ℂ ℤ (fun T => BGGBridge.BGGHomology p B T)
        S (Current.kEquivBGGHomology p B S x) :=
  DirectSum.lmap_lof
    (fun T : ℤ => (Current.kEquivBGGHomology p B T).toLinearMap) S x

/-- Component projections intertwine the assembled and homogeneous comparisons. -/
theorem kTotalEquivBGG_component (B p : ℕ) (S : ℤ) :
    (DirectSum.component ℂ ℤ (fun T => BGGBridge.BGGHomology p B T) S).comp
        (kTotalEquivBGG B p).toLinearMap =
      (Current.kEquivBGGHomology p B S).toLinearMap.comp
        (DirectSum.component ℂ ℤ (fun T => Current.K p B T) S) := rfl

end KhanSL2.Modules
