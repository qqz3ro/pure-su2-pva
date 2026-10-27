module

public import KhanSL2.Chains.Dictionary
public import KhanSL2.Injectivity
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-!
# The transpose of `φ` on coinvariant chain homology

Through the dictionary, the canonical map `φ` has a transpose
`ψ : H_d(coinvariant chains) → (A_d)^*` in every degree `d`. Injectivity of `φ`
makes every `ψ` surjective.
-/

noncomputable section

namespace KhanSL2

/-- The canonical map on a single degree piece. -/
def phiPiece (d : Degree) : Source.piece d →ₗ[ℂ] cohomologyPiece d :=
  (phi ∘ₗ (Source.piece d).subtype).codRestrict (cohomologyPiece d)
    (fun a => phi_degree a.property)

@[simp] theorem phiPiece_coe (d : Degree) (a : Source.piece d) :
    (phiPiece d a : Cohomology) = phi a := rfl

theorem phiPiece_injective (d : Degree) : Function.Injective (phiPiece d) := by
  intro a b h
  apply Subtype.ext
  apply phi_injective
  simpa using congrArg Subtype.val h

/-- `ψ_d`: the transpose of `φ` in degree `d`, read through the dictionary. -/
def psi (d : Degree) : ChainHomology d →ₗ[ℂ] Module.Dual ℂ (Source.piece d) :=
  ((cohomologyPieceEquivDual d).toLinearMap ∘ₗ phiPiece d).dualMap ∘ₗ
    (Module.evalEquiv ℂ (ChainHomology d)).toLinearMap

/-- `ψ` evaluates the pairing of a chain-homology class with the image of a source element. -/
theorem psi_apply (d : Degree) (k : ChainHomology d) (a : Source.piece d) :
    psi d k a = cohomologyToDual d (phi a) k := rfl

/-- **Every `ψ_d` is surjective.** This is `phi_injective` read through the dictionary. -/
theorem psi_surjective (d : Degree) : Function.Surjective (psi d) := by
  have hinj : Function.Injective
      ((cohomologyPieceEquivDual d).toLinearMap ∘ₗ phiPiece d) :=
    (cohomologyPieceEquivDual d).injective.comp (phiPiece_injective d)
  exact (LinearMap.dualMap_surjective_of_injective hinj).comp
    (Module.evalEquiv ℂ (ChainHomology d)).surjective

end KhanSL2
