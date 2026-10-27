module

public import KhanSL2.Chains.Psi
public import KhanSL2.Chains.Comparison.Boundary
public import KhanSL2.Chains.Comparison.Bijective

@[expose] public section

/-!
# Relative Lie algebra homology `H_p(𝔩, 𝔤; Λ^B(ε𝔩))` and the dictionary

The relative chains of the split pair `(𝔩, 𝔤) = (𝔤 ⋉ 𝔩₊, 𝔤)` with coefficients in
`Λ(ε𝔩)` are the `𝔤`-coinvariants of the CE chains `Λ𝔩₊ ⊗ Λ(ε𝔩)`. Here they are built
from the general `LieChains` construction. Their degree pieces are transported along
the comparison isomorphism `PhiEquiv`, which sends the bidegree `(p, B)` and spin `S`
part to the monomials of degree `(B + p, B, S)`.

Main results:
* `relHomologyEquiv d : RelHomology d ≃ₗ[ℂ] ChainHomology d`;
* `cohomologyPieceEquivDualRel d : cohomologyPiece d ≃ₗ[ℂ] Dual (RelHomology d)`;
* `psiRel_surjective d`.
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.Current

open LieChains

/-- Relations defining `𝔤`-coinvariants of the general chains. -/
def genRelations : Submodule ℂ GenChains := ⨆ a : Fin 3, LinearMap.range (relTheta a)

/-- The degree-`d` piece of the general chains. -/
def genPiece (d : Degree) : Submodule ℂ GenChains := (cochainPiece d).comap Phi

/-- Relative cycles of degree `d`: boundary vanishing in coinvariants. -/
def genCycles (d : Degree) : Submodule ℂ GenChains :=
  genPiece d ⊓ genRelations.comap (LieChains.boundary NB)

/-- Relative boundaries of degree `d`. -/
def genBounds (d : Degree) : Submodule ℂ GenChains :=
  (genRelations ⊓ genPiece d) ⊔ (genPiece (d + (1, 0, 0))).map (LieChains.boundary NB)

instance (d : Degree) : HasQuotient (genCycles d) (Submodule ℂ (genCycles d)) :=
  Submodule.hasQuotient (M := genCycles d)

/-- **Relative CE homology** `H(𝔩, 𝔤; Λ(ε𝔩))` in degree `d`. -/
abbrev RelHomology (d : Degree) : Type :=
  ↥(genCycles d) ⧸ (genBounds d).comap (genCycles d).subtype

instance (d : Degree) : AddCommGroup (RelHomology d) :=
  Submodule.Quotient.addCommGroup (M := genCycles d) _

instance (d : Degree) : Module ℂ (RelHomology d) :=
  Submodule.Quotient.module (M := genCycles d) _

/-! ## Transport along `PhiEquiv` -/

theorem Phi_surjective : Function.Surjective Phi := Phi_bijective.2

theorem Phi_injective : Function.Injective Phi := Phi_bijective.1

theorem map_genRelations : genRelations.map Phi = relations := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply iSup_le
    rintro a _ ⟨η, rfl⟩
    change Phi (relTheta a η) ∈ relations
    rw [Phi_relTheta]
    exact Submodule.neg_mem _ (Submodule.mem_iSup_of_mem a ⟨_, rfl⟩)
  · apply iSup_le
    rintro a _ ⟨ζ, rfl⟩
    obtain ⟨η, rfl⟩ := Phi_surjective ζ
    refine ⟨relTheta a (-η), Submodule.mem_iSup_of_mem a ⟨_, rfl⟩, ?_⟩
    rw [map_neg, map_neg, Phi_relTheta, neg_neg]

theorem genRelations_eq : genRelations = relations.comap Phi := by
  rw [← map_genRelations, Submodule.comap_map_eq_of_injective Phi_injective]

theorem genCycles_eq (d : Degree) : genCycles d = (cycles d).comap Phi := by
  ext ξ
  simp only [genCycles, cycles, genPiece, genRelations_eq, Submodule.mem_inf,
    Submodule.mem_comap, Phi_boundary]

set_option maxHeartbeats 4000000 in
theorem genBounds_eq (d : Degree) : genBounds d = (bounds d).comap Phi := by
  ext ξ
  simp only [genBounds, bounds, Submodule.mem_comap]
  constructor
  · intro hξ
    obtain ⟨r, hr, b, hb, rfl⟩ := Submodule.mem_sup.mp hξ
    obtain ⟨η, hη, rfl⟩ := hb
    rw [map_add, Phi_boundary]
    refine Submodule.add_mem_sup ?_ ⟨Phi η, hη, rfl⟩
    rw [genRelations_eq] at hr
    exact hr
  · intro hξ
    obtain ⟨r, hr, b, hb, hrb⟩ := Submodule.mem_sup.mp hξ
    obtain ⟨η', hη', hbη⟩ := hb
    have hPr : Phi (PhiEquiv.symm r) = r := by
      rw [← PhiEquiv_apply, LinearEquiv.apply_symm_apply]
    have hPη : Phi (PhiEquiv.symm η') = η' := by
      rw [← PhiEquiv_apply, LinearEquiv.apply_symm_apply]
    have hξeq : ξ = PhiEquiv.symm r + LieChains.boundary NB (PhiEquiv.symm η') := by
      apply Phi_injective
      rw [map_add, Phi_boundary, hPr, hPη, hbη, hrb]
    rw [hξeq]
    refine Submodule.add_mem_sup ⟨?_, ?_⟩ ⟨PhiEquiv.symm η', ?_, rfl⟩
    · rw [genRelations_eq]
      change Phi (PhiEquiv.symm r) ∈ relations
      rw [hPr]; exact hr.1
    · change Phi (PhiEquiv.symm r) ∈ cochainPiece d
      rw [hPr]; exact hr.2
    · change Phi (PhiEquiv.symm η') ∈ cochainPiece (d + (1, 0, 0))
      rw [hPη]; exact hη'

theorem mem_genCycles_iff {d : Degree} {ξ : GenChains} : ξ ∈ genCycles d ↔ Phi ξ ∈ cycles d := by
  rw [genCycles_eq]; rfl

theorem mem_genBounds_iff {d : Degree} {ξ : GenChains} : ξ ∈ genBounds d ↔ Phi ξ ∈ bounds d := by
  rw [genBounds_eq]; rfl

/-- Relative cycles correspond to coinvariant cycles. -/
def cyclesEquiv (d : Degree) : genCycles d ≃ₗ[ℂ] cycles d where
  toFun ξ := ⟨Phi (ξ : GenChains), mem_genCycles_iff.mp ξ.property⟩
  invFun ζ := ⟨PhiEquiv.symm ζ, by
    rw [mem_genCycles_iff, ← PhiEquiv_apply, LinearEquiv.apply_symm_apply]
    exact ζ.property⟩
  map_add' ξ η := Subtype.ext (map_add Phi (ξ : GenChains) η)
  map_smul' c ξ := Subtype.ext (map_smul Phi c (ξ : GenChains))
  left_inv ξ := Subtype.ext (by
    change PhiEquiv.symm (Phi (ξ : GenChains)) = ξ
    rw [← PhiEquiv_apply, LinearEquiv.symm_apply_apply])
  right_inv ζ := Subtype.ext (by
    change Phi (PhiEquiv.symm ζ) = ζ
    rw [← PhiEquiv_apply, LinearEquiv.apply_symm_apply])

theorem cyclesEquiv_coe (d : Degree) (ξ : genCycles d) :
    (cyclesEquiv d ξ : Chain) = Phi (ξ : GenChains) := rfl

theorem map_cyclesEquiv_bounds (d : Degree) :
    ((genBounds d).comap (genCycles d).subtype).map (cyclesEquiv d : genCycles d →ₗ[ℂ] cycles d) =
      (bounds d).comap (cycles d).subtype := by
  ext ζ
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    exact mem_genBounds_iff.mp hξ
  · intro hζ
    refine ⟨(cyclesEquiv d).symm ζ, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [mem_genBounds_iff, ← cyclesEquiv_coe, LinearEquiv.apply_symm_apply]
    exact hζ

/-- **Relative CE homology equals the homology of coinvariant chains.** -/
def relHomologyEquiv (d : Degree) : RelHomology d ≃ₗ[ℂ] ChainHomology d :=
  Submodule.Quotient.equiv _ _ (cyclesEquiv d) (map_cyclesEquiv_bounds d)

instance (d : Degree) : FiniteDimensional ℂ (RelHomology d) :=
  LinearEquiv.finiteDimensional (relHomologyEquiv d).symm

/-- **The dictionary**, for relative Lie algebra homology. -/
def cohomologyPieceEquivDualRel (d : Degree) :
    cohomologyPiece d ≃ₗ[ℂ] Module.Dual ℂ (RelHomology d) :=
  (cohomologyPieceEquivDual d).trans (relHomologyEquiv d).dualMap

/-- `ψ_d` on relative homology. -/
def psiRel (d : Degree) : RelHomology d →ₗ[ℂ] Module.Dual ℂ (Source.piece d) :=
  psi d ∘ₗ (relHomologyEquiv d).toLinearMap

theorem psiRel_surjective (d : Degree) : Function.Surjective (psiRel d) :=
  (psi_surjective d).comp (relHomologyEquiv d).surjective

end KhanSL2.Current
