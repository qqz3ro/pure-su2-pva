module

public import KhanSL2.Chains.Grading

@[expose] public section

/-!
# The relative CE complex as a quotient complex

The relative chains of the pair `(𝔩, 𝔤) = (𝔤 ⋉ 𝔩₊, 𝔤)` with coefficients in `Λ(ε𝔩)` are the
`𝔤`-coinvariants `RelChains = (Λ𝔩₊ ⊗ Λ(ε𝔩)) ⧸ 𝔤·(Λ𝔩₊ ⊗ Λ(ε𝔩))`. The 𝔤-relations form a
subcomplex, so the CE boundary descends to `relBoundary` with `relBoundary² = 0`, and the
trigrading descends to `relPiece d`.

`RelHomology d` was defined by lifting cycles and boundaries to the chains. Here we show it
is the homology `ker ∂̄ / im ∂̄` of the quotient complex in degree `d`
(`relHomologyEquivComplex`).
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.Current

open LieChains

set_option maxHeartbeats 1000000

/-! ## The boundary preserves relations and lowers the degree -/

theorem boundary_relTheta (a : Fin 3) (ξ : GenChains) :
    LieChains.boundary NB (relTheta a ξ) = relTheta a (LieChains.boundary NB ξ) :=
  boundary_lieDeriv (relTheta_compatible a) ξ

theorem genRelations_le_comap_boundary :
    genRelations ≤ genRelations.comap (LieChains.boundary NB) := by
  apply iSup_le
  rintro a _ ⟨η, rfl⟩
  change LieChains.boundary NB (relTheta a η) ∈ genRelations
  rw [boundary_relTheta]
  exact Submodule.mem_iSup_of_mem a ⟨_, rfl⟩

theorem boundary_mem_genPiece {d : Degree} {ξ : GenChains} (hξ : ξ ∈ genPiece (d + (1, 0, 0))) :
    LieChains.boundary NB ξ ∈ genPiece d := by
  change Phi (LieChains.boundary NB ξ) ∈ cochainPiece d
  rw [Phi_boundary]
  have h := boundary_degree (d := d + (1, 0, 0)) hξ
  rwa [add_sub_cancel_right] at h

/-! ## The quotient complex -/

/-- The relative chains `C(𝔩, 𝔤; Λ(ε𝔩))`: `𝔤`-coinvariants of `Λ𝔩₊ ⊗ Λ(ε𝔩)`. -/
abbrev RelChains : Type := GenChains ⧸ genRelations

/-- The relative CE boundary, induced on coinvariants. -/
def relBoundary : RelChains →ₗ[ℂ] RelChains :=
  genRelations.mapQ genRelations (LieChains.boundary NB) genRelations_le_comap_boundary

theorem relBoundary_mk (ξ : GenChains) :
    relBoundary (genRelations.mkQ ξ) = genRelations.mkQ (LieChains.boundary NB ξ) := rfl

theorem relBoundary_relBoundary (x : RelChains) : relBoundary (relBoundary x) = 0 := by
  obtain ⟨ξ, rfl⟩ := genRelations.mkQ_surjective x
  change genRelations.mkQ (LieChains.boundary NB (LieChains.boundary NB ξ)) = 0
  rw [LieChains.boundary_boundary]
  exact LinearMap.map_zero _

/-- The degree-`d` relative chains. -/
def relPiece (d : Degree) : Submodule ℂ RelChains := (genPiece d).map genRelations.mkQ

/-- Cycles of the relative complex. -/
def relCycles (d : Degree) : Submodule ℂ RelChains := relPiece d ⊓ LinearMap.ker relBoundary

/-- Boundaries of the relative complex. -/
def relBoundaries (d : Degree) : Submodule ℂ RelChains :=
  (relPiece (d + (1, 0, 0))).map relBoundary

theorem relBoundaries_le_relCycles (d : Degree) : relBoundaries d ≤ relCycles d := by
  rintro _ ⟨_, ⟨η, hη, rfl⟩, rfl⟩
  refine ⟨⟨LieChains.boundary NB η, boundary_mem_genPiece hη, ?_⟩, ?_⟩
  · rw [relBoundary_mk]
  · change relBoundary (relBoundary _) = 0
    rw [relBoundary_relBoundary]

instance (d : Degree) : HasQuotient (relCycles d) (Submodule ℂ (relCycles d)) :=
  Submodule.hasQuotient (M := relCycles d)

/-- Homology of the relative complex in degree `d`: `ker ∂̄ / im ∂̄`. -/
abbrev RelComplexHomology (d : Degree) : Type :=
  ↥(relCycles d) ⧸ (relBoundaries d).comap (relCycles d).subtype

instance (d : Degree) : AddCommGroup (RelComplexHomology d) :=
  Submodule.Quotient.addCommGroup (M := relCycles d) _

instance (d : Degree) : Module ℂ (RelComplexHomology d) :=
  Submodule.Quotient.module (M := relCycles d) _

/-! ## Comparison with the lifted description -/

theorem mk_mem_relCycles {d : Degree} (ξ : genCycles d) :
    genRelations.mkQ (ξ : GenChains) ∈ relCycles d := by
  obtain ⟨hp, hr⟩ := ξ.property
  refine ⟨⟨_, hp, rfl⟩, ?_⟩
  change genRelations.mkQ (LieChains.boundary NB (ξ : GenChains)) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hr

/-- Lifted cycles to cycles of the quotient complex. -/
def cyclesToRel (d : Degree) : genCycles d →ₗ[ℂ] relCycles d :=
  LinearMap.codRestrict (relCycles d) (genRelations.mkQ ∘ₗ (genCycles d).subtype)
    mk_mem_relCycles

theorem cyclesToRel_surjective (d : Degree) : Function.Surjective (cyclesToRel d) := by
  rintro ⟨x, ⟨ξ, hξ, rfl⟩, hx⟩
  refine ⟨⟨ξ, hξ, ?_⟩, rfl⟩
  change genRelations.mkQ (LieChains.boundary NB ξ) = 0 at hx
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  exact hx

/-- Lifted cycles to homology of the quotient complex. -/
def cyclesToRelHomology (d : Degree) : genCycles d →ₗ[ℂ] RelComplexHomology d :=
  Submodule.mkQ (M := relCycles d) _ ∘ₗ cyclesToRel d

theorem cyclesToRelHomology_surjective (d : Degree) :
    Function.Surjective (cyclesToRelHomology d) :=
  (Submodule.mkQ_surjective (M := relCycles d) _).comp (cyclesToRel_surjective d)

theorem ker_cyclesToRelHomology (d : Degree) :
    LinearMap.ker (cyclesToRelHomology d) = (genBounds d).comap (genCycles d).subtype := by
  ext ξ
  have h1 : ξ ∈ LinearMap.ker (cyclesToRelHomology d) ↔
      cyclesToRel d ξ ∈ (relBoundaries d).comap (relCycles d).subtype := by
    rw [LinearMap.mem_ker]
    exact Submodule.Quotient.mk_eq_zero _
  rw [h1]
  change genRelations.mkQ (ξ : GenChains) ∈ relBoundaries d ↔ (ξ : GenChains) ∈ genBounds d
  constructor
  · rintro ⟨_, ⟨η, hη, rfl⟩, hx⟩
    change (Submodule.Quotient.mk (LieChains.boundary NB η) : RelChains) =
      Submodule.Quotient.mk (ξ : GenChains) at hx
    rw [Submodule.Quotient.eq] at hx
    have hr : (ξ : GenChains) - LieChains.boundary NB η ∈ genRelations ⊓ genPiece d :=
      ⟨by
          change (ξ : GenChains) - LieChains.boundary NB η ∈ genRelations
          rw [← neg_mem_iff, neg_sub]; exact hx,
        Submodule.sub_mem _ ξ.property.1 (boundary_mem_genPiece hη)⟩
    have hsum : (ξ : GenChains) =
        ((ξ : GenChains) - LieChains.boundary NB η) + LieChains.boundary NB η := by abel
    rw [genBounds, hsum]
    exact Submodule.add_mem_sup hr ⟨η, hη, rfl⟩
  · intro hξ
    obtain ⟨r, hr, b, ⟨η, hη, rfl⟩, hrb⟩ := Submodule.mem_sup.mp hξ
    refine ⟨genRelations.mkQ η, ⟨η, hη, rfl⟩, ?_⟩
    change (Submodule.Quotient.mk (LieChains.boundary NB η) : RelChains) =
      Submodule.Quotient.mk (ξ : GenChains)
    rw [Submodule.Quotient.eq, ← hrb, sub_add_cancel_right, neg_mem_iff]
    exact hr.1

/-- **`RelHomology d` is the homology of the relative CE complex** `(RelChains, ∂̄)` in degree `d`. -/
def relHomologyEquivComplex (d : Degree) : RelHomology d ≃ₗ[ℂ] RelComplexHomology d :=
  (Submodule.quotEquivOfEq _ _ (ker_cyclesToRelHomology d).symm).trans
    ((cyclesToRelHomology d).quotKerEquivOfSurjective (cyclesToRelHomology_surjective d))

instance (d : Degree) : FiniteDimensional ℂ (RelComplexHomology d) :=
  LinearEquiv.finiteDimensional (relHomologyEquivComplex d)

end KhanSL2.Current
