module

public import KhanSL2.Chains.Coinvariant
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

/-!
# The duality dictionary

For every degree `d`, the coefficient pairing identifies the degree-`d` piece of
the restricted relative cohomology with the dual of the degree-`d` homology of
coinvariant chains. The proof is elementary linear algebra on the finite
graded pieces: invariance and closedness are orthogonality to relations and
boundaries, and exactness comes from extending functionals.
-/

noncomputable section

namespace KhanSL2

/-- Over a field, a functional killing the kernel of a linear map factors through it. -/
theorem exists_functional_comp_eq {V X : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup X] [Module ℂ X] (T : V →ₗ[ℂ] X) (ℓ : V →ₗ[ℂ] ℂ)
    (h : LinearMap.ker T ≤ LinearMap.ker ℓ) : ∃ g : X →ₗ[ℂ] ℂ, g ∘ₗ T = ℓ := by
  let ℓbar : (V ⧸ LinearMap.ker T) →ₗ[ℂ] ℂ := (LinearMap.ker T).liftQ ℓ h
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (ℓbar ∘ₗ T.quotKerEquivRange.symm.toLinearMap)
  refine ⟨g, LinearMap.ext fun v => ?_⟩
  have := congrArg (fun F => F ⟨T v, LinearMap.mem_range_self T v⟩) hg
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image] at this
  rw [LinearMap.comp_apply, this]
  rfl

/-! ## The pairing descends -/

theorem pairing_cycle_bounds (d : Degree) (u : CycleSpace) {ζ : Chain} (hζ : ζ ∈ bounds d) :
    pairing (u : Cochain) ζ = 0 := by
  obtain ⟨r, hr, b, hb, rfl⟩ := Submodule.mem_sup.mp hζ
  obtain ⟨ξ, _, rfl⟩ := hb
  rw [map_add, pairing_relations_eq_zero u.property.1 hr.1, ← pairing_q,
    LinearMap.mem_ker.mp u.property.2]
  simp

/-- A relative cycle, as a functional on degree-`d` coinvariant homology. -/
def cycleFunctional (d : Degree) (u : CycleSpace) : Module.Dual ℂ (ChainHomology d) :=
  ((bounds d).comap (cycles d).subtype).liftQ
    ((pairing (u : Cochain)) ∘ₗ (cycles d).subtype)
    (fun _ hζ => pairing_cycle_bounds d u hζ)

@[simp] theorem cycleFunctional_mk (d : Degree) (u : CycleSpace) (ζ : cycles d) :
    cycleFunctional d u (Submodule.Quotient.mk ζ) = pairing (u : Cochain) ζ := rfl

def cycleToDual (d : Degree) : CycleSpace →ₗ[ℂ] Module.Dual ℂ (ChainHomology d) where
  toFun := cycleFunctional d
  map_add' u v := by
    ext ζ
    simp
  map_smul' r u := by
    ext ζ
    simp

@[simp] theorem cycleToDual_apply (d : Degree) (u : CycleSpace) :
    cycleToDual d u = cycleFunctional d u := rfl

theorem cycleToDual_boundaries (d : Degree) :
    relativeBoundaries ≤ LinearMap.ker (cycleToDual d) := by
  intro v hv
  rw [LinearMap.mem_ker]
  change (v : Cochain) ∈ relativeInvariants.map q at hv
  obtain ⟨w, hw, hq⟩ := hv
  ext ζ
  change pairing (v : Cochain) ζ = 0
  rw [← hq, pairing_q]
  exact pairing_relations_eq_zero hw ζ.property.2

/-- The pairing between cohomology and degree-`d` coinvariant homology. -/
def cohomologyToDual (d : Degree) : Cohomology →ₗ[ℂ] Module.Dual ℂ (ChainHomology d) :=
  relativeBoundaries.liftQ (cycleToDual d) (cycleToDual_boundaries d)

@[simp] theorem cohomologyToDual_classOf (d : Degree) (u : Cochain) (hu : u ∈ relativeCycles)
    (ζ : cycles d) :
    cohomologyToDual d (classOf u hu) (Submodule.Quotient.mk ζ) = pairing u ζ := rfl

/-- The dictionary map on the degree-`d` piece. -/
def dictionaryMap (d : Degree) : cohomologyPiece d →ₗ[ℂ] Module.Dual ℂ (ChainHomology d) :=
  cohomologyToDual d ∘ₗ (cohomologyPiece d).subtype

/-! ## Bijectivity -/

theorem dictionaryMap_injective (d : Degree) : Function.Injective (dictionaryMap d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨h, hh⟩ hzero
  obtain ⟨u, hud, rfl⟩ := hh
  -- `u` is a relative cycle of degree `d` orthogonal to all coinvariant cycles.
  have horth : ∀ ζ ∈ cycles d, pairing (u : Cochain) ζ = 0 := by
    intro ζ hζ
    have := congrArg (fun F : Module.Dual ℂ (ChainHomology d) =>
      F (Submodule.Quotient.mk ⟨ζ, hζ⟩)) hzero
    simpa [dictionaryMap, cohomologyToDual] using this
  -- Factor the pairing with `u` through the boundary into coinvariants.
  let P := cochainPiece d
  let T : P →ₗ[ℂ] Chain ⧸ relations := relations.mkQ ∘ₗ boundary ∘ₗ P.subtype
  let ℓ : P →ₗ[ℂ] ℂ := pairing (u : Cochain) ∘ₗ P.subtype
  have hker : LinearMap.ker T ≤ LinearMap.ker ℓ := by
    intro ζ hζ
    rw [LinearMap.mem_ker] at hζ ⊢
    have hrel : boundary (ζ : Chain) ∈ relations := by
      simpa [T, Submodule.Quotient.mk_eq_zero] using hζ
    exact horth ζ ⟨ζ.property, hrel⟩
  obtain ⟨g, hg⟩ := exists_functional_comp_eq T ℓ hker
  -- The primitive.
  let d' := d - (1, 0, 0)
  let v := cochainOfFunctional d' (g ∘ₗ relations.mkQ)
  have hv_piece : v ∈ cochainPiece d' := cochainOfFunctional_mem _ _
  have hv_inv : v ∈ relativeInvariants := by
    apply mem_relativeInvariants_of_pairing hv_piece
    intro ζ hζ hζd
    rw [pairing_cochainOfFunctional _ _ hζd, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero relations).mpr hζ, map_zero]
  have hqv : q v = u := by
    have hqv_piece : q v ∈ cochainPiece d := by
      simpa [d'] using q_degree hv_piece
    have hsub : q v - (u : Cochain) = 0 := by
      apply cochain_eq_zero_of_pairing (Submodule.sub_mem _ hqv_piece hud)
      intro s hs
      have hsP : (Finsupp.single s 1 : Chain) ∈ P := by
        show (Finsupp.single s 1 : Chain) ∈ cochainPiece d
        rw [← hs]; exact cochain_single_mem s 1
      have hb : boundary (Finsupp.single s 1) ∈ cochainPiece d' := boundary_degree hsP
      rw [map_sub, LinearMap.sub_apply, pairing_q, pairing_cochainOfFunctional _ _ hb]
      have := congrArg (fun F => F ⟨_, hsP⟩) hg
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, T, ℓ,
        Submodule.mkQ_apply] at this
      rw [LinearMap.comp_apply, Submodule.mkQ_apply, this]
      simp
    exact sub_eq_zero.mp hsub
  -- Hence the class vanishes.
  apply Subtype.ext
  change Submodule.Quotient.mk u = (0 : Cohomology)
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨v, hv_inv, hqv⟩

theorem dictionaryMap_surjective (d : Degree) : Function.Surjective (dictionaryMap d) := by
  intro F
  let f : cycles d →ₗ[ℂ] ℂ := F ∘ₗ ((bounds d).comap (cycles d).subtype).mkQ
  obtain ⟨G, hG⟩ := LinearMap.exists_extend f
  have hGc : ∀ ζ (hζ : ζ ∈ cycles d), G ζ = F (Submodule.Quotient.mk ⟨ζ, hζ⟩) := by
    intro ζ hζ
    have := congrArg (fun H => H ⟨ζ, hζ⟩) hG
    simpa [f] using this
  have hGb : ∀ ζ ∈ bounds d, G ζ = 0 := by
    intro ζ hζ
    rw [hGc ζ (bounds_le_cycles d hζ)]
    rw [(Submodule.Quotient.mk_eq_zero _).mpr (show _ ∈ (bounds d).comap (cycles d).subtype
      from hζ), map_zero]
  let u := cochainOfFunctional d G
  have hu_piece : u ∈ cochainPiece d := cochainOfFunctional_mem _ _
  have hu_inv : u ∈ relativeInvariants := by
    apply mem_relativeInvariants_of_pairing hu_piece
    intro ζ hζ hζd
    rw [pairing_cochainOfFunctional _ _ hζd]
    exact hGb ζ (Submodule.mem_sup_left ⟨hζ, hζd⟩)
  have hu_cyc : q u = 0 := by
    have hq_piece : q u ∈ cochainPiece (d + (1, 0, 0)) := q_degree hu_piece
    apply cochain_eq_zero_of_pairing hq_piece
    intro s hs
    have hsP : (Finsupp.single s 1 : Chain) ∈ cochainPiece (d + (1, 0, 0)) :=
      hs ▸ cochain_single_mem s 1
    have hb : boundary (Finsupp.single s 1) ∈ cochainPiece d := by
      simpa using boundary_degree hsP
    rw [pairing_q, pairing_cochainOfFunctional _ _ hb]
    exact hGb _ (Submodule.mem_sup_right ⟨_, hsP, rfl⟩)
  have hu : u ∈ relativeCycles := ⟨hu_inv, hu_cyc⟩
  refine ⟨⟨classOf u hu, ⟨u, hu⟩, hu_piece, rfl⟩, ?_⟩
  ext ζ
  change pairing u ζ = F (Submodule.Quotient.mk ζ)
  rw [pairing_cochainOfFunctional _ _ ζ.property.1, hGc]

/-- **The dictionary.** The degree-`d` piece of restricted relative cohomology is the
dual of the degree-`d` homology of coinvariant chains. -/
def cohomologyPieceEquivDual (d : Degree) :
    cohomologyPiece d ≃ₗ[ℂ] Module.Dual ℂ (ChainHomology d) :=
  LinearEquiv.ofBijective (dictionaryMap d)
    ⟨dictionaryMap_injective d, dictionaryMap_surjective d⟩

@[simp] theorem cohomologyPieceEquivDual_apply (d : Degree) (h : cohomologyPiece d) :
    cohomologyPieceEquivDual d h = cohomologyToDual d h := rfl

end KhanSL2
