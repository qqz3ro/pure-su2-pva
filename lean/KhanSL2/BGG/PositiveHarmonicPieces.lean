module

public import KhanSL2.BGG.PositiveContractionGrading

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual harmonic spaces in every degree and energy, as sl₂ modules. -/
noncomputable section
namespace KhanSL2.BGG.PositiveCE

/-- Actual harmonic vectors in a prescribed exterior degree and energy. -/
def harmonicLiePiece (p N : ℕ) : LieSubmodule ℂ G Harmonic :=
  { (piece p N).comap Harmonic.subtype with
    lie_mem := fun {x _u} hu => positiveAction_mem_piece x hu }

/-- Restricting the actual harmonic kernel is precisely the finite spectral kernel.
The equivalence only rearranges subtypes; it does not assume a homology theorem. -/
def harmonicPieceEquivSpectral (p N : ℕ) :
    harmonicLiePiece p N ≃ₗ⁅ℂ,G⁆ spectralKernel p N where
  toFun u := ⟨⟨((u : Harmonic) : Cochain), u.property⟩, by
    change spectralOperator p N ⟨((u : Harmonic) : Cochain), u.property⟩ = 0
    apply Subtype.ext
    change (spectralOperator p N ⟨((u : Harmonic) : Cochain), u.property⟩ : Cochain) = 0
    rw [← energyCasimir_coe_piece, ← laplacian_eq_energyCasimir]
    exact (u : Harmonic).property⟩
  invFun u := ⟨⟨((u : liePiece p N) : Cochain), by
    change laplacian ((u : liePiece p N) : Cochain) = 0
    rw [laplacian_eq_energyCasimir, energyCasimir_coe_piece]
    have hu : spectralOperator p N (u : liePiece p N) = 0 := u.property
    rw [hu]
    rfl⟩, (u : liePiece p N).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

instance finiteDimensional_harmonicLiePiece (p N : ℕ) :
    FiniteDimensional ℂ (harmonicLiePiece p N) :=
  FiniteDimensional.of_injective (harmonicPieceEquivSpectral p N).toLinearMap
    (harmonicPieceEquivSpectral p N).injective

/-- The exceptional actual harmonic piece is the standard representation `V(2p)`. -/
theorem harmonicLiePiece_nonempty_equiv_standard (p : ℕ) :
    Nonempty ((harmonicLiePiece p (triangular p) : Type) ≃ₗ⁅ℂ,G⁆ TauCeti.Sl2Std ℂ (2*p)) := by
  obtain ⟨e⟩ := spectralKernel_nonempty_equiv_standard p
  exact ⟨(harmonicPieceEquivSpectral p (triangular p)).trans e⟩

/-- The full degree/energy dimension formula for actual harmonic cochains. -/
theorem harmonicLiePiece_finrank (p N : ℕ) :
    Module.finrank ℂ (harmonicLiePiece p N) = if N = triangular p then 2*p+1 else 0 := by
  rw [(harmonicPieceEquivSpectral p N).toLinearEquiv.finrank_eq]
  exact spectralKernel_finrank p N

/-- An actual harmonic cochain of pure exterior degree has only the triangular energy. -/
theorem harmonic_mem_piece_of_degree (p : ℕ) (u : Harmonic)
    (hu : (u : Cochain) ∈ Finsupp.supported ℂ ℂ {s : Finset Mode | s.card = p}) :
    (u : Cochain) ∈ piece p (triangular p) := by
  intro s hs
  refine ⟨hu hs, ?_⟩
  by_contra hN
  let q := (p, monomialEnergy s)
  let v := BasisGrading.projection bidegree q (u : Cochain)
  have hv : v ∈ piece p (monomialEnergy s) :=
    (mem_bidegree_piece q v).mp (BasisGrading.projection_mem bidegree q u)
  have hL : laplacian v = 0 := by
    have h := BasisGrading.projection_linearMap bidegree laplacian id Function.injective_id
      (fun k w hw => (mem_bidegree_piece k _).mpr
        (laplacian_mem_piece ((mem_bidegree_piece k w).mp hw))) q (u : Cochain)
    have hu0 : laplacian (u : Cochain) = 0 := u.property
    rw [hu0, map_zero] at h
    exact h.symm
  have hv0 := eq_zero_of_laplacian_eq_zero_of_energy_ne hv hL hN
  have he := congrArg (fun w : Cochain => w s) hv0
  have hcard : s.card = p := hu hs
  have hu0 : (u : Cochain) s = 0 := by
    simpa [v, q, BasisGrading.projection_apply, bidegree, hcard] using he
  exact (Finsupp.mem_support_iff.mp hs) hu0

/-- The actual harmonic subrepresentation of exterior degree `p`. -/
def harmonicDegree (p : ℕ) : LieSubmodule ℂ G Harmonic :=
  { (Finsupp.supported ℂ ℂ {s : Finset Mode | s.card = p}).comap Harmonic.subtype with
    lie_mem := fun {x u} hu => by
      have hfull := harmonic_mem_piece_of_degree p u hu
      have ha := positiveAction_mem_piece x hfull
      exact fun s hs => (ha hs).1 }

/-- The entire degree-p harmonic representation occurs at exactly triangular energy. -/
theorem harmonicDegree_eq_piece (p : ℕ) : harmonicDegree p = harmonicLiePiece p (triangular p) := by
  ext u
  constructor
  · exact harmonic_mem_piece_of_degree p u
  · exact fun hu s hs => (hu hs).1

instance finiteDimensional_harmonicDegree (p : ℕ) : FiniteDimensional ℂ (harmonicDegree p) := by
  rw [harmonicDegree_eq_piece]
  infer_instance

/-- The actual harmonic chain group in degree p is `V(2p)` as an sl₂ module. -/
theorem harmonicDegree_nonempty_equiv_standard (p : ℕ) :
    Nonempty ((harmonicDegree p : Type) ≃ₗ⁅ℂ,G⁆ TauCeti.Sl2Std ℂ (2*p)) := by
  rw [harmonicDegree_eq_piece]
  exact harmonicLiePiece_nonempty_equiv_standard p

theorem harmonicDegree_finrank (p : ℕ) : Module.finrank ℂ (harmonicDegree p) = 2*p+1 := by
  rw [harmonicDegree_eq_piece, harmonicLiePiece_finrank, if_pos rfl]

end KhanSL2.BGG.PositiveCE
