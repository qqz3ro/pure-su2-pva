module

public import KhanSL2.BGG.RootCasimir
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Classification of the actual Casimir spectral kernels, before identifying the
spectral operator with the Chevalley–Eilenberg Laplacian. -/

noncomputable section
namespace KhanSL2.BGG

/-- Every nonzero subrepresentation of a finite exterior piece contains an actual
primitive vector with a natural highest weight. -/
theorem rootSubmodule_exists_primitive {d N : ℕ}
    (S : LieSubmodule ℂ G (rootExteriorLiePiece d N)) (hS : S ≠ ⊥) :
    ∃ (u : rootExteriorLiePiece d N) (n : ℕ),
      u ∈ S ∧ rootSl2Triple.HasPrimitiveVectorWith u (n : ℂ) := by
  let : Nontrivial S := (LieSubmodule.nontrivial_iff_ne_bot ℂ G _).mpr hS
  obtain ⟨u, n, P⟩ := TauCeti.exists_hasPrimitiveVectorWith (K := ℂ) S rootSl2Triple
  refine ⟨u, n, u.property, ?_⟩
  exact {
    ne_zero := fun h => P.ne_zero (Subtype.ext h)
    lie_h := congrArg Subtype.val P.lie_h
    lie_e := congrArg Subtype.val P.lie_e }

/-- A nonzero spectral kernel forces both the triangular energy and its matching degree. -/
theorem rootCasimirKernel_ne_bot_degree {d N : ℕ} (hK : rootCasimirKernel d N ≠ ⊥) :
    ∃ j : ℕ, N = triangular j ∧ d = j := by
  obtain ⟨u, n, hu, P⟩ := rootSubmodule_exists_primitive _ hK
  obtain ⟨j, _, hN, hd⟩ := rootPrimitive_in_kernel_degree P hu
  exact ⟨j, hN, hd⟩

/-- All bidegrees except `(j, triangular j)` have zero spectral kernel. -/
theorem rootCasimirKernel_eq_bot_of_energy_ne {d N : ℕ} (hN : N ≠ triangular d) :
    rootCasimirKernel d N = ⊥ := by
  by_contra hK
  obtain ⟨j, hj, rfl⟩ := rootCasimirKernel_ne_bot_degree hK
  exact hN hj

/-- Every primitive vector in a minimum-energy spectral kernel is a scalar
multiple of the explicit highest wedge, hence lies in its generated module. -/
theorem rootPrimitive_kernel_mem_highest {j n : ℕ}
    {u : rootExteriorLiePiece j (triangular j)}
    (P : rootSl2Triple.HasPrimitiveVectorWith u (n : ℂ))
    (hu : u ∈ rootCasimirKernel j (triangular j)) : u ∈ rootHighestModule j := by
  obtain ⟨k, hn, _, hk⟩ := rootPrimitive_in_kernel_degree P hu
  subst k
  have hH : rootExteriorAction MatrixSL2.h (u : RootExterior) =
      (2 * (j : ℂ)) • (u : RootExterior) := by
    have hh : rootExteriorAction MatrixSL2.h (u : RootExterior) =
        (n : ℂ) • (u : RootExterior) := congrArg Subtype.val P.lie_h
    rw [hn] at hh
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  have hs := root_h_eigenvector_minimal_mem_span j u.property hH
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hs
  have heq : r • rootHighestVector j = u := Subtype.ext hr
  rw [← heq]
  exact (rootHighestModule j).smul_mem r (LieSubmodule.subset_lieSpan rfl)

/-- Complete reducibility and uniqueness of the minimal highest-weight line
identify the entire spectral kernel with the explicitly generated component. -/
theorem rootCasimirKernel_eq_highestModule (j : ℕ) :
    rootCasimirKernel j (triangular j) = rootHighestModule j := by
  let H := rootHighestModule j
  let K := rootCasimirKernel j (triangular j)
  obtain ⟨C, hC⟩ := TauCeti.exists_isCompl_sl_fin_two H
  have hKC : K ⊓ C = ⊥ := by
    by_contra hne
    obtain ⟨u, n, hu, P⟩ := rootSubmodule_exists_primitive (K ⊓ C) hne
    have huH : u ∈ H := rootPrimitive_kernel_mem_highest P hu.1
    have huHC : u ∈ H ⊓ C := ⟨huH, hu.2⟩
    rw [hC.inf_eq_bot] at huHC
    exact P.ne_zero (by simpa using huHC)
  apply le_antisymm ?_ (rootHighestModule_le_kernel j)
  intro u hu
  have huHC : u ∈ H ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := (LieSubmodule.mem_sup H C u).mp huHC
  have hbK : b ∈ K := by
    have hd := K.sub_mem hu (rootHighestModule_le_kernel j ha)
    simpa [← hab] using hd
  have hb0 : b = 0 := by
    have hmem : b ∈ K ⊓ C := ⟨hbK, hb⟩
    rw [hKC] at hmem
    simpa using hmem
  have hau : a = u := by simpa [hb0] using hab
  simpa [← hau] using ha

/-- The exceptional spectral kernel is the irreducible representation of
highest weight `2j`; its dimension is exactly `2j+1`. -/
theorem rootCasimirKernel_finrank (j : ℕ) :
    Module.finrank ℂ (rootCasimirKernel j (triangular j)) = 2 * j + 1 := by
  rw [rootCasimirKernel_eq_highestModule]
  exact rootHighestModule_finrank j

instance rootCasimirKernel_irreducible (j : ℕ) :
    LieModule.IsIrreducible ℂ G (rootCasimirKernel j (triangular j)) := by
  rw [rootCasimirKernel_eq_highestModule]
  infer_instance

/-- The exceptional kernel is actually isomorphic to the standard highest-weight
`2j` representation, not merely equal in dimension. -/
theorem rootCasimirKernel_nonempty_equiv_standard (j : ℕ) :
    Nonempty ((rootCasimirKernel j (triangular j) : Type) ≃ₗ⁅ℂ,G⁆ TauCeti.Sl2Std ℂ (2 * j)) := by
  obtain ⟨n, ⟨e⟩, _⟩ := TauCeti.Sl2Std.existsUnique_nonempty_lieModuleEquiv
    (K := ℂ) (rootCasimirKernel j (triangular j))
  have hn := e.toLinearEquiv.finrank_eq
  rw [rootCasimirKernel_finrank, TauCeti.Sl2Std.finrank_eq] at hn
  have heq : n = 2 * j := by omega
  subst n
  exact ⟨e⟩

end KhanSL2.BGG
