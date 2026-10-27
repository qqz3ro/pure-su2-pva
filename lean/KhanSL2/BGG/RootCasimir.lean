module

public import KhanSL2.BGG.RootHighest
public import TauCeti.Algebra.Lie.Sl2.Generated
public import TauCeti.Algebra.Lie.Sl2.CompleteReducibility

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual Casimir spectral problem on finite root degree-energy pieces.
These operators are defined independently of the CE Laplacian identity. -/

noncomputable section
namespace KhanSL2.BGG

/-- The actual traceless-matrix root generators form an sl₂ triple. -/
theorem rootSl2Triple : IsSl2Triple MatrixSL2.h MatrixSL2.e MatrixSL2.f where
  h_ne_zero := by
    intro h
    have hz := congrArg (fun x : G => x.val 0 0) h
    norm_num [MatrixSL2.h] at hz
  lie_e_f := G.lie_e_f
  lie_h_e_nsmul := by simpa [two_smul] using G.lie_h_e
  lie_h_f_nsmul := by simpa [two_smul] using G.lie_h_f

theorem rootSl2Triple_top : rootSl2Triple.toLieSubalgebra ℂ = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  rw [IsSl2Triple.mem_toLieSubalgebra_iff]
  refine ⟨x.val 0 1, x.val 1 0, x.val 0 0, ?_⟩
  rw [G.lie_e_f]
  conv_lhs => rw [MatrixSL2.decompose x]
  abel

/-- Casimir acts on each actual finite degree-energy representation. -/
def rootPieceCasimir (d N : ℕ) :
    rootExteriorLiePiece d N →ₗ⁅ℂ,G⁆ rootExteriorLiePiece d N :=
  TauCeti.sl2CasimirHom rootSl2Triple rootSl2Triple_top _

/-- The spectral operator `N − Casimir/4`; no identification with a Laplacian is assumed. -/
def rootSpectralOperator (d N : ℕ) :
    rootExteriorLiePiece d N →ₗ⁅ℂ,G⁆ rootExteriorLiePiece d N :=
  (N : ℂ) • LieModuleHom.id - (1 / 4 : ℂ) • rootPieceCasimir d N

@[simp] theorem rootSpectralOperator_apply (d N : ℕ) (u : rootExteriorLiePiece d N) :
    rootSpectralOperator d N u = (N : ℂ) • u - (1 / 4 : ℂ) •
      TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f (rootExteriorLiePiece d N) u := by
  simp [rootSpectralOperator, rootPieceCasimir]

/-- The actual spectral kernel; it becomes the harmonic space only after proving the Laplacian formula. -/
def rootCasimirKernel (d N : ℕ) : LieSubmodule ℂ G (rootExteriorLiePiece d N) :=
  (rootSpectralOperator d N).ker

@[simp] theorem mem_rootCasimirKernel (d N : ℕ) (u : rootExteriorLiePiece d N) :
    u ∈ rootCasimirKernel d N ↔ rootSpectralOperator d N u = 0 := Iff.rfl

theorem casimirScalar_two_mul (j : ℕ) :
    (((2 * j : ℕ) : ℂ) * (((2 * j : ℕ) : ℂ) + 2) / 2) = 4 * (triangular j : ℂ) := by
  have ht : (2 : ℂ) * (triangular j : ℂ) = (j : ℂ) * (j + 1) := by
    exact_mod_cast two_mul_triangular j
  push_cast
  calc
    (2 * (j : ℂ)) * (2 * (j : ℂ) + 2) / 2 = 2 * ((j : ℂ) * (j + 1)) := by ring
    _ = 4 * (triangular j : ℂ) := by rw [← ht]; ring

/-- On a primitive vector of weight `2j`, the spectral scalar is exactly `N−triangular j`. -/
theorem rootSpectralOperator_primitive_even {d N j : ℕ} {u : rootExteriorLiePiece d N}
    (P : rootSl2Triple.HasPrimitiveVectorWith u ((2 * j : ℕ) : ℂ)) :
    rootSpectralOperator d N u = ((N : ℂ) - (triangular j : ℂ)) • u := by
  rw [rootSpectralOperator_apply, TauCeti.sl2Casimir_apply_of_hasPrimitiveVectorWith P,
    casimirScalar_two_mul, smul_smul, ← sub_smul]
  congr 1
  ring

/-- Every primitive weight in a fixed-energy piece is even and has the sharp spectral bound. -/
theorem rootPrimitive_spectral {d N n : ℕ} {u : rootExteriorLiePiece d N}
    (P : rootSl2Triple.HasPrimitiveVectorWith u (n : ℂ)) :
    ∃ j : ℕ, n = 2 * j ∧ triangular j ≤ N ∧
      rootSpectralOperator d N u = ((N : ℂ) - (triangular j : ℂ)) • u := by
  have hne : (u : RootExterior) ≠ 0 := fun h => P.ne_zero (Subtype.ext h)
  have hH : rootExteriorAction MatrixSL2.h (u : RootExterior) = (n : ℂ) • (u : RootExterior) :=
    congrArg Subtype.val P.lie_h
  obtain ⟨j, hn, hN⟩ := root_h_nonnegative_eigenvalue_energy u.property hne n hH
  refine ⟨j, hn, hN, ?_⟩
  subst n
  exact rootSpectralOperator_primitive_even P

/-- A primitive vector in the spectral kernel has the unique matching energy and degree. -/
theorem rootPrimitive_in_kernel_degree {d N n : ℕ} {u : rootExteriorLiePiece d N}
    (P : rootSl2Triple.HasPrimitiveVectorWith u (n : ℂ)) (hu : u ∈ rootCasimirKernel d N) :
    ∃ j : ℕ, n = 2 * j ∧ N = triangular j ∧ d = j := by
  obtain ⟨j, hn, _, hscalar⟩ := rootPrimitive_spectral P
  have hzero : rootSpectralOperator d N u = 0 := hu
  rw [hscalar] at hzero
  have hN : N = triangular j := by
    have hdiff : (N : ℂ) - (triangular j : ℂ) = 0 :=
      (smul_eq_zero.mp hzero).resolve_right P.ne_zero
    exact_mod_cast sub_eq_zero.mp hdiff
  have hne : (u : RootExterior) ≠ 0 := fun h => P.ne_zero (Subtype.ext h)
  have hH : rootExteriorAction MatrixSL2.h (u : RootExterior) = (2 * (j : ℂ)) • (u : RootExterior) := by
    have hh : rootExteriorAction MatrixSL2.h (u : RootExterior) = (n : ℂ) • (u : RootExterior) := congrArg Subtype.val P.lie_h
    rw [hn] at hh
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  have hd : d = j := root_h_eigenvector_minimal_degree j (hN ▸ u.property) hne hH
  exact ⟨j, hn, hN, hd⟩

/-- The explicit highest wedge, read in its finite-dimensional ambient piece. -/
def rootHighestVector (j : ℕ) : rootExteriorLiePiece j (triangular j) :=
  ⟨FiniteExterior.monomial (RootSupport.highest j).toFinset, rootHighest_mem_piece j⟩

theorem rootHighestVector_primitive (j : ℕ) :
    rootSl2Triple.HasPrimitiveVectorWith (rootHighestVector j) ((2 * j : ℕ) : ℂ) where
  ne_zero := fun h => rootHighestMonomial_ne_zero j (congrArg Subtype.val h)
  lie_h := Subtype.ext (by
    change rootExteriorAction MatrixSL2.h (FiniteExterior.monomial (RootSupport.highest j).toFinset) =
      ((2 * j : ℕ) : ℂ) • FiniteExterior.monomial (RootSupport.highest j).toFinset
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using rootHighest_h j)
  lie_e := Subtype.ext (rootHighest_e j)

/-- The irreducible module generated by the actual minimum-energy highest wedge. -/
def rootHighestModule (j : ℕ) : LieSubmodule ℂ G (rootExteriorLiePiece j (triangular j)) :=
  LieSubmodule.lieSpan ℂ G {rootHighestVector j}

instance rootHighestModule_irreducible (j : ℕ) : LieModule.IsIrreducible ℂ G (rootHighestModule j) :=
  TauCeti.isIrreducible_lieSpan_singleton rootSl2Triple_top (rootHighestVector_primitive j)

theorem rootHighestModule_finrank (j : ℕ) : Module.finrank ℂ (rootHighestModule j) = 2 * j + 1 :=
  TauCeti.finrank_lieSpan_singleton rootSl2Triple_top (rootHighestVector_primitive j)

/-- Every vector in the generated minimum-energy component lies in the spectral kernel. -/
theorem rootHighestModule_le_kernel (j : ℕ) : rootHighestModule j ≤ rootCasimirKernel j (triangular j) := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro u rfl
  change rootSpectralOperator j (triangular j) (rootHighestVector j) = 0
  rw [rootSpectralOperator_primitive_even (rootHighestVector_primitive j), sub_self, zero_smul]

end KhanSL2.BGG