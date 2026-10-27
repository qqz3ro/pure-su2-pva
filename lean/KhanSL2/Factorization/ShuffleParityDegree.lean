module

public import KhanSL2.Factorization.ShuffleRelativeDifferential

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The parity in the actual tensor boundary is exactly the usual degree sign. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.BGGBridge KhanSL2.Current

/-- The exterior comparison preserves the parity automorphism. -/
theorem exteriorEquiv_parity (u : ExteriorAlgebra ℂ plus) :
    exteriorEquiv (ExteriorShuffle.parity plus u) =
      FiniteExterior.parityLinear (exteriorEquiv u) := by
  have h : exteriorEquiv.toAlgHom.comp (ExteriorShuffle.parity plus) =
      FiniteExterior.parity.comp exteriorEquiv.toAlgHom := by
    apply ExteriorAlgebra.hom_ext
    apply plusModeBasis.ext
    intro m
    change exteriorEquiv (ExteriorShuffle.parity plus
      (ExteriorAlgebra.ι ℂ (plusModeBasis m))) =
      FiniteExterior.parityLinear (exteriorEquiv (ExteriorAlgebra.ι ℂ (plusModeBasis m)))
    rw [ExteriorShuffle.parity_ι, map_neg]
    change -toE (ExteriorAlgebra.ι ℂ (plusModeBasis m)) =
      FiniteExterior.parityLinear (toE (ExteriorAlgebra.ι ℂ (plusModeBasis m)))
    rw [toE_ι_basis, FiniteExterior.parity_generator]
  exact DFunLike.congr_fun h u

/-- On the actual positive degree-j subspace, parity is multiplication by (-1)^j. -/
theorem parityLinear_of_mem_degC {j : ℕ} {u : PositiveCE.Cochain} (hu : u ∈ degC j) :
    FiniteExterior.parityLinear u = (-1 : ℂ)^j • u := by
  calc
    FiniteExterior.parityLinear u =
        ∑ s ∈ u.support, FiniteExterior.parityLinear (Finsupp.single s (u s)) := by
          rw [← map_sum]
          congr 1
          exact (Finsupp.sum_single u).symm
    _ = ∑ s ∈ u.support, (-1 : ℂ)^j • Finsupp.single s (u s) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [FiniteExterior.parity_single, hu hs]
    _ = (-1 : ℂ)^j • u := by
      rw [← Finset.smul_sum]
      congr 1
      exact Finsupp.sum_single u

variable (N : Type*) [AddCommGroup N] [Module ℂ N]

@[simp] theorem rawParity_tmul (u : PositiveCE.Cochain) (n : N) :
    rawParity N (u ⊗ₜ[ℂ] n) = FiniteExterior.parityLinear u ⊗ₜ[ℂ] n := by
  obtain ⟨v, rfl⟩ := exteriorEquiv.surjective u
  change rawParity N (CEModel.J (v ⊗ₜ[ℂ] n)) = _
  rw [rawParity_J, CEParity.parity_tmul, CEModel.J_tmul, exteriorEquiv_parity]

theorem rawParity_of_mem_degree {j : ℕ} {z : RawChains N} (hz : z ∈ rawDegree N j) :
    rawParity N z = (-1 : ℂ)^j • z := by
  obtain ⟨u, rfl⟩ := hz
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul u n =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, rawParity_tmul,
      parityLinear_of_mem_degC u.property, TensorProduct.smul_tmul']
  | add u v hu hv => simp only [map_add, hu, hv, smul_add]

variable [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]

/-- The signed relative tensor differential uses the ordinary exterior-degree sign. -/
theorem relativeParity_of_mem_degree {j : ℕ} {z : RelativeChains N}
    (hz : z ∈ degree N j) : relativeParity N z = (-1 : ℂ)^j • z := by
  obtain ⟨u, hu, rfl⟩ := hz
  rw [relativeParity_mk, rawParity_of_mem_degree N hu, map_smul]

end KhanSL2.Factorization
