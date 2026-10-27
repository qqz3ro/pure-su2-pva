module

public import KhanSL2.Macdonald.RootOddEmbedding
public import KhanSL2.Macdonald.StrongBridgeFreeRaising

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual odd polynomial embedding intertwines ordinary root raising with
the specified free-source odd raising. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open PolynomialBGG

theorem rootOddExterior_raise_ι (m : ℕ) (p : Polynomial ℂ) :
    freeOddRaise m (rootOddExterior (ExteriorAlgebra.ι ℂ p)) =
      rootOddExterior (ExteriorAlgebra.ι ℂ ((Polynomial.X : Polynomial ℂ)^m * p)) := by
  have h : (freeOddRaise m).comp (rootOddExterior.toLinearMap.comp (ExteriorAlgebra.ι ℂ)) =
      rootOddExterior.toLinearMap.comp ((ExteriorAlgebra.ι ℂ).comp
        (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m))) := by
    apply (Polynomial.basisMonomials ℂ).ext
    intro n
    simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,
      rootOddExterior_ι_basis,freeOddRaise_generator]
    simp only [Polynomial.coe_basisMonomials,← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.C_1,one_mul,LinearMap.mulLeft_apply,← pow_add]
    have hn := rootOddExterior_ι_basis (m+n)
    simp only [Polynomial.coe_basisMonomials,← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.C_1,one_mul] at hn
    rw [hn]
    simp [freeOddRaiseGenerator,Nat.add_comm]
  exact LinearMap.congr_fun h p

theorem rootOddExterior_derivExt (m : ℕ) (x : ExteriorAlgebra ℂ (Polynomial ℂ)) :
    rootOddExterior (LieChains.derivExt
      (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)) x) =
        freeOddRaise m (rootOddExterior x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [LieChains.derivExt_algebraMap,map_zero,AlgHom.commutes]
    rw [Algebra.algebraMap_eq_smul_one,map_smul,freeOddRaise_one,smul_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | ι_mul p x hx =>
    rw [LieChains.derivExt_ι_mul,map_add,map_mul,map_mul,hx,map_mul,
      freeOddRaise_mul,rootOddExterior_raise_ι]
    rfl

/-- Raising on the actual exterior power matches the source generator shift. -/
theorem rootOddPowerEmbedding_shift (m q : ℕ) (x : ⋀[ℂ]^q (Polynomial ℂ)) :
    rootOddPowerEmbedding q (exteriorDeriv q
      (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)) x) =
        freeOddRaise m (rootOddPowerEmbedding q x) :=
  rootOddExterior_derivExt m x.val

/-- The actual odd exterior embedding into the full free superalgebra. -/
def rootOddStrongEmbedding : ExteriorAlgebra ℂ (Polynomial ℂ) →ₐ[ℂ] StrongMacdonald.W :=
  StrongMacdonald.ofExt.comp rootOddExterior

@[simp] theorem rootOddStrongEmbedding_ι_basis (n : ℕ) :
    rootOddStrongEmbedding (ExteriorAlgebra.ι ℂ (Polynomial.basisMonomials ℂ n)) =
      StrongMacdonald.psiOf n 0 := by
  rw [rootOddStrongEmbedding,AlgHom.comp_apply,rootOddExterior_ι_basis]
  rfl

theorem strongFreeRaise_ofExt (m : ℕ) (x : Exterior) :
    strongFreeRaise m (StrongMacdonald.ofExt x) = StrongMacdonald.ofExt (freeOddRaise m x) := by
  apply strongModel.injective
  rw [← strongModel_freeRaise,strongModel_ofExt,strongModel_ofExt]
  simp [freeMixedRaise,freeMixedShift]

/-- The explicit free-source derivation and actual polynomial exterior derivation agree. -/
theorem rootOddStrongEmbedding_shift (m : ℕ) (x : ExteriorAlgebra ℂ (Polynomial ℂ)) :
    strongFreeRaise m (rootOddStrongEmbedding x) =
      rootOddStrongEmbedding (LieChains.derivExt
        (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)) x) := by
  change strongFreeRaise m (StrongMacdonald.ofExt (rootOddExterior x)) = _
  rw [strongFreeRaise_ofExt,← rootOddExterior_derivExt]
  rfl

theorem rootOddStrongEmbedding_mem_free (x : ExteriorAlgebra ℂ (Polynomial ℂ)) :
    rootOddStrongEmbedding x ∈ strongFree := by
  change StrongMacdonald.projFull (rootOddStrongEmbedding x) = rootOddStrongEmbedding x
  have h : StrongMacdonald.projFull.comp rootOddStrongEmbedding = rootOddStrongEmbedding := by
    apply ExteriorAlgebra.hom_ext
    apply (Polynomial.basisMonomials ℂ).ext
    intro n
    change StrongMacdonald.projFull
      (rootOddStrongEmbedding (ExteriorAlgebra.ι ℂ (Polynomial.basisMonomials ℂ n))) =
        rootOddStrongEmbedding (ExteriorAlgebra.ι ℂ (Polynomial.basisMonomials ℂ n))
    rw [rootOddStrongEmbedding_ι_basis]
    simp [StrongMacdonald.psiOf,StrongMacdonald.projFull_psi]
  exact DFunLike.congr_fun h x

end KhanSL2.Macdonald
