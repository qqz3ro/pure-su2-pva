module

public import KhanSL2.Macdonald.RootEvenAlgebra
public import KhanSL2.Macdonald.StrongBridgeFreeRaising

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual color-zero even generators define the symmetric polynomial embedding,
which intertwines the specified weighted raising derivation. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

/-- The original even polynomial variables, embedded as the color-zero σ generators. -/
def rootEvenEmbedding : RootEvenPolynomial →ₐ[ℂ] StrongMacdonald.W :=
  strongModelAlg.symm.toAlgHom.comp
    (Algebra.TensorProduct.includeLeft.comp
      (MvPolynomial.rename (fun n : ℕ => (⟨n,0⟩ : Mode))))

@[simp] theorem strongModel_rootEvenEmbedding (p : RootEvenPolynomial) :
    strongModel (rootEvenEmbedding p) =
      MvPolynomial.rename (fun n : ℕ => (⟨n,0⟩ : Mode)) p ⊗ₜ[ℂ] (1 : Exterior) := by
  change strongModelAlg (strongModelAlg.symm _) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

@[simp] theorem rootEvenEmbedding_X (n : ℕ) :
    rootEvenEmbedding (MvPolynomial.X n) = StrongMacdonald.sigOf n 0 := by
  apply strongModel.injective
  rw [strongModel_rootEvenEmbedding,MvPolynomial.rename_X]
  exact (strongModel_sig ⟨n,0⟩).symm

/-- The explicit free raising operator restricts to twice the actual polynomial shift. -/
theorem rootEvenEmbedding_shift (m : ℕ) (p : RootEvenPolynomial) :
    strongFreeRaise m (rootEvenEmbedding p) =
      (2 : ℂ) • rootEvenEmbedding (rootEvenShift m p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show MvPolynomial.C c = algebraMap ℂ RootEvenPolynomial c from rfl,
      AlgHom.commutes,Derivation.map_algebraMap,map_zero,smul_zero,
      Algebra.algebraMap_eq_smul_one,map_smul,(strongFreeRaise_homDer m).map_one,smul_zero]
  | add p q hp hq => simp only [map_add,hp,hq,smul_add]
  | mul_X p n hp =>
    have hn : strongFreeRaise m (StrongMacdonald.sigOf n 0) =
        (2 : ℂ) • StrongMacdonald.sigOf (n+m) 0 := strongFreeRaise_sig m ⟨n,0⟩
    have hmul : rootEvenShift m (p * MvPolynomial.X n) =
        rootEvenShift m p * MvPolynomial.X n + p * rootEvenShift m (MvPolynomial.X n) := by
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      ring
    rw [map_mul,(strongFreeRaise_homDer m).zero_mul_apply,rootEvenEmbedding_X,hn,hp,hmul]
    simp only [map_add,map_mul,rootEvenShift_X,rootEvenEmbedding_X,
      smul_add,smul_mul_assoc,mul_smul_comm,Nat.add_comm n m]

/-- The generator inclusion lands in the actual free color-zero subspace. -/
theorem rootEvenEmbedding_mem_free (p : RootEvenPolynomial) :
    rootEvenEmbedding p ∈ strongFree := by
  change StrongMacdonald.projFull (rootEvenEmbedding p) = rootEvenEmbedding p
  have h : StrongMacdonald.projFull.comp rootEvenEmbedding = rootEvenEmbedding := by
    apply MvPolynomial.algHom_ext
    intro n
    simp [rootEvenEmbedding_X,StrongMacdonald.sigOf,StrongMacdonald.projFull_sig]
  exact DFunLike.congr_fun h p

end KhanSL2.Macdonald
