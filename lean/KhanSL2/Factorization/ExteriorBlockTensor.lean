module

public import KhanSL2.Factorization.ExteriorBlockCoproduct
public import KhanSL2.PolynomialBGG.ProjectiveModel

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # The original normalized exterior section and literal tensor blocks -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.ExteriorBlock

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- Full alternation is independent of the chosen finite indexing equivalence. -/
theorem alternatization_domDomCongr {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (f : MultilinearMap ℂ (fun _ : ι => M) N) :
    (f.domDomCongr e).alternatization = f.alternatization.domDomCongr e := by
  ext v
  simp only [MultilinearMap.alternatization_apply, AlternatingMap.domDomCongr_apply,
    MultilinearMap.domDomCongr_apply]
  rw [← Equiv.sum_comp e.permCongr]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Equiv.Perm.sign_permCongr]
  congr 2
  funext i
  simp [Equiv.permCongr_apply, Function.comp_def]

variable (M)

/-- Wedge the first and second labelled blocks separately, with their original ordering. -/
def tensorBlockMap (r s : ℕ) :
    (⨂[ℂ] (_ : Fin (r+s)), M) →ₗ[ℂ]
      ExteriorAlgebra ℂ M ⊗[ℂ] ExteriorAlgebra ℂ M :=
  PiTensorProduct.lift
    ((MultilinearMap.domCoprod (ExteriorAlgebra.ιMulti ℂ r (M := M)).toMultilinearMap
      (ExteriorAlgebra.ιMulti ℂ s (M := M)).toMultilinearMap).domDomCongr finSumFinEquiv)

@[simp] theorem tensorBlockMap_tprod (r s : ℕ) (v : Fin (r+s) → M) :
    tensorBlockMap M r s (PiTensorProduct.tprod ℂ v) =
      ExteriorAlgebra.ιMulti ℂ r (fun i => v (finSumFinEquiv (Sum.inl i))) ⊗ₜ[ℂ]
        ExteriorAlgebra.ιMulti ℂ s (fun i => v (finSumFinEquiv (Sum.inr i))) :=
  PiTensorProduct.lift.tprod _

/-- The signed shuffle block map supplied by the alternating universal property. -/
def exteriorBlockMap (r s : ℕ) : (⋀[ℂ]^(r+s) M) →ₗ[ℂ]
    ExteriorAlgebra ℂ M ⊗[ℂ] ExteriorAlgebra ℂ M :=
  exteriorPower.alternatingMapLinearEquiv
    (((ExteriorAlgebra.ιMulti ℂ r).domCoprod (ExteriorAlgebra.ιMulti ℂ s)).domDomCongr
      finSumFinEquiv)

@[simp] theorem exteriorBlockMap_ιMulti (r s : ℕ) (v : Fin (r+s) → M) :
    exteriorBlockMap M r s (exteriorPower.ιMulti ℂ (r+s) v) =
      ((ExteriorAlgebra.ιMulti ℂ r).domCoprod (ExteriorAlgebra.ιMulti ℂ s))
        (v ∘ finSumFinEquiv) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The literal two-block tensor map after the previously defined normalized
exterior section is precisely the inverse-binomial signed shuffle block map. -/
theorem tensorBlockMap_exteriorToTensor (r s : ℕ) (x : ⋀[ℂ]^(r+s) M) :
    tensorBlockMap M r s (PolynomialBGG.exteriorToTensor M (r+s) x) =
      (Nat.choose (r+s) r : ℂ)⁻¹ • exteriorBlockMap M r s x := by
  have heq : (tensorBlockMap M r s).compMultilinearMap (PiTensorProduct.tprod ℂ) =
      (MultilinearMap.domCoprod (ExteriorAlgebra.ιMulti ℂ r (M := M)).toMultilinearMap
        (ExteriorAlgebra.ιMulti ℂ s (M := M)).toMultilinearMap).domDomCongr finSumFinEquiv := by
    ext v
    exact tensorBlockMap_tprod M r s v
  have h := LinearMap.compMultilinearMap_alternatization
    (tensorBlockMap M r s) (PiTensorProduct.tprod ℂ)
  rw [heq, alternatization_domDomCongr,
    MultilinearMap.domCoprod_alternatization_eq] at h
  have hmap : (tensorBlockMap M r s).comp (PolynomialBGG.exteriorToTensor M (r+s)) =
      (Nat.choose (r+s) r : ℂ)⁻¹ • exteriorBlockMap M r s := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have hv := congrArg (fun f => f v) h
    simp only [AlternatingMap.domDomCongr_apply, AlternatingMap.smul_apply,
      Fintype.card_fin, LinearMap.compAlternatingMap_apply] at hv
    change tensorBlockMap M r s (PolynomialBGG.exteriorToTensor M (r+s)
      (exteriorPower.ιMulti ℂ (r+s) v)) = _
    rw [PolynomialBGG.exteriorToTensor, LinearMap.smul_apply, map_smul]
    simp only [exteriorPower.toTensorPower,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rw [← hv, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul,
      factorial_ratio_eq_inv_choose]
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply, exteriorBlockMap_ιMulti]
  exact LinearMap.congr_fun hmap x

end KhanSL2.Factorization.ExteriorBlock
