module

public import KhanSL2.SymmetricFamily.TensorDerivations
public import KhanSL2.PolynomialBGG.TensorModel

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! Symmetric current coefficients as invariant labelled-root polynomials with
finite color tensors. Both permutations and coefficient operators are explicit. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open Macdonald PolynomialBGG

/-- The finite-color labelled-root ambient module. -/
abbrev Labelled (k : ℕ) := RootPolynomial k ⊗[ℂ] Color k

/-- Relabel the roots, contravariantly to slot precomposition. -/
def rootPermute {k : ℕ} (σ : Equiv.Perm (Fin k)) : Module.End ℂ (RootPolynomial k) :=
  (MvPolynomial.rename σ.symm).toLinearMap

/-- Relabel the finite color tensor basis in exactly the same slots. -/
def colorPermute {k : ℕ} (σ : Equiv.Perm (Fin k)) : Module.End ℂ (Color k) :=
  (Pi.basisFun ℂ (Fin k → Fin 3)).constr ℂ
    (fun c => Pi.basisFun ℂ (Fin k → Fin 3) (c ∘ σ))

@[simp] theorem colorPermute_basis {k : ℕ} (σ : Equiv.Perm (Fin k)) (c : Fin k → Fin 3) :
    colorPermute σ (Pi.basisFun ℂ (Fin k → Fin 3) c) =
      Pi.basisFun ℂ (Fin k → Fin 3) (c ∘ σ) := Module.Basis.constr_basis _ _ _ _

/-- The actual simultaneous permutation of labelled roots and color slots. -/
def labelledPermute {k : ℕ} (σ : Equiv.Perm (Fin k)) : Module.End ℂ (Labelled k) :=
  TensorProduct.map (rootPermute σ) (colorPermute σ)

/-- The root-polynomial identification carries tensor permutation to simultaneous permutation. -/
theorem rootTensorEquiv_permute {k : ℕ} (σ : Equiv.Perm (Fin k))
    (x : ⨂[ℂ]^k BGG.Current) :
    rootTensorEquiv k (tensorPermute σ x) = labelledPermute σ (rootTensorEquiv k x) := by
  have h : (rootTensorEquiv k).toLinearMap.comp (tensorPermute σ).toLinearMap =
      (labelledPermute σ).comp (rootTensorEquiv k).toLinearMap := by
    apply (tensorCurrentBasis k).ext
    intro q
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorCurrentBasis_apply,
      tensorPermute_tprod, Function.comp_def, rootTensorEquiv_tprod,
      labelledPermute, TensorProduct.map_tmul, colorPermute_basis]
    congr 1
    change MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (fun i => (q (σ i)).1)) 1 =
        MvPolynomial.rename σ.symm
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun i => (q i).1)) 1)
    rw [MvPolynomial.rename_monomial]
    have he : Finsupp.equivFunOnFinite.symm (fun i => (q (σ i)).1) =
        Finsupp.mapDomain σ.symm (Finsupp.equivFunOnFinite.symm (fun i => (q i).1)) := by
      ext i
      simp [Finsupp.mapDomain_equiv_apply]
    exact congrArg (fun d => MvPolynomial.monomial d (1 : ℂ)) he
  exact LinearMap.congr_fun h x

/-- The invariant labelled-root polynomial family, with its explicit slot action. -/
def invariantLabelled (k : ℕ) : Submodule ℂ (Labelled k) where
  carrier := {x | ∀ σ : Equiv.Perm (Fin k), labelledPermute σ x = x}
  zero_mem' := by simp
  add_mem' hx hy σ := by rw [map_add, hx σ, hy σ]
  smul_mem' c _ hx σ := by rw [map_smul, hx σ]

theorem rootTensorEquiv_mem_invariant (k : ℕ) (x : ⨂[ℂ]^k BGG.Current) :
    rootTensorEquiv k x ∈ invariantLabelled k ↔ x ∈ invariantTensors k := by
  rw [mem_invariantTensors_iff]
  change (∀ σ, labelledPermute σ (rootTensorEquiv k x) = rootTensorEquiv k x) ↔ _
  simp only [← rootTensorEquiv_permute, (rootTensorEquiv k).injective.eq_iff]

/-- The genuine symmetric-power / labelled-root invariant equivalence. -/
def symmetricLabelledEquiv (k : ℕ) : symmetricPower k ≃ₗ[ℂ] invariantLabelled k where
  toFun p := ⟨rootTensorEquiv k (symmetricToTensor k p),
    (rootTensorEquiv_mem_invariant k _).mpr (symmetricToTensor_mem k p)⟩
  invFun x := tensorToSymmetric k ((rootTensorEquiv k).symm x.val)
  left_inv p := by simp
  right_inv x := by
    apply Subtype.ext
    have hx : (rootTensorEquiv k).symm x.val ∈ invariantTensors k := by
      apply (rootTensorEquiv_mem_invariant k _).mp
      rw [LinearEquiv.apply_symm_apply]
      exact x.property
    change rootTensorEquiv k (symmetricToTensor k (tensorToSymmetric k
      ((rootTensorEquiv k).symm x.val))) = x.val
    rw [symmetricToTensor_tensorToSymmetric k _ hx, LinearEquiv.apply_symm_apply]
  map_add' p q := by apply Subtype.ext; simp
  map_smul' c p := by apply Subtype.ext; simp

/-- Every raising coefficient operator becomes multiplication by the corresponding root power sum. -/
theorem symmetricLabelledEquiv_coefficientEnd (m k : ℕ) (p : symmetricPower k) :
    (symmetricLabelledEquiv k (symmetricPowerCoefficientEnd m k p)).val =
      LinearMap.rTensor (Color k)
        (LinearMap.mulLeft ℂ (show RootPolynomial k from MvPolynomial.psum (Fin k) ℂ m))
        (symmetricLabelledEquiv k p).val := by
  change rootTensorEquiv k (symmetricToTensor k
    (symmetricDegreeDeriv k (Modules.coefficientShift m) p)) = _
  rw [symmetricToTensor_symmetricDegreeDeriv, rootTensorEquiv_coefficientShift]
  rfl

end KhanSL2.SymmetricFamily
