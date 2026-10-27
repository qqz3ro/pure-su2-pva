module

public import KhanSL2.BGGBridge.ChainIso
public import KhanSL2.BGG.ExteriorEuler
public import KhanSL2.BGG.CurrentScaling
public import KhanSL2.BGG.PositiveEnergyScale
public import KhanSL2.Chains.Grading

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The trigrading in the BGG model

On `PositiveCE.Cochain ⊗ Λ(ε𝔩)`, the form degree, coefficient degree, spin and energy
dilation are all diagonal in the tensor basis
`β (s, t) = monomial s ⊗ curBasisLex.ExteriorAlgebra t`. `J` carries M2's grading operators
`formDegree`, `coeffDegree`, `spin` to these.

The dilation of `Λ(ε𝔩)` (`dilN`, spin as a power of 2) is compatible with the right action of
`U(𝔩₊)`, and the coefficient degree commutes with it.
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.BGGBridge

open KhanSL2.BGG KhanSL2.Current KhanSL2.FiniteExterior

/-! ## Transport of derivations to the BGG model -/

theorem exteriorEquiv_derivExt (D : Module.End ℂ plus) (w : PositiveCE.Mode → ℂ)
    (hD : ∀ m, D (plusModeBasis m) = w m • plusModeBasis m) (ξ : ExteriorAlgebra ℂ plus) :
    exteriorEquiv (LieChains.derivExt D ξ) = euler w (exteriorEquiv ξ) := by
  have hgen : (exteriorEquiv.toLinearMap ∘ₗ ExteriorAlgebra.ι ℂ ∘ₗ D) =
      (euler w ∘ₗ exteriorEquiv.toLinearMap ∘ₗ ExteriorAlgebra.ι ℂ) := by
    apply plusModeBasis.ext
    intro m
    change toE (ExteriorAlgebra.ι ℂ (D (plusModeBasis m))) =
      euler w (toE (ExteriorAlgebra.ι ℂ (plusModeBasis m)))
    rw [toE_ι, toE_ι, hD, LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one, generatorLinear_single, generatorLinear_single, one_smul,
      euler_generator]
  induction ξ using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [LieChains.derivExt_algebraMap, map_zero, AlgEquiv.commutes,
      Algebra.algebraMap_eq_smul_one, map_smul, euler_one, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x y hx =>
    have h1 := LinearMap.congr_fun hgen y
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply] at h1
    change exteriorEquiv (LieChains.derivExt D (ExteriorAlgebra.ι ℂ y * x)) =
      euler w (exteriorEquiv (ExteriorAlgebra.ι ℂ y * x))
    rw [LieChains.derivExt_ι_mul, map_add, E_mul, E_mul, h1, hx, E_mul, euler_mul]

/-- The form-degree weight of positive modes. -/
def formW (_ : PositiveCE.Mode) : ℂ := 1

/-- The spin of positive modes: `z^{j+1}` has spin `j + 1`. -/
def energyW (m : PositiveCE.Mode) : ℂ := ((m.index + 1 : ℕ) : ℂ)

theorem one_plusModeBasis (m : PositiveCE.Mode) :
    (1 : Module.End ℂ plus) (plusModeBasis m) = formW m • plusModeBasis m := by
  rw [Module.End.one_apply, formW, one_smul]

theorem eulerPlus_plusModeBasis (m : PositiveCE.Mode) :
    eulerPlus (plusModeBasis m) = energyW m • plusModeBasis m := by
  rw [plusModeBasis_apply, eulerPlus_plusCur]
  rfl

/-! ## Grading operators in the BGG model -/

/-- Form degree on `PositiveCE.Cochain ⊗ Λ(ε𝔩)`. -/
def numC : Module.End ℂ (ChainN NB) := LinearMap.rTensor NB (euler formW)

/-- Coefficient degree on `PositiveCE.Cochain ⊗ Λ(ε𝔩)`. -/
def numB : Module.End ℂ (ChainN NB) :=
  LinearMap.lTensor PositiveCE.Cochain (LieChains.derivExt (1 : Module.End ℂ Cur))

/-- Spin on `PositiveCE.Cochain ⊗ Λ(ε𝔩)`. -/
def spinC : Module.End ℂ (ChainN NB) := diag (euler energyW) (LieChains.derivExt eulerCoeff)

set_option maxHeartbeats 1000000 in
theorem J_formDegree (ξ : GenChains) : J (formDegree ξ) = numC (J ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul x ν =>
    have h1 : formDegree (x ⊗ₜ ν) = LieChains.derivExt 1 x ⊗ₜ ν + x ⊗ₜ (0 : Module.End ℂ NB) ν :=
      rfl
    rw [h1, LinearMap.zero_apply, TensorProduct.tmul_zero, add_zero, J_tmul, J_tmul, numC,
      LinearMap.rTensor_tmul, exteriorEquiv_derivExt 1 formW one_plusModeBasis]
  | add ξ η hξ hη => simp only [map_add, hξ, hη]

set_option maxHeartbeats 1000000 in
theorem J_coeffDegree (ξ : GenChains) : J (coeffDegree ξ) = numB (J ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul x ν =>
    have h1 : coeffDegree (x ⊗ₜ ν) =
        LieChains.derivExt 0 x ⊗ₜ ν + x ⊗ₜ LieChains.derivExt (1 : Module.End ℂ Cur) ν := rfl
    rw [h1, LieChains.derivExt_zero_apply, TensorProduct.zero_tmul, zero_add, J_tmul, J_tmul,
      numB, LinearMap.lTensor_tmul]
  | add ξ η hξ hη => simp only [map_add, hξ, hη]

set_option maxHeartbeats 1000000 in
theorem J_spin (ξ : GenChains) : J (spin ξ) = spinC (J ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul x ν =>
    have h1 : spin (x ⊗ₜ ν) =
        LieChains.derivExt eulerPlus x ⊗ₜ ν + x ⊗ₜ LieChains.derivExt eulerCoeff ν := rfl
    rw [h1, map_add, J_tmul, J_tmul, J_tmul, spinC, diag_tmul,
      exteriorEquiv_derivExt eulerPlus energyW eulerPlus_plusModeBasis]
  | add ξ η hξ hη => simp only [map_add, hξ, hη]

/-! ## The dilation of `Λ(ε𝔩)` -/

/-- Spin dilation on `𝔩 = 𝔤[z]`, with `ε` of spin one: `z^n t ↦ 2^{n+1} z^n t`. -/
def scaleCur : Module.End ℂ Cur := (2 : ℂ) • (currentScale 2 : Current →ₗ⁅ℂ⁆ Current).toLinearMap

theorem scaleCur_cur (n : ℕ) (a : Fin 3) : scaleCur (cur n a) = (2 : ℂ) ^ (n + 1) • cur n a := by
  rw [scaleCur, LinearMap.smul_apply, LieHom.coe_toLinearMap]
  change (2 : ℂ) • currentScale 2 (mode n (MatrixSL2.color a)) = _
  rw [currentScale_mode, smul_smul, pow_succ, mul_comm]
  rfl

/-- Spin dilation on `Λ(ε𝔩)`. -/
def dilN : Module.End ℂ NB := (ExteriorAlgebra.map scaleCur).toLinearMap

theorem scaleCur_lie (y c : Current) :
    scaleCur ⁅y, c⁆ = ⁅currentScale 2 y, scaleCur c⁆ := by
  simp only [scaleCur, LinearMap.smul_apply, LieHom.coe_toLinearMap, LieHom.map_lie]
  change (2 : ℂ) • ⁅currentScale 2 y, currentScale 2 c⁆ =
    LieModule.toEnd ℂ Current Current (currentScale 2 y) ((2 : ℂ) • currentScale 2 c)
  rw [map_smul]
  rfl

/-- An algebra map induced by `g` intertwines derivation extensions of intertwined maps. -/
theorem map_derivExt {L L' : Type*} [AddCommGroup L] [Module ℂ L] [AddCommGroup L']
    [Module ℂ L'] (g : L →ₗ[ℂ] L') (D : Module.End ℂ L) (D' : Module.End ℂ L')
    (h : ∀ y, g (D y) = D' (g y)) (x : ExteriorAlgebra ℂ L) :
    ExteriorAlgebra.map g (LieChains.derivExt D x) = LieChains.derivExt D' (ExteriorAlgebra.map g x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => rw [LieChains.derivExt_algebraMap, map_zero, AlgHom.commutes,
      LieChains.derivExt_algebraMap]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x y hx =>
    rw [LieChains.derivExt_ι_mul, map_add, map_mul, map_mul, ExteriorAlgebra.map_apply_ι,
      ExteriorAlgebra.map_apply_ι, h, hx, map_mul, ExteriorAlgebra.map_apply_ι,
      LieChains.derivExt_ι_mul]

theorem dilN_lie (y : Current) (ν : NB) :
    dilN ⁅y, ν⁆ = ⁅currentScale 2 y, dilN ν⁆ := by
  change ExteriorAlgebra.map scaleCur (LieChains.derivExt (adCur y) ν) =
    LieChains.derivExt (adCur (currentScale 2 y)) (ExteriorAlgebra.map scaleCur ν)
  exact map_derivExt scaleCur _ _ (fun c => scaleCur_lie y c) ν

theorem positiveUEScale_ι (y : positive) :
    positiveUEScale (UniversalEnvelopingAlgebra.ι ℂ y) =
      UniversalEnvelopingAlgebra.ι ℂ (positiveScale 2 y) := by
  rw [positiveUEScale, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- **The spin dilation of `Λ(ε𝔩)` is compatible with the right action.** -/
theorem dilN_ract (u : PositiveEnveloping) (ν : NB) :
    dilN (ract (rightAction NB) u ν) = ract (rightAction NB) (positiveUEScale u) (dilN ν) := by
  revert ν
  refine positiveUE_induction (P := fun u => ∀ ν : NB,
    dilN (ract (rightAction NB) u ν) = ract (rightAction NB) (positiveUEScale u) (dilN ν))
    ?_ ?_ ?_ ?_ u
  · intro y ν
    rw [ract_ι, positiveUEScale_ι, ract_ι, map_neg, dilN_lie, positiveScale_coe]
  · intro r ν
    rw [ract_algebraMap, AlgHom.commutes, ract_algebraMap, map_smul]
  · intro a b ha hb ν
    rw [ract_add, LinearMap.add_apply, map_add, ha, hb, map_add, ract_add, LinearMap.add_apply]
  · intro a b ha hb ν
    rw [ract_mul_apply, hb, ha, map_mul, ract_mul_apply]

/-- The coefficient degree commutes with the positive currents. -/
theorem numB_lie (y : positive) (ν : NB) :
    LieChains.derivExt (1 : Module.End ℂ Cur) ⁅(y : Current), ν⁆ =
      ⁅(y : Current), LieChains.derivExt (1 : Module.End ℂ Cur) ν⁆ := by
  change LieChains.derivExt 1 (LieChains.derivExt (adCur (y : Cur)) ν) =
    LieChains.derivExt (adCur (y : Cur)) (LieChains.derivExt 1 ν)
  have hX : (1 : Module.End ℂ Cur) * adCur (y : Cur) - adCur (y : Cur) * 1 = 0 := by
    apply LinearMap.ext
    intro c
    simp
  rw [← sub_eq_zero, LieChains.derivExt_commutator, hX, LieChains.derivExt_zero_apply]

theorem numB_ract (u : PositiveEnveloping) (ν : NB) :
    LieChains.derivExt (1 : Module.End ℂ Cur) (ract (rightAction NB) u ν) =
      ract (rightAction NB) u (LieChains.derivExt (1 : Module.End ℂ Cur) ν) :=
  ract_commute NB numB_lie u ν

/-! ## The tensor basis and its eigenvalues -/

/-- The tensor basis of `PositiveCE.Cochain ⊗ Λ(ε𝔩)`. -/
def betaBasis : Module.Basis (Finset PositiveCE.Mode × Finset Idx) ℂ (ChainN NB) :=
  (Finsupp.basisSingleOne : Module.Basis (Finset PositiveCE.Mode) ℂ PositiveCE.Cochain).tensorProduct
    curBasisLex.ExteriorAlgebra

theorem betaBasis_apply (s : Finset PositiveCE.Mode) (t : Finset Idx) :
    betaBasis (s, t) = FiniteExterior.monomial s ⊗ₜ curBasisLex.ExteriorAlgebra t := by
  rw [betaBasis, Module.Basis.tensorProduct_apply, Finsupp.coe_basisSingleOne]
  rfl

theorem prod_univ_map_orderEmb {I : Type*} [LinearOrder I] {n : ℕ} (μ : I → ℂ)
    (u : Set.powersetCard I n) :
    ∏ j : Fin n, μ (Set.powersetCard.ofFinEmbEquiv.symm u j) = ∏ i ∈ u.val, μ i := by
  have h : Finset.univ.map (Set.powersetCard.ofFinEmbEquiv.symm u).toEmbedding = u.val := by
    ext p
    simp only [Finset.mem_map, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    exact Set.mem_range.symm.trans (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem u p)
  rw [← h, Finset.prod_map]
  rfl

theorem map_list_prod_smul {I : Type*} (v : I → Cur) (g : Module.End ℂ Cur) (μ : I → ℂ)
    (hg : ∀ i, g (v i) = μ i • v i) (l : List I) :
    ExteriorAlgebra.map g (l.map fun i => ExteriorAlgebra.ι ℂ (v i)).prod =
      (l.map μ).prod • (l.map fun i => ExteriorAlgebra.ι ℂ (v i)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [map_mul, ExteriorAlgebra.map_apply_ι, hg, ih, map_smul, smul_mul_assoc, mul_smul_comm,
      smul_smul]

/-- An algebra map induced by a diagonal map is diagonal on monomials. -/
theorem map_basis (g : Module.End ℂ Cur) (μ : Idx → ℂ) (hg : ∀ q, g (curBasisLex q) = μ q • curBasisLex q)
    (t : Finset Idx) :
    ExteriorAlgebra.map g (curBasisLex.ExteriorAlgebra t) =
      (∏ q ∈ t, μ q) • curBasisLex.ExteriorAlgebra t := by
  rw [ExteriorAlgebra.basis_apply_ofCard curBasisLex (rfl : t.card = t.card)]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply, Function.comp_def]
  have hl := map_list_prod_smul curBasisLex g μ hg
    (List.ofFn fun j => Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard
      (rfl : t.card = t.card)) j)
  simp only [List.map_ofFn, Function.comp_def] at hl
  rw [hl, List.prod_ofFn, prod_univ_map_orderEmb]
  rfl

theorem scaleCur_basis (q : Idx) :
    scaleCur (curBasisLex q) = ((2 : ℂ) ^ idxSpin q) • curBasisLex q := by
  rw [curBasisLex_apply, scaleCur_cur]
  rfl

theorem dilN_basis (t : Finset Idx) :
    dilN (curBasisLex.ExteriorAlgebra t) =
      ((2 : ℂ) ^ idxWeight t) • curBasisLex.ExteriorAlgebra t := by
  change ExteriorAlgebra.map scaleCur _ = _
  rw [map_basis scaleCur (fun q => (2 : ℂ) ^ idxSpin q) scaleCur_basis, Finset.prod_pow_eq_pow_sum,
    idxWeight]

/-- Spin dilation on `PositiveCE.Cochain ⊗ Λ(ε𝔩)`. -/
def dilC : Module.End ℂ (ChainN NB) := TensorProduct.map PositiveCE.energyScale dilN

theorem numC_beta (i : Finset PositiveCE.Mode × Finset Idx) :
    numC (betaBasis i) = (i.1.card : ℂ) • betaBasis i := by
  obtain ⟨s, t⟩ := i
  rw [betaBasis_apply, numC, LinearMap.rTensor_tmul, euler_monomial, TensorProduct.smul_tmul']
  simp [formW]

theorem numB_beta (i : Finset PositiveCE.Mode × Finset Idx) :
    numB (betaBasis i) = (i.2.card : ℂ) • betaBasis i := by
  obtain ⟨s, t⟩ := i
  rw [betaBasis_apply, numB, LinearMap.lTensor_tmul, LieChains.derivExt_one_basis,
    TensorProduct.tmul_smul]

theorem spinC_beta (i : Finset PositiveCE.Mode × Finset Idx) :
    spinC (betaBasis i) =
      ((PositiveCE.monomialEnergy i.1 + idxWeight i.2 : ℕ) : ℂ) • betaBasis i := by
  obtain ⟨s, t⟩ := i
  have h1 : (∑ a ∈ s, energyW a) = ((PositiveCE.monomialEnergy s : ℕ) : ℂ) := by
    simp [energyW, PositiveCE.monomialEnergy]
  have h2 : (∑ q ∈ t, (idxSpin q : ℂ)) = ((idxWeight t : ℕ) : ℂ) := by
    simp [idxWeight]
  rw [betaBasis_apply, spinC, diag_tmul, euler_monomial, h1,
    LieChains.derivExt_basis curBasisLex eulerCoeff (fun q => (idxSpin q : ℂ)) eulerCoeff_basis,
    h2, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', ← add_smul]
  push_cast
  rfl

theorem dilC_beta (i : Finset PositiveCE.Mode × Finset Idx) :
    dilC (betaBasis i) =
      ((2 : ℂ) ^ (((PositiveCE.monomialEnergy i.1 + idxWeight i.2 : ℕ) : ℤ))) • betaBasis i := by
  obtain ⟨s, t⟩ := i
  rw [betaBasis_apply, dilC, TensorProduct.map_tmul, PositiveCE.energyScale_monomial, dilN_basis]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  congr 2
  rw [zpow_natCast, pow_add, mul_comm]

end KhanSL2.BGGBridge
