module

public import KhanSL2.BGGBridge.ExteriorIso
public import KhanSL2.BGG.PositiveBoundaryAdjoint

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-!
# The CE boundary of `Λ𝔩₊` in the two models

The BGG development defines the boundary `PositiveCE.boundary` of `Λ𝔩₊` as the coefficient
transpose of the positive-current differential `PositiveCE.d`. M2 defines the general CE
boundary `LieChains.boundary` by Cartan's recursion. This file shows that they agree:
* the pure-`c` inclusion intertwines `PositiveCE.boundary` with the project's chain boundary
  (`boundary_inclusion`);
* hence, through `exteriorEquiv`, the M2 boundary on `Λ𝔩₊ ⊗ 1` is `PositiveCE.boundary`
  (`boundary_tmul_one`);
* consequently `PositiveCE.boundary` satisfies Cartan's recursion
  `∂(g ∧ ω) = -ad_g ω - g ∧ ∂ω` (`bdLambda_ι_mul`).
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.BGGBridge

open KhanSL2.BGG KhanSL2.Current KhanSL2.FiniteExterior

/-- Restriction of project cochains to their pure-`c` monomials. -/
def comapC : KhanSL2.Cochain →ₗ[ℂ] PositiveCE.Cochain :=
  Finsupp.lcomapDomain (Finset.map cEmb) (Finset.map_injective cEmb)

@[simp] theorem comapC_apply (u : KhanSL2.Cochain) (t : Finset PositiveCE.Mode) :
    comapC u t = u (t.map cEmb) := rfl

theorem comapC_reindex (v : PositiveCE.Cochain) : comapC (reindex cEmb v) = v := by
  ext t
  rw [comapC_apply]
  exact Finsupp.mapDomain_apply_of_injective (Finset.map_injective cEmb) v t

theorem pairing_reindex (u : KhanSL2.Cochain) (v : PositiveCE.Cochain) :
    coefficientPairing u (reindex cEmb v) = coefficientPairing (comapC u) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single t r =>
    rw [reindex_single, coefficientPairing_symm, coefficientPairing_single,
      coefficientPairing_symm, coefficientPairing_single, comapC_apply]

theorem bCount_map_cEmb (t : Finset PositiveCE.Mode) :
    (∑ m ∈ t.map cEmb, m.bCount) = 0 := by
  rw [Finset.sum_map]
  apply Finset.sum_eq_zero
  intro m _
  rfl

/-- A monomial outside the pure-`c` part contains a `b`-mode. -/
theorem exists_preimage_or_bCount (s : Finset KhanSL2.Mode) :
    (∃ t : Finset PositiveCE.Mode, t.map cEmb = s) ∨ 0 < ∑ m ∈ s, m.bCount := by
  by_cases h : ∀ m ∈ s, m.bCount = 0
  · left
    refine ⟨s.preimage cEmb cEmb.injective.injOn, ?_⟩
    ext m
    simp only [Finset.mem_map, Finset.mem_preimage]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hm
      have hb := h m hm
      cases m with
      | b j a => exact absurd hb (by simp [KhanSL2.Mode.bCount])
      | c j a => exact ⟨⟨j, a⟩, hm, rfl⟩
  · right
    push Not at h
    obtain ⟨m, hm, hb⟩ := h
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero hb) (Finset.single_le_sum (by simp) hm)

theorem comapC_q_single_of_bCount {s : Finset KhanSL2.Mode} (hs : 0 < ∑ m ∈ s, m.bCount) :
    comapC (KhanSL2.q (Finsupp.single s 1)) = 0 := by
  have hq := q_degree (d := monomialDegree s) (Finsupp.single_mem_supported ℂ 1 rfl)
  ext t
  rw [comapC_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  have hdeg : monomialDegree (t.map cEmb) = monomialDegree s + (1, 0, 0) :=
    hq (Finsupp.mem_support_iff.mpr hne)
  simp only [monomialDegree, Prod.mk_add_mk, Prod.mk.injEq, bCount_map_cEmb] at hdeg
  omega

/-- `comapC` intertwines the project's CE differential with the positive one. -/
theorem comapC_q (u : KhanSL2.Cochain) : comapC (KhanSL2.q u) = PositiveCE.d (comapC u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]
  | single s r =>
    rcases exists_preimage_or_bCount s with ⟨t, rfl⟩ | hs
    · have h : Finsupp.single (t.map cEmb) r = PositiveCE.inclusion (Finsupp.single t r) := by
        rw [inclusion_eq_reindex, reindex_single]
      rw [h, ← PositiveCE.inclusion_d, inclusion_eq_reindex, inclusion_eq_reindex,
        comapC_reindex, comapC_reindex]
    · have h0 : comapC (Finsupp.single s r) = 0 := by
        ext t
        rw [comapC_apply, Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply, if_neg]
        intro hst
        subst hst
        rw [bCount_map_cEmb] at hs
        exact lt_irrefl 0 hs
      have hr : Finsupp.single s r = r • Finsupp.single s (1 : ℂ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [h0, map_zero, hr, map_smul, map_smul, comapC_q_single_of_bCount hs, smul_zero]

/-- **The pure-`c` inclusion intertwines the two chain boundaries.** -/
theorem boundary_inclusion (ω : PositiveCE.Cochain) :
    KhanSL2.boundary (PositiveCE.inclusion ω) =
      PositiveCE.inclusion (PositiveCE.boundary ω) := by
  apply chain_ext
  intro u
  rw [← pairing_q, inclusion_eq_reindex, inclusion_eq_reindex]
  change coefficientPairing (KhanSL2.q u) (reindex cEmb ω) =
    coefficientPairing u (reindex cEmb (PositiveCE.boundary ω))
  rw [pairing_reindex, pairing_reindex, comapC_q, coefficientPairing_symm _ (PositiveCE.boundary ω),
    PositiveCE.boundary_pairing, coefficientPairing_symm]

/-! ## The boundary on `Λ𝔩₊` -/

/-- `PositiveCE.boundary`, transported to `Λ𝔩₊`. -/
def bdLambda : Module.End ℂ (ExteriorAlgebra ℂ plus) :=
  exteriorEquiv.symm.toLinearMap ∘ₗ PositiveCE.boundary ∘ₗ exteriorEquiv.toLinearMap

theorem exteriorEquiv_bdLambda (ξ : ExteriorAlgebra ℂ plus) :
    exteriorEquiv (bdLambda ξ) = PositiveCE.boundary (exteriorEquiv ξ) := by
  simp only [bdLambda, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.apply_symm_apply]

theorem PhiB_one : PhiB (1 : NB) = 1 := map_one PhiB

/-- **On trivial coefficients, the M2 boundary is the BGG boundary.** -/
theorem boundary_tmul_one (ξ : ExteriorAlgebra ℂ plus) :
    LieChains.boundary NB (ξ ⊗ₜ (1 : NB)) = bdLambda ξ ⊗ₜ (1 : NB) := by
  apply Phi_injective
  rw [Phi_boundary, Phi_tmul, Phi_tmul, PhiB_one, mul_one, mul_one,
    ← inclusion_exteriorEquiv, ← inclusion_exteriorEquiv, boundary_inclusion,
    exteriorEquiv_bdLambda]

/-- `x ↦ x ⊗ 1` is injective. -/
theorem tmul_one_injective :
    Function.Injective fun ξ : ExteriorAlgebra ℂ plus => ξ ⊗ₜ[ℂ] (1 : NB) := by
  let f : GenChains →ₗ[ℂ] ExteriorAlgebra ℂ plus :=
    (TensorProduct.rid ℂ (ExteriorAlgebra ℂ plus)).toLinearMap ∘ₗ
      LinearMap.lTensor (ExteriorAlgebra ℂ plus) (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Cur)).toLinearMap
  intro ξ η h
  have hf : ∀ x : ExteriorAlgebra ℂ plus, f (x ⊗ₜ (1 : NB)) = x := by
    intro x
    simp [f]
  rw [← hf ξ, ← hf η]
  exact congrArg f h

theorem toEnd_plus_NB_one (y : plus) : LieModule.toEnd ℂ plus NB y (1 : NB) = 0 := by
  change LieChains.derivExt (adCur (y : Cur)) 1 = 0
  exact LieChains.derivExt_one _

/-- **Cartan's recursion for the boundary of `Λ𝔩₊`.** -/
theorem bdLambda_ι_mul (y : plus) (ξ : ExteriorAlgebra ℂ plus) :
    bdLambda (ExteriorAlgebra.ι ℂ y * ξ) =
      -LieChains.derivExt (LieModule.toEnd ℂ plus plus y) ξ - ExteriorAlgebra.ι ℂ y * bdLambda ξ := by
  apply tmul_one_injective
  have h := LieChains.boundary_wedgeLeft (M := NB) y (ξ ⊗ₜ (1 : NB))
  simp only [LieChains.wedgeLeft_tmul, boundary_tmul_one] at h
  simp only [h, LieChains.theta, LieChains.lieDeriv_tmul, toEnd_plus_NB_one,
    TensorProduct.tmul_zero, add_zero, TensorProduct.sub_tmul, TensorProduct.neg_tmul]

end KhanSL2.BGGBridge
