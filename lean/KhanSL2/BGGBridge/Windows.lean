module

public import KhanSL2.BGGBridge.GradingOps
public import KhanSL2.DictionaryStatement
public import KhanSL2.BGG.ContractionDegreeHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# `K p B S` is computed by the BGG complex

The degree `(p, B, S)` pieces on the two sides of the transferred BGG contraction:
* on chains, `degWin p B S`: form degree `p`, coefficient degree `B` and spin `S`. `J` carries
  M2's `genPiece (kDegree p B S)` onto it.
* on harmonic chains, `harmWin p B S`: harmonic degree `p` (a copy of `V(2p)`), coefficient
  degree `B` and spin `S`.

All contraction maps respect these pieces; the homotopy raises `p` by one. So
`degreeHomologyEquiv` gives `K p B S ≃ H_p` of the BGG complex in coefficient degree `B` and
spin `S` (`kEquivBGG`).
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.BGGBridge

open KhanSL2.BGG KhanSL2.Current KhanSL2.FiniteExterior

/-! ## Support conditions in the tensor basis -/

/-- The index condition of the piece `(p, B, S)`. -/
def IdxCond (p B : ℕ) (S : ℤ) (i : Finset PositiveCE.Mode × Finset Idx) : Prop :=
  i.1.card = p ∧ i.2.card = B ∧ ((PositiveCE.monomialEnergy i.1 + idxWeight i.2 : ℕ) : ℤ) = S

theorem eigen_numC_iff (p : ℕ) (z : ChainN NB) :
    numC z = (p : ℂ) • z ↔ ∀ i, betaBasis.repr z i ≠ 0 → i.1.card = p := by
  rw [betaBasis.apply_eq_smul_iff_of_diagonal numC _ numC_beta]
  exact forall_congr' fun _ => imp_congr_right fun _ => Nat.cast_inj

theorem eigen_numB_iff (B : ℕ) (z : ChainN NB) :
    numB z = (B : ℂ) • z ↔ ∀ i, betaBasis.repr z i ≠ 0 → i.2.card = B := by
  rw [betaBasis.apply_eq_smul_iff_of_diagonal numB _ numB_beta]
  exact forall_congr' fun _ => imp_congr_right fun _ => Nat.cast_inj

theorem natCast_eq_intCast_iff (n : ℕ) (S : ℤ) : ((n : ℂ) = (S : ℂ)) ↔ (n : ℤ) = S := by
  rw [← Int.cast_natCast, Int.cast_inj]

theorem eigen_spinC_iff (S : ℤ) (z : ChainN NB) :
    spinC z = (S : ℂ) • z ↔ ∀ i, betaBasis.repr z i ≠ 0 →
      ((PositiveCE.monomialEnergy i.1 + idxWeight i.2 : ℕ) : ℤ) = S := by
  rw [betaBasis.apply_eq_smul_iff_of_diagonal spinC _ spinC_beta]
  exact forall_congr' fun _ => imp_congr_right fun _ => natCast_eq_intCast_iff _ S

theorem eigen_dilC_iff (S : ℤ) (z : ChainN NB) :
    dilC z = ((2 : ℂ) ^ S) • z ↔ ∀ i, betaBasis.repr z i ≠ 0 →
      ((PositiveCE.monomialEnergy i.1 + idxWeight i.2 : ℕ) : ℤ) = S := by
  rw [betaBasis.apply_eq_smul_iff_of_diagonal dilC _ dilC_beta]
  exact forall_congr' fun _ => imp_congr_right fun _ => energyEigenvalue_injective.eq_iff

theorem euler_formW_of_mem {p : ℕ} {a : PositiveCE.Cochain} (ha : a ∈ degC p) :
    euler formW a = (p : ℂ) • a := by
  rw [degC, Finsupp.supported_eq_span_single] at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    change euler formW (FiniteExterior.monomial s) = (p : ℂ) • FiniteExterior.monomial s
    rw [euler_monomial]
    simp only [formW, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [show s.card = p from hs]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

theorem mem_tensorLeft_degC_iff (p : ℕ) (z : ChainN NB) :
    z ∈ tensorLeft (degC p) ↔ ∀ i, betaBasis.repr z i ≠ 0 → i.1.card = p := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← eigen_numC_iff]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a n =>
      rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, numC, LinearMap.rTensor_tmul,
        euler_formW_of_mem a.property, TensorProduct.smul_tmul']
    | add y w hy hw => rw [map_add, map_add, hy, hw, smul_add]
  · intro h
    rw [← betaBasis.linearCombination_repr z, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    obtain ⟨s, t⟩ := i
    rw [betaBasis_apply]
    exact tmul_mem_tensorLeft (Finsupp.single_mem_supported ℂ 1
      (show s.card = p from h (s, t) (Finsupp.mem_support_iff.mp hi))) _

/-- Form degree `p`, coefficient degree `B`, spin `S` on `Λ𝔩₊ ⊗ Λ(ε𝔩)` (BGG model). -/
def degWin (p B : ℕ) (S : ℤ) : Submodule ℂ (ChainN NB) :=
  tensorLeft (degC p) ⊓ Module.End.eigenspace numB (B : ℂ) ⊓
    Module.End.eigenspace dilC ((2 : ℂ) ^ S)

theorem mem_degWin_iff (p B : ℕ) (S : ℤ) (z : ChainN NB) :
    z ∈ degWin p B S ↔ ∀ i, betaBasis.repr z i ≠ 0 → IdxCond p B S i := by
  simp only [degWin, Submodule.mem_inf, Module.End.mem_eigenspace_iff, mem_tensorLeft_degC_iff,
    eigen_numB_iff, eigen_dilC_iff, IdxCond]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ i hi
    exact ⟨h1 i hi, h2 i hi, h3 i hi⟩
  · intro h
    exact ⟨⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2.1⟩, fun i hi => (h i hi).2.2⟩

theorem J_smul (c : ℂ) (ξ : GenChains) : J (c • ξ) = c • J ξ := map_smul J c ξ

/-- **`J` carries M2's degree pieces onto the BGG-model pieces.** -/
theorem mem_genPiece_iff_J (p B : ℕ) (S : ℤ) (ξ : GenChains) :
    ξ ∈ genPiece (kDegree p B S) ↔ J ξ ∈ degWin p B S := by
  rw [mem_kPiece_iff, mem_degWin_iff]
  have e1 : formDegree ξ = (p : ℂ) • ξ ↔ numC (J ξ) = (p : ℂ) • J ξ := by
    rw [← J_formDegree, ← J_smul, J.injective.eq_iff]
  have e2 : coeffDegree ξ = (B : ℂ) • ξ ↔ numB (J ξ) = (B : ℂ) • J ξ := by
    rw [← J_coeffDegree, ← J_smul, J.injective.eq_iff]
  have e3 : spin ξ = (S : ℂ) • ξ ↔ spinC (J ξ) = (S : ℂ) • J ξ := by
    rw [← J_spin, ← J_smul, J.injective.eq_iff]
  rw [e1, e2, e3, eigen_numC_iff, eigen_numB_iff, eigen_spinC_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩ i hi
    exact ⟨h1 i hi, h2 i hi, h3 i hi⟩
  · intro h
    exact ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2.1, fun i hi => (h i hi).2.2⟩

/-! ## Harmonic pieces -/

/-- Coefficient degree on harmonic chains. -/
def numBH : Module.End ℂ (HarmN NB) :=
  LinearMap.lTensor PositiveCE.Harmonic (LieChains.derivExt (1 : Module.End ℂ Cur))

/-- Spin dilation on harmonic chains. -/
def dilH : Module.End ℂ (HarmN NB) := TensorProduct.map PositiveCE.harmonicEnergyScale dilN

/-- Harmonic degree `p` (a copy of `V(2p)`), coefficient degree `B`, spin `S`. -/
def harmWin (p B : ℕ) (S : ℤ) : Submodule ℂ (HarmN NB) :=
  tensorLeft (degH p) ⊓ Module.End.eigenspace numBH (B : ℂ) ⊓
    Module.End.eigenspace dilH ((2 : ℂ) ^ S)

/-! ## The contraction respects the pieces -/

theorem mem_eigenspace_map {P Q : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q]
    [Module ℂ Q] {T : Module.End ℂ P} {T' : Module.End ℂ Q} (f : P →ₗ[ℂ] Q)
    (hf : ∀ z, f (T z) = T' (f z)) {c : ℂ} {z : P} (hz : z ∈ Module.End.eigenspace T c) :
    f z ∈ Module.End.eigenspace T' c := by
  rw [Module.End.mem_eigenspace_iff] at hz ⊢
  rw [← hf, hz, map_smul]

theorem dilN_ract' (u : PositiveEnveloping) (ν : NB) :
    dilN (ract (rightAction NB) u ν) =
      ract (rightAction NB) (positiveUEScale.toLinearMap u) (dilN ν) :=
  dilN_ract u ν

theorem positiveUEScale_one' : positiveUEScale.toLinearMap (1 : PositiveEnveloping) = 1 :=
  map_one positiveUEScale

theorem homotopy_totalEnergyScale (u : FreeCE.Chain) :
    FreeCE.totalEnergyScale (PositiveTransfer.contraction.homotopy u) =
      PositiveTransfer.contraction.homotopy (FreeCE.totalEnergyScale u) := by
  rw [PositiveTransfer.contraction_homotopy_apply, PositiveTransfer.contraction_homotopy_apply,
    map_sub, PositiveTransfer.totalEnergyScale_baseHomotopy,
    PositiveTransfer.totalEnergyScale_baseHomotopy, PositiveTransfer.totalEnergyScale_series,
    PositiveTransfer.totalEnergyScale_baseHomotopy]

theorem incl_mem_win {p B : ℕ} {S : ℤ} {z : HarmN NB} (hz : z ∈ harmWin p B S) :
    (cN NB).incl z ∈ degWin p B S := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hz
  refine ⟨⟨incl_mem_degree NB h1, ?_⟩, ?_⟩
  · exact mem_eigenspace_map ((cN NB).incl) (fun z =>
      base_lTensor (rightAction NB) numB_ract PositiveTransfer.contraction.incl z) h2
  · exact mem_eigenspace_map ((cN NB).incl) (fun z =>
      base_map_map (rightAction NB) positiveUEScale_one' dilN_ract'
        PositiveTransfer.contraction.incl
        (fun t => (PositiveTransfer.totalEnergyScale_incl t).symm) z) h3

theorem proj_mem_win {p B : ℕ} {S : ℤ} {z : ChainN NB} (hz : z ∈ degWin p B S) :
    (cN NB).proj z ∈ harmWin p B S := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hz
  refine ⟨⟨proj_mem_degree NB h1, ?_⟩, ?_⟩
  · exact mem_eigenspace_map ((cN NB).proj) (fun z =>
      base_lTensor (rightAction NB) numB_ract PositiveTransfer.contraction.proj z) h2
  · exact mem_eigenspace_map ((cN NB).proj) (fun z =>
      base_map_map (rightAction NB) positiveUEScale_one' dilN_ract'
        PositiveTransfer.contraction.proj
        (fun t => (PositiveTransfer.totalEnergyScale_proj t).symm) z) h3

theorem homotopy_mem_win {p B : ℕ} {S : ℤ} {z : ChainN NB} (hz : z ∈ degWin p B S) :
    (cN NB).homotopy z ∈ degWin (p + 1) B S := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hz
  refine ⟨⟨homotopy_mem_degree NB h1, ?_⟩, ?_⟩
  · exact mem_eigenspace_map ((cN NB).homotopy) (fun z =>
      base_lTensor (rightAction NB) numB_ract PositiveTransfer.contraction.homotopy z) h2
  · exact mem_eigenspace_map ((cN NB).homotopy) (fun z =>
      base_map_map (rightAction NB) positiveUEScale_one' dilN_ract'
        PositiveTransfer.contraction.homotopy
        (fun t => (homotopy_totalEnergyScale t).symm) z) h3

theorem dH_mem_win {p B : ℕ} {S : ℤ} {z : HarmN NB} (hz : z ∈ harmWin (p + 1) B S) :
    dH NB z ∈ harmWin p B S := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hz
  refine ⟨⟨dH_mem_degree NB h1, ?_⟩, ?_⟩
  · exact mem_eigenspace_map (dH NB) (fun z =>
      base_lTensor (rightAction NB) numB_ract PositiveTransfer.differential z) h2
  · exact mem_eigenspace_map (dH NB) (fun z =>
      base_map_map (rightAction NB) positiveUEScale_one' dilN_ract'
        PositiveTransfer.differential
        (fun t => (PositiveTransfer.totalEnergyScale_differential t).symm) z) h3

/-! ## The BGG complex in degree `(p, B, S)` -/

theorem dC_comp_dC : (dC NB).comp (dC NB) = 0 := by
  rw [dC, ← base_comp]
  have h : FreeCE.differential.comp FreeCE.differential = 0 :=
    LinearMap.ext fun u => FreeCE.differential_square_zero u
  rw [h, base_zero]

theorem dCq_comp_dCq : (dCq NB).comp (dCq NB) = 0 := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro z
  have h := LinearMap.congr_fun (dC_comp_dC) z
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  change Submodule.Quotient.mk (dC NB (dC NB z)) = (0 : ChainN NB ⧸ relC NB)
  rw [h, Submodule.Quotient.mk_zero]

theorem dHq_comp_dHq : (dHq NB).comp (dHq NB) = 0 :=
  (qcN NB).dN_comp_dN_eq_zero (dCq_comp_dCq)

/-- The BGG terms in degree `(p, B, S)`, modulo the `𝔤`-relations. -/
def bggTerm (p B : ℕ) (S : ℤ) : Submodule ℂ (HarmN NB ⧸ relH NB) :=
  (harmWin p B S).map (relH NB).mkQ

/-- The BGG complex around degree `p`, at coefficient degree `B` and spin `S`. -/
def bggWindow (p B : ℕ) (S : ℤ) : Contraction.DegreeWindow (dHq NB) where
  current := bggTerm p B S
  previous := bggTerm (p + 1) B S
  differential_mem := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨dH NB z, dH_mem_win hz, rfl⟩

/-- **The homology of the BGG complex** in degree `p`, coefficient degree `B` and spin `S`. -/
abbrev BGGHomology (p B : ℕ) (S : ℤ) : Type :=
  (bggWindow p B S).homology (dHq_comp_dHq)

theorem relBoundary_comp_self : relBoundary.comp relBoundary = 0 :=
  LinearMap.ext fun x => relBoundary_relBoundary x

theorem kDegree_succ (p B : ℕ) (S : ℤ) : kDegree p B S + (1, 0, 0) = kDegree (p + 1) B S := by
  simp only [kDegree, Prod.mk_add_mk, add_zero, Prod.mk.injEq, and_true]
  push_cast
  ring

/-- M2's relative complex around degree `(p, B, S)`. -/
def kWindow (p B : ℕ) (S : ℤ) : Contraction.DegreeWindow relBoundary where
  current := relPiece (kDegree p B S)
  previous := relPiece (kDegree p B S + (1, 0, 0))
  differential_mem := by
    rintro _ ⟨ξ, hξ, rfl⟩
    exact ⟨LieChains.boundary NB ξ, boundary_mem_genPiece hξ, rfl⟩

/-- The BGG contraction on M2's relative complex. -/
def relContraction : TauCeti.LinearSpecialContraction (M := RelChains) (N := HarmN NB ⧸ relH NB)
    relBoundary (dHq NB) :=
  equivContraction Jq (fun x => dCq_Jq x) (qcN NB)

theorem Jq_symm_mk (z : ChainN NB) :
    Jq.symm (Submodule.Quotient.mk z) = (Submodule.Quotient.mk (J.symm z) : RelChains) := rfl

theorem relContraction_incl_mk (z : HarmN NB) :
    relContraction.incl (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk (J.symm ((cN NB).incl z)) : RelChains) := rfl

theorem relContraction_proj_mk (ξ : GenChains) :
    relContraction.proj (Submodule.Quotient.mk ξ) =
      (Submodule.Quotient.mk ((cN NB).proj (J ξ)) : HarmN NB ⧸ relH NB) := rfl

theorem relContraction_homotopy_mk (ξ : GenChains) :
    relContraction.homotopy (Submodule.Quotient.mk ξ) =
      (Submodule.Quotient.mk (J.symm ((cN NB).homotopy (J ξ))) : RelChains) := rfl

theorem incl_mem_relPiece {p B : ℕ} {S : ℤ} {x : HarmN NB ⧸ relH NB} (hx : x ∈ bggTerm p B S) :
    relContraction.incl x ∈ relPiece (kDegree p B S) := by
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨J.symm ((cN NB).incl z), ?_, rfl⟩
  rw [SetLike.mem_coe, mem_genPiece_iff_J, LinearEquiv.apply_symm_apply]
  exact incl_mem_win hz

theorem proj_mem_bggTerm {p B : ℕ} {S : ℤ} {x : RelChains} (hx : x ∈ relPiece (kDegree p B S)) :
    relContraction.proj x ∈ bggTerm p B S := by
  obtain ⟨ξ, hξ, rfl⟩ := hx
  exact ⟨(cN NB).proj (J ξ), proj_mem_win ((mem_genPiece_iff_J p B S ξ).mp hξ), rfl⟩

theorem homotopy_mem_relPiece {p B : ℕ} {S : ℤ} {x : RelChains}
    (hx : x ∈ relPiece (kDegree p B S)) :
    relContraction.homotopy x ∈ relPiece (kDegree (p + 1) B S) := by
  obtain ⟨ξ, hξ, rfl⟩ := hx
  refine ⟨J.symm ((cN NB).homotopy (J ξ)), ?_, rfl⟩
  rw [SetLike.mem_coe, mem_genPiece_iff_J, LinearEquiv.apply_symm_apply]
  exact homotopy_mem_win ((mem_genPiece_iff_J p B S ξ).mp hξ)

/-- **`K p B S` is the homology of the BGG complex** in degree `p`, coefficient degree `B` and
spin `S`. -/
def kEquivBGG (p B : ℕ) (S : ℤ) : K p B S ≃ₗ[ℂ] BGGHomology p B S :=
  Contraction.degreeHomologyEquiv relContraction relBoundary_comp_self (kWindow p B S)
    (bggWindow p B S)
    (fun _ hx => incl_mem_relPiece hx)
    (fun _ hx => proj_mem_bggTerm hx)
    (fun _ hx => by
      change _ ∈ relPiece (kDegree p B S + (1, 0, 0))
      rw [kDegree_succ]
      exact incl_mem_relPiece hx)
    (fun _ hx => by
      change _ ∈ relPiece (kDegree p B S + (1, 0, 0)) at hx
      rw [kDegree_succ] at hx
      exact proj_mem_bggTerm hx)
    (fun _ hx => by
      change _ ∈ relPiece (kDegree p B S + (1, 0, 0))
      rw [kDegree_succ]
      exact homotopy_mem_relPiece hx)

end KhanSL2.BGGBridge
