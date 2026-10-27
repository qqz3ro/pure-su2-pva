module

public import KhanSL2.BGGBridge.Windows
public import KhanSL2.BGG.EquivariantHarmonicDecomposition
public import KhanSL2.BGG.FreeCEAugmentationEquivariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# Trivial coefficients: `K p 0 S`

In coefficient degree `B = 0` the coefficient module is `Λ⁰(ε𝔩) = ℂ`, so the BGG term in degree
`p` is the space of coinvariants `V(2p)_𝔤`, sitting in spin `p(p+1)/2`.
* For `p ≥ 1`, `V(2p)` is irreducible and nontrivial, so it is spanned by the vectors `x · v`
  and its coinvariants vanish (`bggTerm_eq_bot_of_pos`).
* For `p = 0`, the harmonic degree-zero part is `ℂ · 1` and has energy `0`; the class of
  `1 ⊗ 1` is nonzero because the augmentation `h ⊗ ν ↦ h(∅) · ν₀` kills the relations
  (`bggTerm_zero`, `oneClass_ne_zero`).

Hence `K p 0 S = H_p(𝔩, 𝔤; ℂ)_S` is `ℂ` for `p = S = 0` and zero otherwise
(`finrank_K_trivial`), and through the dictionary the same holds for the restricted relative
cohomology `cohomologyPiece (kDegree p 0 S)` (`finrank_cohomologyPiece_trivial`). Since the class
of `1` is nonzero, the piece of degree `(0, 0, 0)` is spanned by it (`cohomology_B_zero`).
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.BGGBridge

open KhanSL2 KhanSL2.BGG KhanSL2.Current KhanSL2.FiniteExterior

/-! ## Coefficient degree zero -/

/-- The monomial basis of `Λ(ε𝔩)`. -/
abbrev basisN : Module.Basis (Finset Idx) ℂ NB := curBasisLex.ExteriorAlgebra

theorem basisN_empty : basisN ∅ = 1 := by
  rw [ExteriorAlgebra.basis_apply_ofCard curBasisLex (rfl : (∅ : Finset Idx).card = 0)]
  exact ExteriorAlgebra.ιMulti_zero_apply _

/-- A partial inverse of the coefficient-degree operator. -/
def invN : Module.End ℂ NB := basisN.constr ℂ fun t => ((t.card : ℂ)⁻¹) • basisN t

theorem invN_derivExt_add (ν : NB) :
    invN (LieChains.derivExt (1 : Module.End ℂ Cur) ν) + basisN.coord ∅ ν • (1 : NB) = ν := by
  have h : invN ∘ₗ LieChains.derivExt (1 : Module.End ℂ Cur) +
      LinearMap.smulRight (basisN.coord ∅) (1 : NB) = LinearMap.id := by
    apply basisN.ext
    intro t
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
      LieChains.derivExt_one_basis, map_smul, invN, Module.Basis.constr_basis,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases ht : t = ∅
    · subst ht
      simp [basisN_empty]
    · have hc : (t.card : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr ht))
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul, if_neg ht, zero_smul, add_zero]
  exact LinearMap.congr_fun h ν

/-- The coefficient-degree-zero part of a harmonic chain. -/
def psiH : HarmN NB →ₗ[ℂ] PositiveCE.Harmonic :=
  (TensorProduct.rid ℂ PositiveCE.Harmonic).toLinearMap ∘ₗ
    LinearMap.lTensor PositiveCE.Harmonic (basisN.coord ∅)

theorem psiH_tmul (h : PositiveCE.Harmonic) (ν : NB) :
    psiH (h ⊗ₜ ν) = basisN.coord ∅ ν • h := by
  simp [psiH]

/-- **A harmonic chain of coefficient degree `0` is `h ⊗ 1`.** -/
theorem eq_psiH_tmul_one {z : HarmN NB} (hz : numBH z = 0) : z = psiH z ⊗ₜ (1 : NB) := by
  have key : ∀ w : HarmN NB,
      LinearMap.lTensor PositiveCE.Harmonic invN (numBH w) + psiH w ⊗ₜ (1 : NB) = w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul h ν =>
      rw [numBH, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, psiH_tmul,
        TensorProduct.smul_tmul, ← TensorProduct.tmul_add, invN_derivExt_add]
    | add w w' hw hw' =>
      conv_rhs => rw [← hw, ← hw']
      rw [map_add, map_add, map_add, TensorProduct.add_tmul]
      abel
  have h := key z
  rw [hz, map_zero, zero_add] at h
  exact h.symm

theorem psiH_mem {p : ℕ} {z : HarmN NB} (hz : z ∈ tensorLeft (degH p)) : psiH z ∈ degH p := by
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a ν =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, psiH_tmul]
    exact Submodule.smul_mem _ _ a.property
  | add y y' hy hy' =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hy hy'

theorem numBH_eq_zero {p : ℕ} {S : ℤ} {z : HarmN NB} (hz : z ∈ harmWin p 0 S) : numBH z = 0 := by
  have h := Module.End.mem_eigenspace_iff.mp hz.1.2
  rwa [Nat.cast_zero, zero_smul] at h

/-! ## The relations on `h ⊗ 1` -/

theorem toEnd_constant_one (x : G) : LieModule.toEnd ℂ Current NB (constant x) (1 : NB) = 0 := by
  change LieChains.derivExt (adCur (constant x : Cur)) 1 = 0
  exact LieChains.derivExt_one _

theorem actH_tmul_one (x : G) (h : PositiveCE.Harmonic) :
    actH NB x (h ⊗ₜ (1 : NB)) = ⁅x, h⁆ ⊗ₜ (1 : NB) := by
  rw [actH, diag_tmul, toEnd_constant_one, TensorProduct.tmul_zero, add_zero,
    LieModule.toEnd_apply_apply]

theorem lie_tmul_one_mem_relH (x : G) (h : PositiveCE.Harmonic) :
    ⁅x, h⁆ ⊗ₜ (1 : NB) ∈ relH NB :=
  Submodule.mem_iSup_of_mem x ⟨h ⊗ₜ (1 : NB), actH_tmul_one x h⟩

/-! ## `V(n)` is spanned by `𝔤 · V(n)` for `n ≥ 1` -/

/-- **A nontrivial irreducible `V(n)` equals `𝔤 · V(n)`.** -/
theorem sl2Std_mem_span_lie (n : ℕ) (hn : n ≠ 0) (v : TauCeti.Sl2Std ℂ n) :
    v ∈ Submodule.span ℂ
      {w : TauCeti.Sl2Std ℂ n | ∃ (x : G) (u : TauCeti.Sl2Std ℂ n), ⁅x, u⁆ = w} := by
  let W : LieSubmodule ℂ G (TauCeti.Sl2Std ℂ n) :=
    { Submodule.span ℂ
        {w : TauCeti.Sl2Std ℂ n | ∃ (x : G) (u : TauCeti.Sl2Std ℂ n), ⁅x, u⁆ = w} with
      lie_mem := fun {x m} _ => Submodule.subset_span ⟨x, m, rfl⟩ }
  have hW : W ≠ ⊥ := by
    intro hW
    have hmem : ⁅TauCeti.slFinTwoBasis ℂ 2, TauCeti.Sl2Std.basis ℂ n 0⁆ ∈ W :=
      Submodule.subset_span ⟨_, _, rfl⟩
    rw [hW, LieSubmodule.mem_bot, TauCeti.Sl2Std.lie_slFinTwoBasis_two,
      TauCeti.Sl2Std.diag_basis] at hmem
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, sub_zero, smul_eq_zero,
      Nat.cast_eq_zero] at hmem
    rcases hmem with h | h
    · exact hn h
    · exact (TauCeti.Sl2Std.basis ℂ n).ne_zero 0 h
  have htop : W = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hW
  have hv : v ∈ W := htop ▸ LieSubmodule.mem_top v
  exact hv

/-- **For `p ≥ 1`, `h ⊗ 1` is a relation for every `h` of harmonic degree `p`.** -/
theorem tmul_one_mem_relH {p : ℕ} (hp : 0 < p) {h : PositiveCE.Harmonic} (hh : h ∈ degH p) :
    h ⊗ₜ[ℂ] (1 : NB) ∈ relH NB := by
  let e := PositiveCE.harmonicDegreeStandardEquiv p
  let L : TauCeti.Sl2Std ℂ (2 * p) →ₗ[ℂ] HarmN NB :=
    (TensorProduct.mk ℂ PositiveCE.Harmonic NB).flip (1 : NB) ∘ₗ
      (degH p).subtype ∘ₗ e.symm.toLinearEquiv.toLinearMap
  have hL : ∀ v, L v = ((e.symm v : PositiveCE.harmonicDegree p) : PositiveCE.Harmonic) ⊗ₜ[ℂ]
      (1 : NB) := fun _ => rfl
  have hspan : Submodule.span ℂ {w : TauCeti.Sl2Std ℂ (2 * p) |
      ∃ (x : G) (u : TauCeti.Sl2Std ℂ (2 * p)), ⁅x, u⁆ = w} ≤ (relH NB).comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨x, u, rfl⟩
    have hlie : e.symm ⁅x, u⁆ = ⁅x, e.symm u⁆ := e.symm.toLieModuleHom.map_lie x u
    rw [SetLike.mem_coe, Submodule.mem_comap, hL, hlie, LieSubmodule.coe_bracket]
    exact lie_tmul_one_mem_relH x _
  have hv := hspan (sl2Std_mem_span_lie (2 * p) (by omega) (e ⟨h, hh⟩))
  rw [Submodule.mem_comap, hL, LieModuleEquiv.symm_apply_apply] at hv
  exact hv

/-! ## Degree zero -/

/-- The harmonic cochain `1`. -/
def oneH : PositiveCE.Harmonic := ⟨1, LinearMap.mem_ker.mpr PositiveCE.laplacian_one⟩

@[simp] theorem oneH_coe : (oneH : PositiveCE.Cochain) = 1 := rfl

theorem oneH_mem_degH : oneH ∈ degH 0 := by
  change (1 : PositiveCE.Cochain) ∈ Finsupp.supported ℂ ℂ {s : Finset PositiveCE.Mode | s.card = 0}
  rw [show (1 : PositiveCE.Cochain) = FiniteExterior.monomial ∅ from rfl]
  exact Finsupp.single_mem_supported ℂ 1 rfl

theorem oneH_ne_zero : oneH ≠ 0 := by
  intro h
  have h1 := congrArg (fun u : PositiveCE.Harmonic => FreeCE.scalarCoefficient (u : PositiveCE.Cochain)) h
  simp only [oneH_coe, FreeCE.scalarCoefficient_one, ZeroMemClass.coe_zero, map_zero] at h1
  exact one_ne_zero h1

/-- **Harmonic degree `0` is the line `ℂ · 1`.** -/
theorem exists_eq_smul_oneH {h : PositiveCE.Harmonic} (hh : h ∈ degH 0) : ∃ c : ℂ, h = c • oneH := by
  have hfin : Module.finrank ℂ (PositiveCE.harmonicDegree 0) = 1 := by
    rw [PositiveCE.harmonicDegree_finrank]
  have hne : (⟨oneH, oneH_mem_degH⟩ : PositiveCE.harmonicDegree 0) ≠ 0 := by
    intro h0
    exact oneH_ne_zero (congrArg Subtype.val h0)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hfin ⟨h, hh⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- Harmonic degree `0` has energy `0`. -/
theorem harmonicEnergyScale_of_degH_zero {h : PositiveCE.Harmonic} (hh : h ∈ degH 0) :
    PositiveCE.harmonicEnergyScale h = h := by
  apply Subtype.ext
  rw [PositiveCE.harmonicEnergyScale_coe]
  have hp : h ∈ PositiveCE.harmonicLiePiece 0 (triangular 0) := by
    rw [← PositiveCE.harmonicDegree_eq_piece]
    exact hh
  rw [PositiveCE.energyScale_of_piece (u := (h : PositiveCE.Cochain)) hp, triangular_zero,
    pow_zero, one_smul]

theorem dilN_one : dilN (1 : NB) = 1 := map_one (ExteriorAlgebra.map scaleCur)

theorem dilH_tmul_one {h : PositiveCE.Harmonic} (hh : h ∈ degH 0) :
    dilH (h ⊗ₜ (1 : NB)) = h ⊗ₜ (1 : NB) := by
  rw [dilH, TensorProduct.map_tmul, harmonicEnergyScale_of_degH_zero hh, dilN_one]

/-- The transferred differential vanishes in degree `0`. -/
theorem dH_eq_zero_of_degH_zero {z : HarmN NB} (hz : z ∈ tensorLeft (degH 0)) : dH NB z = 0 := by
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a ν =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, dH, base_tmul,
      PositiveTransfer.differential_eq_zero_of_degree_zero
        (Submodule.tmul_mem_baseChange_of_mem 1 a.property),
      TensorProduct.zero_tmul, map_zero]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', add_zero]

/-! ## The augmentation -/

theorem algebraMapInv_derivExt (D : Module.End ℂ Cur) (ν : NB) :
    ExteriorAlgebra.algebraMapInv (LieChains.derivExt D ν) = 0 := by
  induction ν using ExteriorAlgebra.induction with
  | algebraMap r => rw [LieChains.derivExt_algebraMap, map_zero]
  | ι y =>
    rw [LieChains.derivExt_ι]
    simp [ExteriorAlgebra.algebraMapInv]
  | mul a b ha hb =>
    rw [LieChains.derivExt_mul, map_add, map_mul, map_mul, ha, hb, zero_mul, mul_zero, add_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

/-- The augmentation `h ⊗ ν ↦ h(∅) · ν₀` of harmonic chains. -/
def augH : HarmN NB →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
    TensorProduct.map (FreeCE.scalarCoefficient ∘ₗ PositiveCE.Harmonic.subtype)
      (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Cur)).toLinearMap

theorem augH_tmul (h : PositiveCE.Harmonic) (ν : NB) :
    augH (h ⊗ₜ ν) = FreeCE.scalarCoefficient (h : PositiveCE.Cochain) *
      ExteriorAlgebra.algebraMapInv ν := by
  simp [augH]

theorem augH_actH (x : G) (z : HarmN NB) : augH (actH NB x z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h ν =>
    have hcoe : ((⁅x, h⁆ : PositiveCE.Harmonic) : PositiveCE.Cochain) =
        ColorRoot.positiveAction x (h : PositiveCE.Cochain) := rfl
    rw [actH, diag_tmul, map_add, augH_tmul, augH_tmul, LieModule.toEnd_apply_apply, hcoe,
      FreeCE.scalarCoefficient_positiveAction, zero_mul, zero_add]
    have h0 : ExteriorAlgebra.algebraMapInv (LieModule.toEnd ℂ Current NB (constant x) ν) = 0 :=
      algebraMapInv_derivExt (adCur (constant x : Cur)) ν
    rw [h0, mul_zero]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', add_zero]

theorem relH_le_ker_augH : relH NB ≤ LinearMap.ker augH := by
  apply iSup_le
  rintro x _ ⟨z, rfl⟩
  exact augH_actH x z

theorem augH_oneH : augH (oneH ⊗ₜ (1 : NB)) = 1 := by
  rw [augH_tmul, oneH_coe, FreeCE.scalarCoefficient_one, map_one, mul_one]

/-! ## The BGG terms in coefficient degree zero -/

/-- **The degree-`p` term vanishes for `p ≥ 1`.** -/
theorem bggTerm_eq_bot_of_pos {p : ℕ} (hp : 0 < p) (S : ℤ) : bggTerm p 0 S = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨z, hz, rfl⟩
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    eq_psiH_tmul_one (numBH_eq_zero hz)]
  exact tmul_one_mem_relH hp (psiH_mem hz.1.1)

/-- **The degree-`0` term vanishes away from spin `0`.** -/
theorem bggTerm_zero_eq_bot {S : ℤ} (hS : S ≠ 0) : bggTerm 0 0 S = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨z, hz, rfl⟩
  have hz' := eq_psiH_tmul_one (numBH_eq_zero hz)
  have hfix : dilH z = z := by
    rw [hz']
    exact dilH_tmul_one (psiH_mem hz.1.1)
  have h1 : z ∈ Module.End.eigenspace dilH (1 : ℂ) := by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact hfix
  have hne : (1 : ℂ) ≠ (2 : ℂ) ^ S := by
    intro h
    apply hS
    have h5 : (2 : ℂ) ^ (0 : ℤ) = (2 : ℂ) ^ S := by rw [zpow_zero]; exact h
    exact (energyEigenvalue_injective h5).symm
  have hdisj := (Module.End.eigenspaces_iSupIndep dilH).pairwiseDisjoint hne
  have hz0 : z = 0 := Submodule.disjoint_def.mp hdisj z h1 hz.2
  rw [hz0, map_zero]
  exact Submodule.zero_mem _

theorem oneH_tmul_mem_harmWin : oneH ⊗ₜ[ℂ] (1 : NB) ∈ harmWin 0 0 0 := by
  refine ⟨⟨tmul_mem_tensorLeft oneH_mem_degH 1, Module.End.mem_eigenspace_iff.mpr ?_⟩,
    Module.End.mem_eigenspace_iff.mpr ?_⟩
  · rw [numBH, LinearMap.lTensor_tmul, LieChains.derivExt_one, TensorProduct.tmul_zero,
      Nat.cast_zero, zero_smul]
  · rw [dilH_tmul_one oneH_mem_degH, zpow_zero, one_smul]

/-- The class of `1 ⊗ 1`. -/
def oneClass : HarmN NB ⧸ relH NB := Submodule.Quotient.mk (oneH ⊗ₜ[ℂ] (1 : NB))

theorem oneClass_ne_zero : oneClass ≠ 0 := by
  intro h
  have hmem : oneH ⊗ₜ[ℂ] (1 : NB) ∈ relH NB := (Submodule.Quotient.mk_eq_zero _).mp h
  have h1 := relH_le_ker_augH hmem
  rw [LinearMap.mem_ker, augH_oneH] at h1
  exact one_ne_zero h1

/-- **The degree-`0` term in spin `0` is the line through `1 ⊗ 1`.** -/
theorem bggTerm_zero : bggTerm 0 0 0 = ℂ ∙ oneClass := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hc⟩ := exists_eq_smul_oneH (psiH_mem hz.1.1)
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [Submodule.mkQ_apply, eq_psiH_tmul_one (numBH_eq_zero hz), hc, oneClass,
      ← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul']
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨_, oneH_tmul_mem_harmWin, rfl⟩

theorem dHq_eq_zero_of_mem_bggTerm_zero {x : HarmN NB ⧸ relH NB} (hx : x ∈ bggTerm 0 0 0) :
    dHq NB x = 0 := by
  obtain ⟨z, hz, rfl⟩ := hx
  change Submodule.Quotient.mk (dH NB z) = (0 : HarmN NB ⧸ relH NB)
  rw [dH_eq_zero_of_degH_zero hz.1.1, Submodule.Quotient.mk_zero]

/-! ## The homology -/

theorem bggHomology_subsingleton {p : ℕ} {S : ℤ} (h : bggTerm p 0 S = ⊥) :
    Subsingleton (BGGHomology p 0 S) := by
  have hc : Subsingleton (bggWindow p 0 S).cycles := by
    constructor
    intro a b
    apply Subtype.ext
    have ha : ((a : HarmN NB ⧸ relH NB)) ∈ bggTerm p 0 S := a.property.1
    have hb : ((b : HarmN NB ⧸ relH NB)) ∈ bggTerm p 0 S := b.property.1
    rw [h, Submodule.mem_bot] at ha hb
    rw [ha, hb]
  constructor
  intro a b
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b => rw [Subsingleton.elim a b]

theorem finrank_bggHomology_zero : Module.finrank ℂ (BGGHomology 0 0 0) = 1 := by
  have hprev : bggTerm 1 0 0 = ⊥ := bggTerm_eq_bot_of_pos one_pos 0
  have hb : (bggWindow 0 0 0).boundaries = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨v, hv, hvw⟩ := (Contraction.DegreeWindow.mem_boundaries _ w).mp hw
    have hv' : v ∈ bggTerm 1 0 0 := hv
    rw [hprev, Submodule.mem_bot] at hv'
    rw [Submodule.mem_bot]
    apply Subtype.ext
    rw [← hvw, hv', map_zero]
    rfl
  have hc : (bggWindow 0 0 0).cycles = ℂ ∙ oneClass := by
    change bggTerm 0 0 0 ⊓ LinearMap.ker (dHq NB) = _
    rw [inf_eq_left.mpr (fun x hx => LinearMap.mem_ker.mpr (dHq_eq_zero_of_mem_bggTerm_zero hx)),
      bggTerm_zero]
  rw [(Submodule.quotEquivOfEqBot _ hb).finrank_eq, hc, finrank_span_singleton oneClass_ne_zero]

/-- **The BGG complex with trivial coefficients**: its homology is `ℂ` in degree `0`, spin `0`,
and zero otherwise. -/
theorem finrank_bggHomology_trivial (p : ℕ) (S : ℤ) :
    Module.finrank ℂ (BGGHomology p 0 S) = if p = 0 ∧ S = 0 then 1 else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact finrank_bggHomology_zero
  · have hterm : bggTerm p 0 S = ⊥ := by
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · exact bggTerm_zero_eq_bot fun hS => h ⟨rfl, hS⟩
      · exact bggTerm_eq_bot_of_pos hp S
    have := bggHomology_subsingleton hterm
    exact Module.finrank_zero_of_subsingleton

/-- **`H_p(𝔩, 𝔤; ℂ)_S`**: `K p 0 S` is `ℂ` for `p = S = 0` and zero otherwise. -/
theorem finrank_K_trivial (p : ℕ) (S : ℤ) :
    Module.finrank ℂ (K p 0 S) = if p = 0 ∧ S = 0 then 1 else 0 := by
  rw [(kEquivBGG p 0 S).finrank_eq, finrank_bggHomology_trivial]

/-- **The `B = 0` corollary in cohomological form**: the restricted relative cohomology in degree
`(p, 0, S)` is `ℂ` for `p = S = 0` and zero otherwise. -/
theorem finrank_cohomologyPiece_trivial (p : ℕ) (S : ℤ) :
    Module.finrank ℂ (cohomologyPiece (kDegree p 0 S)) = if p = 0 ∧ S = 0 then 1 else 0 := by
  rw [(dictionary p 0 S).finrank_eq, Subspace.dual_finrank_eq, finrank_K_trivial]

/-! ## The class of `1` -/

/-- The CE differential has no constant term. -/
theorem q_apply_empty (u : KhanSL2.Cochain) : KhanSL2.q u ∅ = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, Finsupp.add_apply, hu, hv, add_zero]
  | single s r =>
    by_contra hne
    have hdeg : monomialDegree (∅ : ExteriorMonomial) = monomialDegree s + (1, 0, 0) :=
      KhanSL2.q_degree (cochain_single_mem s r) (Finsupp.mem_support_iff.mpr hne)
    simp only [monomialDegree, Finset.card_empty, Finset.sum_empty, Prod.mk_add_mk,
      Prod.mk.injEq] at hdeg
    omega

/-- **The class of `1` is nonzero.** -/
theorem classOf_one_ne_zero : classOf cochainOne one_mem_cycles ≠ 0 := by
  intro h
  obtain ⟨u, -, hu⟩ := (Submodule.Quotient.mk_eq_zero _).mp h
  have h1 := congrArg (fun w : KhanSL2.Cochain => w ∅) hu
  simp only [q_apply_empty] at h1
  simp [cochainOne] at h1

theorem one_mem_cohomologyPiece :
    classOf cochainOne one_mem_cycles ∈ cohomologyPiece (kDegree 0 0 0) := by
  refine ⟨⟨cochainOne, one_mem_cycles⟩, ?_, rfl⟩
  change cochainOne ∈ cochainPiece (kDegree 0 0 0)
  rw [show kDegree 0 0 0 = 0 from rfl]
  exact cochain_one_mem

instance finiteDimensional_cohomologyPiece (p B : ℕ) (S : ℤ) :
    FiniteDimensional ℂ (cohomologyPiece (kDegree p B S)) :=
  LinearEquiv.finiteDimensional (dictionary p B S).symm

/-- **Corollary (paper (2.1), blueprint `cohomology_B_zero`).** In coefficient degree `0`, the
restricted relative cohomology is `ℂ · [1]`: the piece of degree `(p, 0, S)` vanishes unless
`(p, S) = (0, 0)`, and the piece of degree `(0, 0, 0)` is spanned by the class of `1`. -/
theorem cohomology_B_zero :
    (∀ (p : ℕ) (S : ℤ), ¬(p = 0 ∧ S = 0) → cohomologyPiece (kDegree p 0 S) = ⊥) ∧
      cohomologyPiece (kDegree 0 0 0) = ℂ ∙ classOf cochainOne one_mem_cycles := by
  refine ⟨fun p S h => ?_, ?_⟩
  · rw [← Submodule.finrank_eq_zero, finrank_cohomologyPiece_trivial, if_neg h]
  · symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact one_mem_cohomologyPiece
    · rw [finrank_span_singleton classOf_one_ne_zero, finrank_cohomologyPiece_trivial,
        if_pos ⟨rfl, rfl⟩]

end KhanSL2.BGGBridge
