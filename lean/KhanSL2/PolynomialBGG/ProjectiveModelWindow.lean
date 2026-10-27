module

public import KhanSL2.PolynomialBGG.ProjectiveModelExterior
public import KhanSL2.PolynomialBGG.ProjectiveModelRetract
public import KhanSL2.PolynomialBGG.ColoredWindows
public import KhanSL2.BGG.HarmonicTensorTerms

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! A fixed harmonic degree and exterior coefficient degree form a genuine
retract of the full harmonic tensor module, equivariantly for constant sl₂.
Their coinvariant quotient consequently embeds in the existing BGG quotient.
-/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.PolynomialBGG
open BGG BGGBridge Current Conditional

/-- The ungraded coefficient model with fixed harmonic and exterior degree. -/
abbrev WindowModel (B p : ℕ) := TauCeti.Sl2Std ℂ (2*p) ⊗[ℂ] (⋀[ℂ]^B Cur)

theorem exteriorNumber_eq (B : ℕ) (u : ⋀[ℂ]^B Cur) :
    LieChains.derivExt (1 : Module.End ℂ Cur) (u : NB) = (B : ℂ) • (u : NB) := by
  have h : exteriorDeriv B (1 : Module.End ℂ Cur) = (B : ℂ) • LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, exteriorDeriv_ιMulti,
      Module.End.one_apply, Function.update_eq_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, LinearMap.smul_apply, LinearMap.id_apply,
      Nat.cast_smul_eq_nsmul]
  exact congrArg Subtype.val (LinearMap.congr_fun h u)

theorem coefficientProjection_eq_exteriorProjection (B : ℕ) (u : NB) :
    coefficientProjection B u = (exteriorProjection Cur B u : NB) := by
  have h : coefficientProjection B =
      (⋀[ℂ]^B Cur).subtype.comp (exteriorProjection Cur B) := by
    apply basisN.ext
    intro t
    have ht : basisN t ∈ ⋀[ℂ]^t.card Cur := by
      have hb := ExteriorAlgebra.basis_eq_coe_basis curBasisLex
        (⟨t, rfl⟩ : Set.powersetCard Idx t.card)
      rw [show basisN t = _ from hb]
      exact (curBasisLex.exteriorPower t.card ⟨t, rfl⟩).property
    simp only [coefficientProjection, Module.Basis.constr_basis, LinearMap.comp_apply,
      Submodule.subtype_apply]
    by_cases he : t.card = B
    · subst B
      rw [if_pos rfl, show exteriorProjection Cur t.card (basisN t) =
          (⟨basisN t, ht⟩ : ⋀[ℂ]^t.card Cur) from exteriorProjection_coe Cur t.card ⟨_, ht⟩]
    · rw [if_neg he, exteriorProjection_of_mem_ne Cur B t.card he _ ht]
      rfl
  exact LinearMap.congr_fun h u

theorem exteriorProjection_eq_of_number (B : ℕ) (u : NB)
    (hu : LieChains.derivExt (1 : Module.End ℂ Cur) u = (B : ℂ) • u) :
    (exteriorProjection Cur B u : NB) = u := by
  have h := coefficientComplementInv_identity B u
  rw [hu, sub_self, map_zero, zero_add] at h
  exact (coefficientProjection_eq_exteriorProjection B u).symm.trans h

/-- Include the fixed-degree model in the harmonic tensor module. -/
def windowIncl (B p : ℕ) : WindowModel B p →ₗ[ℂ] HarmN NB :=
  TensorProduct.map (PositiveCE.standardHarmonicEmbedding p).toLinearMap (⋀[ℂ]^B Cur).subtype

/-- Project both factors to their prescribed degrees. -/
def windowProj (B p : ℕ) : HarmN NB →ₗ[ℂ] WindowModel B p :=
  TensorProduct.map (PositiveCE.standardHarmonicProjection p).toLinearMap (exteriorProjection Cur B)

@[simp] theorem windowProj_windowIncl (B p : ℕ) (u : WindowModel B p) :
    windowProj B p (windowIncl B p u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul v ν => simp [windowIncl, windowProj]

/-- The diagonal constant action on the fixed-degree model. -/
def windowAct (B p : ℕ) (x : G) : Module.End ℂ (WindowModel B p) :=
  diag (LieModule.toEnd ℂ G (TauCeti.Sl2Std ℂ (2*p)) x)
    (exteriorDeriv B (adCur (constant x)))

theorem windowIncl_act (B p : ℕ) (x : G) (u : WindowModel B p) :
    windowIncl B p (windowAct B p x u) = actH NB x (windowIncl B p u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul v ν =>
    simp only [windowAct, windowIncl, actH, diag_tmul, map_add, TensorProduct.map_tmul,
      LieModule.toEnd_apply_apply]
    change PositiveCE.standardHarmonicEmbedding p ⁅x, v⁆ ⊗ₜ[ℂ] (ν : NB) +
      PositiveCE.standardHarmonicEmbedding p v ⊗ₜ[ℂ] LieChains.derivExt (adCur (constant x)) ν =
      ⁅x, PositiveCE.standardHarmonicEmbedding p v⁆ ⊗ₜ[ℂ] (ν : NB) +
        PositiveCE.standardHarmonicEmbedding p v ⊗ₜ[ℂ] LieChains.derivExt (adCur (constant x)) ν
    rw [(PositiveCE.standardHarmonicEmbedding p).map_lie]

theorem windowProj_act (B p : ℕ) (x : G) (u : HarmN NB) :
    windowProj B p (actH NB x u) = windowAct B p x (windowProj B p u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul v ν =>
    simp only [windowAct, windowProj, actH, diag_tmul, map_add, TensorProduct.map_tmul,
      LieModule.toEnd_apply_apply]
    change PositiveCE.standardHarmonicProjection p ⁅x, v⁆ ⊗ₜ[ℂ] exteriorProjection Cur B ν +
      PositiveCE.standardHarmonicProjection p v ⊗ₜ[ℂ]
        exteriorProjection Cur B (LieChains.derivExt (adCur (constant x)) ν) =
      ⁅x, PositiveCE.standardHarmonicProjection p v⁆ ⊗ₜ[ℂ] exteriorProjection Cur B ν +
        PositiveCE.standardHarmonicProjection p v ⊗ₜ[ℂ]
          exteriorDeriv B (adCur (constant x)) (exteriorProjection Cur B ν)
    rw [(PositiveCE.standardHarmonicProjection p).map_lie, exteriorProjection_derivExt]

/-- The genuine constant Lie algebra relations on the fixed-degree model. -/
def windowRelations (B p : ℕ) : Submodule ℂ (WindowModel B p) := actionRelations (windowAct B p)

abbrev WindowCoinvariants (B p : ℕ) := WindowModel B p ⧸ windowRelations B p

/-- Include the quotient by the actual diagonal constant relations. -/
def windowInclQ (B p : ℕ) : WindowCoinvariants B p →ₗ[ℂ] HarmN NB ⧸ relH NB :=
  (windowRelations B p).mapQ (relH NB) (windowIncl B p)
    (actionRelations_le_comap (windowAct B p) (actH NB) (windowIncl B p)
      (fun x => LinearMap.ext (windowIncl_act B p x)))

/-- The equivariant degree projector descends through the constant relations. -/
def windowProjQ (B p : ℕ) : (HarmN NB ⧸ relH NB) →ₗ[ℂ] WindowCoinvariants B p :=
  (relH NB).mapQ (windowRelations B p) (windowProj B p)
    (actionRelations_le_comap (actH NB) (windowAct B p) (windowProj B p)
      (fun x => LinearMap.ext (windowProj_act B p x)))

@[simp] theorem windowProjQ_windowInclQ (B p : ℕ) (u : WindowCoinvariants B p) :
    windowProjQ B p (windowInclQ B p u) = u := by
  induction u using Submodule.Quotient.induction_on with
  | _ u =>
    change (windowRelations B p).mkQ (windowProj B p (windowIncl B p u)) =
      (windowRelations B p).mkQ u
    rw [windowProj_windowIncl]

theorem windowInclQ_injective (B p : ℕ) : Function.Injective (windowInclQ B p) :=
  (show Function.LeftInverse (windowProjQ B p) (windowInclQ B p) from
    windowProjQ_windowInclQ B p).injective

/-- No fixed-degree harmonic class is lost by the model inclusion. -/
theorem windowIncl_proj_of_mem (B p : ℕ) (S : ℤ) (u : HarmN NB)
    (hu : u ∈ harmWin p B S) : windowIncl B p (windowProj B p u) = u := by
  let W := LinearMap.ker ((windowIncl B p).comp (windowProj B p) - LinearMap.id)
  have hW : harmWin p B S ≤ W := by
    apply harmWin_le_of_tmul
    intro h hh ν hν
    change windowIncl B p (windowProj B p (h ⊗ₜ[ℂ] ν)) - h ⊗ₜ[ℂ] ν = 0
    rw [sub_eq_zero]
    simp only [windowIncl, windowProj, TensorProduct.map_tmul]
    change PositiveCE.standardHarmonicEmbedding p (PositiveCE.standardHarmonicProjection p h) ⊗ₜ[ℂ]
      (exteriorProjection Cur B ν : NB) = h ⊗ₜ[ℂ] ν
    rw [PositiveCE.standardHarmonicEmbedding_projection_of_mem p h hh,
      exteriorProjection_eq_of_number B ν hν]
  exact sub_eq_zero.mp (hW hu)

/-- The fixed-degree model maps precisely into the actual assembled term. -/
theorem windowInclQ_mem_termRange (B p : ℕ) (u : WindowCoinvariants B p) :
    windowInclQ B p u ∈ (BGGComplex.termToCoinvariantsLinear B p).range := by
  induction u using Submodule.Quotient.induction_on with
  | _ u =>
    let W := ((BGGComplex.termToCoinvariantsLinear B p).range).restrictScalars ℂ
    change (relH NB).mkQ (windowIncl B p u) ∈ W
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simpa only [map_add] using W.add_mem hu hv
    | tmul v ν => exact coefficientClass_mem_termRange B p v ν (exteriorNumber_eq B ν)

/-- Project the actual spin-assembled term into the fixed-degree model quotient. -/
def termToWindow (B p : ℕ) : BGGComplex.Term B p →ₗ[ℂ] WindowCoinvariants B p :=
  (windowProjQ B p).comp (BGGComplex.termToCoinvariants B p)

theorem windowInclQ_termToWindow (B p : ℕ) (u : BGGComplex.Term B p) :
    windowInclQ B p (termToWindow B p u) = BGGComplex.termToCoinvariants B p u := by
  have h : (windowInclQ B p).comp (termToWindow B p) = BGGComplex.termToCoinvariants B p := by
    apply DirectSum.linearMap_ext
    intro S
    apply LinearMap.ext
    intro x
    change windowInclQ B p (windowProjQ B p
      (BGGComplex.termToCoinvariants B p (DirectSum.lof ℂ ℤ _ S x))) =
      BGGComplex.termToCoinvariants B p (DirectSum.lof ℂ ℤ _ S x)
    rw [BGGComplex.termToCoinvariants_lof]
    obtain ⟨z, hz, heq⟩ := x.property
    rw [← heq]
    change (relH NB).mkQ (windowIncl B p (windowProj B p z)) = (relH NB).mkQ z
    rw [windowIncl_proj_of_mem B p S z hz]
  exact LinearMap.congr_fun h u

theorem termToWindow_injective (B p : ℕ) : Function.Injective (termToWindow B p) := by
  intro u v h
  apply BGGComplex.termToCoinvariants_injective B p
  simpa only [windowInclQ_termToWindow] using congrArg (windowInclQ B p) h

theorem termToWindow_surjective (B p : ℕ) : Function.Surjective (termToWindow B p) := by
  intro u
  obtain ⟨v, hv⟩ := windowInclQ_mem_termRange B p u
  refine ⟨v, ?_⟩
  apply windowInclQ_injective B p
  rw [windowInclQ_termToWindow]
  exact hv

/-- The actual assembled BGG term is exactly the coinvariants of
V(2p) tensored with the B-th exterior power of the current algebra. -/
def termEquivWindow (B p : ℕ) : BGGComplex.Term B p ≃ₗ[ℂ] WindowCoinvariants B p :=
  LinearEquiv.ofBijective (termToWindow B p)
    ⟨termToWindow_injective B p, termToWindow_surjective B p⟩

end KhanSL2.PolynomialBGG
