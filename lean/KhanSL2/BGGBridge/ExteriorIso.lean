module

public import KhanSL2.BGGBridge.Transfer
public import KhanSL2.BGG.ExteriorModel
public import KhanSL2.Chains.RelativeComplex
public import KhanSL2.ExteriorReindex

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-!
# The two exterior models of `Λ𝔩₊`

M2 uses Mathlib's `ExteriorAlgebra ℂ 𝔩₊`. The BGG development uses the concrete
ordered-monomial algebra `PositiveCE.Cochain` on the positive modes `(j, a)`, which stand for
`z^{j+1} t_a`. `exteriorEquiv` is the algebra isomorphism matching the generators.

It is compatible with the project's chain model. The BGG model sits inside the project's
cochains as the pure-`c` part (`PositiveCE.inclusion`), and this inclusion composed with
`exteriorEquiv` is the map `PhiC` used to prove M2.
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.BGGBridge

open KhanSL2.BGG KhanSL2.Current KhanSL2.FiniteExterior

/-- Positive modes, indexed as `(j, a)`. -/
def modeEquiv : ℕ × Fin 3 ≃ PositiveCE.Mode where
  toFun p := ⟨p.1, p.2⟩
  invFun m := (m.index, m.color)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The basis `z^{j+1} t_a` of `𝔩₊`, indexed by positive modes. -/
def plusModeBasis : Module.Basis PositiveCE.Mode ℂ plus := plusBasis.reindex modeEquiv

theorem plusModeBasis_apply (m : PositiveCE.Mode) :
    plusModeBasis m = plusCur m.index m.color := by
  rw [plusModeBasis, Module.Basis.reindex_apply]
  exact plusBasis_apply' _

/-- `Λ𝔩₊ → PositiveCE.Cochain`. -/
def toE : ExteriorAlgebra ℂ plus →ₐ[ℂ] PositiveCE.Cochain :=
  fromMathlibExterior.comp (ExteriorAlgebra.map plusModeBasis.repr.toLinearMap)

/-- `PositiveCE.Cochain → Λ𝔩₊`. -/
def ofE : PositiveCE.Cochain →ₐ[ℂ] ExteriorAlgebra ℂ plus :=
  (ExteriorAlgebra.map plusModeBasis.repr.symm.toLinearMap).comp toMathlibExterior

theorem toE_ι (y : plus) :
    toE (ExteriorAlgebra.ι ℂ y) = generatorLinear (plusModeBasis.repr y) := by
  rw [toE, AlgHom.comp_apply, ExteriorAlgebra.map_apply_ι, fromMathlibExterior_ι]
  rfl

theorem toE_ι_basis (m : PositiveCE.Mode) :
    toE (ExteriorAlgebra.ι ℂ (plusModeBasis m)) = FiniteExterior.generator m := by
  rw [toE_ι, Module.Basis.repr_self, generatorLinear_single, one_smul]

theorem ofE_generator (m : PositiveCE.Mode) :
    ofE (FiniteExterior.generator m) = ExteriorAlgebra.ι ℂ (plusModeBasis m) := by
  rw [ofE, AlgHom.comp_apply, toMathlibExterior_generator, ExteriorAlgebra.map_apply_ι]
  simp

/-- **The two exterior models agree.** -/
def exteriorEquiv : ExteriorAlgebra ℂ plus ≃ₐ[ℂ] PositiveCE.Cochain :=
  AlgEquiv.ofAlgHom toE ofE
    (algHom_ext _ _ fun m => by
      rw [AlgHom.comp_apply, ofE_generator, toE_ι_basis, AlgHom.id_apply])
    (ExteriorAlgebra.hom_ext (plusModeBasis.ext fun m => by
      change ofE (toE (ExteriorAlgebra.ι ℂ (plusModeBasis m))) = ExteriorAlgebra.ι ℂ (plusModeBasis m)
      rw [toE_ι_basis, ofE_generator]))

@[simp] theorem exteriorEquiv_apply (ξ : ExteriorAlgebra ℂ plus) : exteriorEquiv ξ = toE ξ := rfl

@[simp] theorem exteriorEquiv_symm_apply (ω : PositiveCE.Cochain) :
    exteriorEquiv.symm ω = ofE ω := rfl

theorem exteriorEquiv_ι_plusCur (j : ℕ) (a : Fin 3) :
    exteriorEquiv (ExteriorAlgebra.ι ℂ (plusCur j a)) =
      FiniteExterior.generator (⟨j, a⟩ : PositiveCE.Mode) := by
  rw [exteriorEquiv_apply, show plusCur j a = plusModeBasis ⟨j, a⟩ from
    (plusModeBasis_apply ⟨j, a⟩).symm, toE_ι_basis]

/-! ## The pure-`c` inclusion is a reindexing -/

/-- Positive modes as the `c`-modes of the project's cochains. -/
def cEmb : PositiveCE.Mode ↪ KhanSL2.Mode where
  toFun m := KhanSL2.Mode.c m.index m.color
  inj' := by
    intro m n h
    simp only [KhanSL2.Mode.c.injEq] at h
    exact PositiveCE.Mode.ext h.1 h.2

theorem cEmb_code (m n : PositiveCE.Mode) :
    GeneratorOrder.code (cEmb m) < GeneratorOrder.code (cEmb n) ↔
      GeneratorOrder.code m < GeneratorOrder.code n := by
  change 6 * m.index + 3 + m.color.val < 6 * n.index + 3 + n.color.val ↔
    3 * m.index + m.color.val < 3 * n.index + n.color.val
  have := m.color.isLt
  have := n.color.isLt
  omega

theorem inclusion_eq_reindex (ω : PositiveCE.Cochain) :
    PositiveCE.inclusion ω = reindex cEmb ω := by
  have h : PositiveCE.inclusion = reindexAlgHom cEmb cEmb_code := by
    apply algHom_ext
    intro m
    rw [PositiveCE.inclusion_generator]
    change _ = reindex cEmb (FiniteExterior.generator m)
    rw [reindex_generator]
    rfl
  rw [h]
  rfl

/-- The pure-`c` inclusion after `exteriorEquiv` is M2's `PhiC`. -/
theorem inclusion_exteriorEquiv (ξ : ExteriorAlgebra ℂ plus) :
    PositiveCE.inclusion (exteriorEquiv ξ) = PhiC ξ := by
  have h : PositiveCE.inclusion.comp toE = PhiC := by
    apply ExteriorAlgebra.hom_ext
    apply plusBasis.ext
    rintro ⟨j, a⟩
    simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      plusBasis_apply, PhiC_ι, phiC_plusCur]
    rw [show plusCur j a = plusModeBasis ⟨j, a⟩ from (plusModeBasis_apply ⟨j, a⟩).symm,
      toE_ι_basis, PositiveCE.inclusion_generator]
  exact DFunLike.congr_fun h ξ

end KhanSL2.BGGBridge
