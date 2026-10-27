module

public import KhanSL2.SymmetricFamily.LocalGradedBounds
public import KhanSL2.Factorization.EvenWeightBoundsTopQuotient

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The unique actual extremal vector of a one-point symmetric coefficient
fibre, and the one-dimensional top eigenspace of its degree-zero evaluation quotient. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald Factorization.EvenWeightBounds

/-- Every actual slot-invariant local root/color vector comes from the original coefficient fibre. -/
theorem exists_localSymmetricRootPreimage (k : ℕ) (a : ℂ) (x : LocalRootColors k a)
    (hx : ∀ σ, localRootColorPermute k a σ x = x) :
    ∃ v : LocalSymmetricFibre k a, localSymmetricRootInclusion k a v = x := by
  let := localCoefficientAlgebra k a
  let : IsScalarTower ℂ (Depth.RB k) ℂ :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).commutes z).symm
  let y : fixedOperators (baseLabelledPermute k ℂ) := ⟨x,fun σ => hx σ.symm⟩
  refine ⟨(symmetricBaseChangedLabelledEquiv k ℂ).symm y,?_⟩
  exact congrArg Subtype.val ((symmetricBaseChangedLabelledEquiv k ℂ).apply_symm_apply y)

/-- The all-e top color tensor with unit root coefficient. -/
def localTopRoot (k : ℕ) (a : ℂ) : LocalRootColors k a :=
  (1 : LocalRootAlgebra k a) ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin k → Fin 3) (fun _ => 0)

theorem localTopRoot_invariant (k : ℕ) (a : ℂ) (σ : Equiv.Perm (Fin k)) :
    localRootColorPermute k a σ (localTopRoot k a) = localTopRoot k a := by
  simp only [localTopRoot,localRootColorPermute,TensorProduct.map_tmul,
    AlgEquiv.toLinearMap_apply,map_one,colorPermute_basis,Function.comp_def]

/-- The actual top vector, obtained through the checked normalized coefficient realization. -/
def localSymmetricTop (k : ℕ) (a : ℂ) : LocalSymmetricFibre k a :=
  (exists_localSymmetricRootPreimage k a (localTopRoot k a) (localTopRoot_invariant k a)).choose

@[simp] theorem localSymmetricTop_image (k : ℕ) (a : ℂ) :
    localSymmetricRootInclusion k a (localSymmetricTop k a) = localTopRoot k a :=
  (exists_localSymmetricRootPreimage k a (localTopRoot k a) (localTopRoot_invariant k a)).choose_spec

theorem localSymmetricTop_ne_zero (k : ℕ) (a : ℂ) : localSymmetricTop k a ≠ 0 := by
  intro h
  have hz : localTopRoot k a = 0 := by rw [← localSymmetricTop_image,h,map_zero]
  have he := congrArg (fun y => localRootEvaluation k a
    (colorCoordinates k (LocalRootAlgebra k a) y (fun _ => 0))) hz
  have he0 : (1 : ℂ) = 0 := by
    simpa only [localTopRoot,colorCoordinates_basis_tmul,ite_true,map_zero,map_one,Pi.zero_apply] using he
  exact one_ne_zero he0

theorem localSymmetricTop_cartan (k : ℕ) (a : ℂ) :
    ⁅BGG.constant MatrixSL2.h,localSymmetricTop k a⁆ = (2*(k:ℂ)) • localSymmetricTop k a := by
  apply localSymmetricRootInclusion_injective k a
  rw [localSymmetricRootInclusion_cartan,map_smul,localSymmetricTop_image]
  simp only [localTopRoot,LinearMap.lTensor_tmul,colorCartan_basis,TensorProduct.tmul_smul]
  have hw : colorWordHalfWeight (fun _ : Fin k => (0 : Fin 3)) = (k:ℤ) :=
    (colorWordHalfWeight_eq_top_iff _).mpr rfl
  rw [hw,Int.cast_natCast]

/-- Every actual top eigenvector is a scalar multiple of this specified vector. -/
theorem localSymmetric_top_spanned (k : ℕ) (a : ℂ) (v : LocalSymmetricFibre k a)
    (hv : ⁅BGG.constant MatrixSL2.h,v⁆ = (2*(k:ℂ)) • v) :
    ∃ c : ℂ, c • localSymmetricTop k a = v := by
  have hc : LinearMap.lTensor (LocalRootAlgebra k a)
      (colorDeriv k (LieAlgebra.ad ℂ BGG.G MatrixSL2.h)) (localSymmetricRootInclusion k a v) =
      (2*(k:ℂ)) • localSymmetricRootInclusion k a v := by
    rw [← localSymmetricRootInclusion_cartan,hv,map_smul]
  obtain ⟨q,hq⟩ := exists_root_tmul_top_of_cartan k (LocalRootAlgebra k a) _ hc
  obtain ⟨c,hc⟩ := localRoot_fixed_isScalar k a q
    (localRootColor_top_coefficient_fixed k a _ (localSymmetricRootInclusion_invariant k a v) q hq)
  refine ⟨c,localSymmetricRootInclusion_injective k a ?_⟩
  rw [map_smul,localSymmetricTop_image,hq,← hc]
  simp only [localTopRoot,TensorProduct.smul_tmul',Algebra.smul_def,mul_one]

/-- The canonical projection of the original full fibre to its degree-zero evaluation quotient. -/
def localSymmetricZeroProjection (k : ℕ) (a : ℂ) :
    LocalSymmetricFibre k a →ₗ⁅ℂ,BGG.Current⁆ LocalSymmetricGraded k a 0 :=
  (LieSubmodule.Quotient.mk' (localSymmetricSuccessor k a 0)).comp
    { toLinearMap :=
        { toFun := fun v => ⟨v,by rw [localSymmetricFiltration_zero]; trivial⟩
          map_add' := fun v w => rfl
          map_smul' := fun c v => rfl }
      map_lie' := fun {x v} => rfl }

theorem localSymmetricZeroProjection_surjective (k : ℕ) (a : ℂ) :
    Function.Surjective (localSymmetricZeroProjection k a) := by
  intro v
  obtain ⟨u,rfl⟩ := LieSubmodule.Quotient.surjective_mk' (localSymmetricSuccessor k a 0) v
  exact ⟨u.val,rfl⟩

/-- The specified top vector survives the actual degree-zero quotient. -/
theorem localSymmetricZeroTop_ne_zero (k : ℕ) (a : ℂ) :
    localSymmetricZeroProjection k a (localSymmetricTop k a) ≠ 0 := by
  intro hz
  have hi : localSymmetricTop k a ∈ localSymmetricFiltration k a 1 :=
    (LieSubmodule.Quotient.mk_eq_zero (localSymmetricSuccessor k a 0)).mp hz
  exact localSymmetricTop_ne_zero k a
    (localSymmetricFiltration_positive_top_eq_zero k a _ hi (localSymmetricTop_cartan k a))

/-- A surjection carrying a spanning highest vector to a nonzero vector preserves
its one-dimensional highest eigenspace. The splitting used here is only G-equivariant. -/
theorem top_finrank_one_of_surjective {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [LieRingModule BGG.G V] [LieModule ℂ BGG.G V]
    [AddCommGroup W] [Module ℂ W] [LieRingModule BGG.G W] [LieModule ℂ BGG.G W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (f : V →ₗ⁅ℂ,BGG.G⁆ W) (hf : Function.Surjective f) (z : ℂ) (t : V)
    (ht : ⁅MatrixSL2.h,t⁆ = z • t) (hft : f t ≠ 0)
    (hspan : ∀ v : V, ⁅MatrixSL2.h,v⁆ = z • v → ∃ c : ℂ, c • t = v) :
    Module.finrank ℂ ((cartan W).eigenspace z) = 1 := by
  let w : (cartan W).eigenspace z := ⟨f t,by
    apply Module.End.mem_eigenspace_iff.mpr
    change ⁅MatrixSL2.h,f t⁆ = _
    rw [← f.map_lie,ht,map_smul]⟩
  have hw : w ≠ 0 := fun h => hft (congrArg Subtype.val h)
  apply (finrank_eq_one_iff_of_nonzero' w hw).mpr
  intro v
  obtain ⟨s,hs⟩ := BGG.exists_lie_generalizedInverse f
  have hfs (u : W) : f (s u) = u := by
    obtain ⟨v,rfl⟩ := hf u
    exact hs v
  have he : ⁅MatrixSL2.h,s v.val⁆ = z • s v.val := by
    rw [← s.map_lie]
    have hv : ⁅MatrixSL2.h,v.val⁆ = z • v.val := Module.End.mem_eigenspace_iff.mp v.property
    rw [hv,map_smul]
  obtain ⟨c,hc⟩ := hspan (s v.val) he
  refine ⟨c,Subtype.ext ?_⟩
  change c • f t = v.val
  rw [← map_smul,hc,hfs]

/-- The degree-zero evaluation quotient has exactly one top vector up to scalar. -/
theorem localSymmetricGradedZero_top_finrank (k : ℕ) (a : ℂ) :
    Module.finrank ℂ ((cartan (ConstantRestriction (LocalSymmetricGraded k a 0))).eigenspace
      (2*(k:ℂ))) = 1 := by
  apply top_finrank_one_of_surjective
    (constantRestrictionHom (localSymmetricZeroProjection k a))
    (localSymmetricZeroProjection_surjective k a) (2*(k:ℂ))
    (show ConstantRestriction (LocalSymmetricFibre k a) from localSymmetricTop k a)
    (localSymmetricTop_cartan k a) (localSymmetricZeroTop_ne_zero k a)
  intro v hv
  exact localSymmetric_top_spanned k a (constantRestrictionEquiv (LocalSymmetricFibre k a) v) hv

end KhanSL2.SymmetricFamily