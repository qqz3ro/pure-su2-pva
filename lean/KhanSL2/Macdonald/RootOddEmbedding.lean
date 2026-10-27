module

public import KhanSL2.Macdonald.StrongBridgeRootModel
public import KhanSL2.Macdonald.ExteriorCoproductPairing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The one-color polynomial exterior algebra embeds by its actual ordered
color-zero generators. This identifies the root model's exterior basis. -/
noncomputable section
namespace KhanSL2.Macdonald
open BGGBridge

/-- The actual polynomial basis, mapped to color-zero positive-current modes. -/
def rootOddCurrent : Polynomial ℂ →ₗ[ℂ] Current.plus :=
  (Polynomial.basisMonomials ℂ).constr ℂ (fun n => plusModeBasis ⟨n,0⟩)

@[simp] theorem rootOddCurrent_basis (n : ℕ) :
    rootOddCurrent (Polynomial.basisMonomials ℂ n) = plusModeBasis ⟨n,0⟩ :=
  Module.Basis.constr_basis _ _ _ _

/-- The original exterior functor applied to the actual polynomial generator inclusion. -/
def rootOddExterior : ExteriorAlgebra ℂ (Polynomial ℂ) →ₐ[ℂ] Exterior :=
  exteriorEquiv.toAlgHom.comp (ExteriorAlgebra.map rootOddCurrent)

@[simp] theorem rootOddExterior_ι_basis (n : ℕ) :
    rootOddExterior (ExteriorAlgebra.ι ℂ (Polynomial.basisMonomials ℂ n)) =
      FiniteExterior.generator (⟨n,0⟩ : Mode) := by
  rw [rootOddExterior,AlgHom.comp_apply,ExteriorAlgebra.map_apply_ι,rootOddCurrent_basis]
  exact exteriorEquiv_ι_mode _

/-- Color-zero embedding of exponent indices, with their original increasing order. -/
def rootOddModeEmbedding : ℕ ↪ Mode where
  toFun n := ⟨n,0⟩
  inj' _n _m h := congrArg BGG.PositiveCE.Mode.index h

/-- An increasing product of the actual positive-mode generators is its monomial. -/
theorem positive_list_prod_generator (l : List Mode)
    (hl : l.Pairwise (fun x y => BGG.PositiveCE.Mode.code x < BGG.PositiveCE.Mode.code y)) :
    (l.map FiniteExterior.generator).prod = FiniteExterior.monomial l.toFinset := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.map_cons,List.prod_cons,ih hl.2,List.toFinset_cons]
    change FiniteExterior.wedge BGG.PositiveCE.Mode.code (Finsupp.single {x} 1)
      (Finsupp.single l.toFinset 1) = _
    rw [FiniteExterior.wedge_single,one_mul,one_smul,FiniteExterior.monomialWedge]
    have hx : x ∉ l.toFinset := by
      intro hx
      exact lt_irrefl _ (hl.1 x (List.mem_toFinset.mp hx))
    rw [if_pos (Finset.disjoint_singleton_left.mpr hx),Finset.singleton_union]
    congr 1
    have h0 : FiniteExterior.inversionCount BGG.PositiveCE.Mode.code {x} l.toFinset = 0 := by
      rw [FiniteExterior.inversionCount,Finset.sum_singleton,Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro y hy
      exact not_lt.mpr (hl.1 y (List.mem_toFinset.mp hy)).le
    rw [h0,pow_zero]

/-- The exterior-power restriction of the specified generator embedding. -/
def rootOddPowerEmbedding (q : ℕ) : (⋀[ℂ]^q (Polynomial ℂ)) →ₗ[ℂ] Exterior :=
  rootOddExterior.toLinearMap.comp (ExteriorAlgebra.exteriorPower ℂ q (Polynomial ℂ)).subtype

/-- Its actual basis image, with no untracked determinant sign. -/
theorem rootOddPowerEmbedding_basis (q : ℕ) (t : Set.powersetCard ℕ q) :
    rootOddPowerEmbedding q ((Polynomial.basisMonomials ℂ).exteriorPower q t) =
      FiniteExterior.monomial (t.val.map rootOddModeEmbedding) := by
  change rootOddExterior (((Polynomial.basisMonomials ℂ).exteriorPower q t).val) = _
  rw [exteriorPower.basis_apply,exteriorPower.ιMulti_family_apply_coe]
  simp only [ExteriorAlgebra.ιMulti_family,ExteriorAlgebra.ιMulti_apply,
    Function.comp_def,map_list_prod,List.map_ofFn,rootOddExterior_ι_basis]
  let e := Set.powersetCard.ofFinEmbEquiv.symm t
  have h := positive_list_prod_generator (List.ofFn (fun i => (⟨e i,0⟩ : Mode))) (by
    rw [List.pairwise_ofFn]
    intro i j hij
    have he := e.strictMono hij
    simp only [BGG.PositiveCE.Mode.code,Fin.val_zero,Nat.add_zero]
    omega)
  rw [List.map_ofFn] at h
  simp only [Function.comp_def] at h
  change (List.ofFn (fun i => FiniteExterior.generator (⟨e i,0⟩ : Mode))).prod = _
  rw [h]
  congr 1
  ext m
  simp only [List.mem_toFinset,List.mem_ofFn,Finset.mem_map]
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨e i,?_,rfl⟩
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t (e i)).mp ⟨i,rfl⟩
  · rintro ⟨n,hn,rfl⟩
    obtain ⟨i,hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t n).mpr hn
    exact ⟨i,congrArg (fun a => (⟨a,0⟩ : Mode)) hi⟩

end KhanSL2.Macdonald
