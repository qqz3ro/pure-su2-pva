module

public import KhanSL2.Macdonald.RootEvenEmbedding
public import KhanSL2.Macdonald.RootOddEmbedding

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The root-model monomial bases map to precisely the color-zero free basis. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

/-- The actual inclusion of even mode numbers into color-zero labels. -/
def rootEvenModeEmbedding : ℕ ↪ StrongMacdonald.SMode where
  toFun n := ⟨n,0⟩
  inj' _n _m h := congrArg StrongMacdonald.SMode.index h

def rootEvenExponent (e : ℕ →₀ ℕ) : StrongMacdonald.Exp :=
  e.embDomain rootEvenModeEmbedding

theorem rootEvenExponent_support (e : ℕ →₀ ℕ) :
    ∀ g ∈ (rootEvenExponent e).support, g.color = 0 := by
  intro g hg
  rw [rootEvenExponent,Finsupp.support_embDomain] at hg
  obtain ⟨n,_hn,rfl⟩ := Finset.mem_map.mp hg
  rfl

theorem strongFreeEvenEquiv_rootExponent (e : ℕ →₀ ℕ) :
    strongFreeEvenEquiv ⟨rootEvenExponent e,rootEvenExponent_support e⟩ = e := by
  change Finsupp.equivMapDomain strongZeroEvenEquiv
    ((rootEvenExponent e).subtypeDomain (fun g : StrongMacdonald.SMode => g.color = 0)) = e
  ext n
  rw [Finsupp.equivMapDomain_apply,Finsupp.subtypeDomain_apply]
  exact Finsupp.embDomain_apply_self rootEvenModeEmbedding e n

@[simp] theorem strongFreeEvenEquiv_symm_val (e : ℕ →₀ ℕ) :
    (strongFreeEvenEquiv.symm e).val = rootEvenExponent e := by
  exact congrArg Subtype.val (strongFreeEvenEquiv.symm_apply_eq.mpr
    (strongFreeEvenEquiv_rootExponent e).symm)

@[simp] theorem strongFreeOddEquiv_symm_val (t : Finset ℕ) :
    (strongFreeOddEquiv.symm t).val = t.map rootOddModeEmbedding := by
  change (t.map strongZeroOddEquiv.symm.toEmbedding).map
    (Function.Embedding.subtype (fun m : Mode => m.color = 0)) = _
  rw [Finset.map_map]
  rfl

@[simp] theorem strongFreeIndexEquiv_symm_val (e : ℕ →₀ ℕ) (t : Finset ℕ) :
    (strongFreeIndexEquiv.symm (e,t)).val =
      (rootEvenExponent e,t.map rootOddModeEmbedding) := by
  change ((strongFreeEvenEquiv.symm e).val,(strongFreeOddEquiv.symm t).val) = _
  rw [strongFreeEvenEquiv_symm_val,strongFreeOddEquiv_symm_val]

theorem strongExponent_rootEvenExponent (e : ℕ →₀ ℕ) :
    strongExponentEquiv (rootEvenExponent e) =
      e.mapDomain (fun n : ℕ => (⟨n,0⟩ : Mode)) := by
  rw [rootEvenExponent,Finsupp.embDomain_eq_mapDomain]
  change Finsupp.equivMapDomain strongModeEquiv
    (e.mapDomain rootEvenModeEmbedding) = _
  rw [Finsupp.equivMapDomain_eq_mapDomain,← Finsupp.mapDomain_comp]
  rfl

/-- The actual even algebra embedding sends every monomial to its specified free monomial. -/
theorem rootEvenEmbedding_monomial (e : ℕ →₀ ℕ) :
    rootEvenEmbedding (MvPolynomial.monomial e 1) =
      StrongMacdonald.mono (rootEvenExponent e) ∅ := by
  apply strongModel.injective
  rw [strongModel_rootEvenEmbedding,MvPolynomial.rename_monomial,
    strongModel_mono,basis_apply,strongExponent_rootEvenExponent]
  rfl

end KhanSL2.Macdonald
