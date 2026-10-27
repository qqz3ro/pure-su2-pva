module

public import KhanSL2.Macdonald.StrongBridgeFreeCoordinates
public import KhanSL2.SymmetricFamily.UncoloredWords

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Removing the fixed colour-zero labels from the explicit free basis.
The remaining indices are ordinary polynomial multiplicities and finite
sets of positive exterior-mode indices. -/
noncomputable section
namespace KhanSL2.Macdonald

def strongZeroEvenEquiv : {g : StrongMacdonald.SMode // g.color = 0} ≃ ℕ where
  toFun g := g.val.index
  invFun n := ⟨⟨n,0⟩,rfl⟩
  left_inv g := by
    obtain ⟨⟨n,c⟩,hc⟩ := g
    change c = 0 at hc
    subst c
    rfl
  right_inv n := rfl

def strongZeroOddEquiv : {g : Mode // g.color = 0} ≃ ℕ where
  toFun g := g.val.index
  invFun n := ⟨⟨n,0⟩,rfl⟩
  left_inv g := by
    obtain ⟨⟨n,c⟩,hc⟩ := g
    change c = 0 at hc
    subst c
    rfl
  right_inv n := rfl

def strongFreeEvenEquiv :
    {e : StrongMacdonald.Exp // ∀ g ∈ e.support, g.color = 0} ≃ (ℕ →₀ ℕ) :=
  (Finsupp.restrictSupportEquiv {g : StrongMacdonald.SMode | g.color = 0} ℕ).trans
    (Finsupp.domCongr strongZeroEvenEquiv).toEquiv

/-- A finite set supported in a subset is exactly a finite set in that subset. -/
def finiteSetSupportedEquiv {α : Type*} (P : α → Prop) [DecidablePred P] :
    {s : Finset α // ∀ a ∈ s, P a} ≃ Finset {a : α // P a} where
  toFun s := s.val.subtype P
  invFun s := ⟨s.map (Function.Embedding.subtype P),
    fun _ h => Finset.property_of_mem_map_subtype s h⟩
  left_inv s := Subtype.ext (Finset.subtype_map_of_mem s.property)
  right_inv s := by
    ext a
    simp only [Finset.mem_subtype, Finset.mem_map]
    constructor
    · rintro ⟨b,hb,he⟩
      have hba : b = a := Subtype.ext he
      simpa only [hba] using hb
    · intro ha
      exact ⟨a,ha,rfl⟩

def strongFreeOddEquiv : {t : Finset Mode // ∀ m ∈ t, m.color = 0} ≃ Finset ℕ :=
  (finiteSetSupportedEquiv (fun m : Mode => m.color = 0)).trans strongZeroOddEquiv.finsetCongr

abbrev FreeMonomialIndex := (ℕ →₀ ℕ) × Finset ℕ

/-- Actual colour-zero indices become uncoloured even multiplicities and odd sets. -/
def strongFreeIndexEquiv : strongFreeIndices ≃ FreeMonomialIndex :=
  Equiv.subtypeProdEquivProd.trans (strongFreeEvenEquiv.prodCongr strongFreeOddEquiv)

/-- Explicit uncoloured monomial coordinates on the imported free harmonic source. -/
def strongFreeUncoloredEquiv : strongFree ≃ₗ[ℂ] FreeMonomialIndex →₀ ℂ :=
  strongFreeCoordinateEquiv.trans (Finsupp.domLCongr strongFreeIndexEquiv)

/-- The specified free-generator cohomology map, in uncoloured finite coordinates. -/
def uncoloredFreeCohomologyEquiv : (FreeMonomialIndex →₀ ℂ) ≃ₗ[ℂ] Cohomology :=
  strongFreeUncoloredEquiv.symm.trans strongFreeCohomologyEquiv

@[simp] theorem strongFreeUncoloredEquiv_apply (u : strongFree) (b : FreeMonomialIndex) :
    strongFreeUncoloredEquiv u b =
      StrongMacdonald.coefW u.val (strongFreeIndexEquiv.symm b).val.1
        (strongFreeIndexEquiv.symm b).val.2 := by
  simp [strongFreeUncoloredEquiv, Finsupp.domLCongr_apply]

end KhanSL2.Macdonald
