module

public import KhanSL2.Factorization.RelativeChainsDualityQuotient

@[expose] public section

/-! Canonical homology duality for a short complex of complex vector spaces.
The map is evaluation on represented cycles. Its surjectivity uses extension of
linear functionals; the map itself involves no choice of splitting. -/

noncomputable section
namespace KhanSL2.Factorization.PerfectDuality

variable {X Y Z : Type*}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [AddCommGroup Z] [Module ℂ Z]

/-- The incoming boundary subspace inside the outgoing kernel. -/
def pairBoundaries (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z) : Submodule ℂ (LinearMap.ker g) :=
  (LinearMap.range f).comap (LinearMap.ker g).subtype

/-- The actual middle cycles/boundaries quotient of a square-zero pair. -/
abbrev PairHomology (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z) (_h : g.comp f = 0) :=
  LinearMap.ker g ⧸ pairBoundaries f g

/-- Transposition reverses a square-zero pair. -/
theorem dualPair_square (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z) (h : g.comp f = 0) :
    f.dualMap.comp g.dualMap = 0 := by
  apply LinearMap.ext
  intro ℓ
  apply LinearMap.ext
  intro x
  change ℓ (g (f x)) = 0
  have hx : g (f x) = 0 := LinearMap.congr_fun h x
  rw [hx, map_zero]

/-- Homology of the transposed pair. -/
abbrev DualPairHomology (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z) (h : g.comp f = 0) :=
  PairHomology g.dualMap f.dualMap (dualPair_square f g h)

/-- A transposed cocycle evaluates on actual homology classes. -/
def dualCycleFunctional (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z) (h : g.comp f = 0)
    (ℓ : LinearMap.ker f.dualMap) : Module.Dual ℂ (PairHomology f g h) :=
  (pairBoundaries f g).liftQ (ℓ.val.comp (LinearMap.ker g).subtype) (by
    intro z hz
    change z.val ∈ LinearMap.range f at hz
    obtain ⟨x, hx⟩ := hz
    change ℓ.val z.val = 0
    rw [← hx]
    exact LinearMap.congr_fun ℓ.property x)

@[simp] theorem dualCycleFunctional_mk (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z)
    (h : g.comp f = 0) (ℓ : LinearMap.ker f.dualMap) (z : LinearMap.ker g) :
    dualCycleFunctional f g h ℓ (Submodule.Quotient.mk z) = ℓ.val z.val := rfl

/-- Evaluation on homology is linear in its transposed cocycle. -/
def dualCycleToDual (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z) (h : g.comp f = 0) :
    LinearMap.ker f.dualMap →ₗ[ℂ] Module.Dual ℂ (PairHomology f g h) where
  toFun := dualCycleFunctional f g h
  map_add' ℓ m := by
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (pairBoundaries f g) z
    rfl
  map_smul' r ℓ := by
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (pairBoundaries f g) z
    rfl

theorem dualCycleToDual_boundaries (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z)
    (h : g.comp f = 0) :
    pairBoundaries g.dualMap f.dualMap ≤ LinearMap.ker (dualCycleToDual f g h) := by
  intro ℓ hℓ
  change ℓ.val ∈ LinearMap.range g.dualMap at hℓ
  obtain ⟨ψ, hψ⟩ := hℓ
  apply LinearMap.ext
  intro z
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (pairBoundaries f g) z
  change ℓ.val v.val = 0
  rw [← hψ]
  change ψ (g v.val) = 0
  rw [v.property, map_zero]

/-- The canonical map from transposed homology to the dual of actual homology. -/
def dualHomologyMap (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z) (h : g.comp f = 0) :
    DualPairHomology f g h →ₗ[ℂ] Module.Dual ℂ (PairHomology f g h) :=
  (pairBoundaries g.dualMap f.dualMap).liftQ (dualCycleToDual f g h)
    (dualCycleToDual_boundaries f g h)

@[simp] theorem dualHomologyMap_mk (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z)
    (h : g.comp f = 0) (ℓ : LinearMap.ker f.dualMap) (z : LinearMap.ker g) :
    dualHomologyMap f g h (Submodule.Quotient.mk ℓ) (Submodule.Quotient.mk z) =
      ℓ.val z.val := rfl

theorem dualHomologyMap_injective (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z)
    (h : g.comp f = 0) : Function.Injective (dualHomologyMap f g h) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  obtain ⟨ℓ, rfl⟩ := Submodule.mkQ_surjective (pairBoundaries g.dualMap f.dualMap) a
  change (Submodule.Quotient.mk ℓ : DualPairHomology f g h) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change ℓ.val ∈ LinearMap.range g.dualMap
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  apply (Submodule.mem_dualAnnihilator ℓ.val).mpr
  intro z hz
  have he := congrArg (fun F : Module.Dual ℂ (PairHomology f g h) =>
    F (Submodule.Quotient.mk (⟨z,hz⟩ : LinearMap.ker g))) ha
  exact he

theorem dualHomologyMap_surjective (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z)
    (h : g.comp f = 0) : Function.Surjective (dualHomologyMap f g h) := by
  intro F
  let ℓ₀ : LinearMap.ker g →ₗ[ℂ] ℂ := F.comp (pairBoundaries f g).mkQ
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hcycle : ℓ ∈ LinearMap.ker f.dualMap := by
    apply LinearMap.ext
    intro x
    let z : LinearMap.ker g := ⟨f x, LinearMap.congr_fun h x⟩
    have hz : (pairBoundaries f g).mkQ z = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨x,rfl⟩
    have he := LinearMap.congr_fun hℓ z
    change ℓ (f x) = F ((pairBoundaries f g).mkQ z) at he
    rw [hz, map_zero] at he
    exact he
  refine ⟨Submodule.Quotient.mk (⟨ℓ,hcycle⟩ : LinearMap.ker f.dualMap), ?_⟩
  apply LinearMap.ext
  intro z
  obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective (pairBoundaries f g) z
  exact LinearMap.congr_fun hℓ v

/-- Evaluation identifies transposed homology with the full dual of homology. -/
def homologyDualEquiv (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z) (h : g.comp f = 0) :
    DualPairHomology f g h ≃ₗ[ℂ] Module.Dual ℂ (PairHomology f g h) :=
  LinearEquiv.ofBijective (dualHomologyMap f g h)
    ⟨dualHomologyMap_injective f g h, dualHomologyMap_surjective f g h⟩

@[simp] theorem homologyDualEquiv_mk (f : X →ₗ[ℂ] Y) (g : Y →ₗ[ℂ] Z)
    (h : g.comp f = 0) (ℓ : LinearMap.ker f.dualMap) (z : LinearMap.ker g) :
    homologyDualEquiv f g h (Submodule.Quotient.mk ℓ) (Submodule.Quotient.mk z) =
      ℓ.val z.val := rfl

end KhanSL2.Factorization.PerfectDuality
