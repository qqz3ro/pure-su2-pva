module

public import KhanSL2.Factorization.RelativeChainsTotalHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! A homogeneous window splits off from total square-zero homology whenever
its actual projection preserves cycles and shifts boundaries as specified. -/

noncomputable section
namespace KhanSL2.Factorization
open BGG.Contraction

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  {dA : Module.End ℂ A} {dB : Module.End ℂ B}

/-- An actual chain-level homogeneous projection and its shifted predecessor.
The cycle and boundary laws are proved separately for each concrete complex. -/
structure HomologyWindowSplit (W : DegreeWindow dA) where
  projection : Module.End ℂ A
  previousProjection : Module.End ℂ A
  projection_mem : ∀ u, projection u ∈ W.current
  previousProjection_mem : ∀ u, previousProjection u ∈ W.previous
  projection_of_mem : ∀ u ∈ W.current, projection u = u
  projection_mem_ker : ∀ u ∈ LinearMap.ker dA, projection u ∈ LinearMap.ker dA
  projection_differential : ∀ u, projection (dA u) = dA (previousProjection u)

namespace HomologyWindowSplit
variable {W : DegreeWindow dA} (P : HomologyWindowSplit W)

def cycleInclusion (_P : HomologyWindowSplit W) : W.cycles →ₗ[ℂ] LinearMap.ker dA where
  toFun u := ⟨u.val,u.property.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cycleProjection : LinearMap.ker dA →ₗ[ℂ] W.cycles :=
  (P.projection.comp (LinearMap.ker dA).subtype).codRestrict _
    (fun u => ⟨P.projection_mem u.val,P.projection_mem_ker u.val u.property⟩)

def inclusion (hd : dA.comp dA = 0) :
    W.homology hd →ₗ[ℂ] PerfectDuality.PairHomology dA dA hd :=
  W.boundaries.mapQ (PerfectDuality.pairBoundaries dA dA) P.cycleInclusion
    (by rintro u ⟨v,hv,hvu⟩; exact ⟨v,hvu⟩)

def homologyProjection (hd : dA.comp dA = 0) :
    PerfectDuality.PairHomology dA dA hd →ₗ[ℂ] W.homology hd :=
  (PerfectDuality.pairBoundaries dA dA).mapQ W.boundaries P.cycleProjection (by
    rintro u ⟨v,hvu⟩
    exact ⟨P.previousProjection v,P.previousProjection_mem v,by
      change dA (P.previousProjection v) = P.projection u.val
      rw [← P.projection_differential,hvu]
      rfl⟩)

@[simp] theorem projection_inclusion (hd : dA.comp dA = 0) (u : W.homology hd) :
    P.homologyProjection hd (P.inclusion hd u) = u := by
  obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective W.boundaries u
  change Submodule.Quotient.mk (P.cycleProjection (P.cycleInclusion v)) = Submodule.Quotient.mk v
  congr 1
  apply Subtype.ext
  exact P.projection_of_mem v.val v.property.1

theorem inclusion_injective (hd : dA.comp dA = 0) : Function.Injective (P.inclusion hd) :=
  Function.LeftInverse.injective (P.projection_inclusion hd)

end HomologyWindowSplit

/-- The total short-complex map specified by a genuine commuting linear map. -/
def totalPairMap (f : A →ₗ[ℂ] B) (hf : f.comp dA = dB.comp f) :
    PerfectDuality.PairMap dA dA dB dB where
  left := f
  middle := f
  right := f
  comm_in := hf
  comm_out := hf

/-- A genuine degree-preserving map which is an isomorphism on total homology
is an isomorphism on each split homogeneous window. -/
theorem windowHomologyMap_bijective_of_total
    (W : DegreeWindow dA) (V : DegreeWindow dB)
    (P : HomologyWindowSplit W) (Q : HomologyWindowSplit V)
    (f : A →ₗ[ℂ] B) (hdA : dA.comp dA = 0) (hdB : dB.comp dB = 0)
    (hf : f.comp dA = dB.comp f)
    (hc : ∀ u ∈ W.current, f u ∈ V.current)
    (hp : ∀ u ∈ W.previous, f u ∈ V.previous)
    (hproj : ∀ u, f (P.projection u) = Q.projection (f u))
    (htotal : Function.Bijective ((totalPairMap f hf).homologyMap hdA hdB)) :
    Function.Bijective (W.homologyMap V f hdA hdB hf hc hp) := by
  apply bijective_of_split_components
    (P.inclusion hdA) (P.homologyProjection hdA)
    (Q.inclusion hdB) (Q.homologyProjection hdB)
    (P.projection_inclusion hdA) (Q.projection_inclusion hdB)
    (W.homologyMap V f hdA hdB hf hc hp)
    ((totalPairMap f hf).homologyMap hdA hdB) htotal
  · intro u
    obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective W.boundaries u
    rfl
  · intro u
    obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective (PerfectDuality.pairBoundaries dA dA) u
    change Submodule.Quotient.mk
      (W.cyclesMap V f hf hc (P.cycleProjection v)) =
        Submodule.Quotient.mk (Q.cycleProjection ((totalPairMap f hf).cyclesMap v))
    congr 1
    apply Subtype.ext
    exact hproj v.val

/-- The general splitting specializes to the actual relative exterior-degree projection. -/
def relativeHomologyWindowSplit (N : Type*) [AddCommGroup N] [Module ℂ N]
    [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N] (j : ℕ) :
    HomologyWindowSplit (window N j) where
  projection := degreeProjection N j
  previousProjection := degreeProjection N (j+1)
  projection_mem := degreeProjection_mem N j
  previousProjection_mem := degreeProjection_mem N (j+1)
  projection_of_mem := fun _ hu => degreeProjection_of_mem N hu
  projection_mem_ker := fun _ hu => degreeProjection_mem_ker N j hu
  projection_differential := degreeProjection_differential N j

end KhanSL2.Factorization
