module

public import KhanSL2.BasisGrading
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-! Homogeneous components, their restriction to graded subspaces, and quotients. -/

noncomputable section

namespace KhanSL2

variable {ι A B : Type*} [DecidableEq ι]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

def sumComponents : (ι →₀ A) →ₗ[ℂ] A :=
  Finsupp.lsum ℂ fun _ => LinearMap.id

omit [DecidableEq ι] in
@[simp] theorem sumComponents_single (i : ι) (a : A) :
    sumComponents (Finsupp.single i a) = a := by
  simp [sumComponents, Finsupp.lsum_single]

omit [DecidableEq ι] in
theorem map_sumComponents (f : A →ₗ[ℂ] B) (v : ι →₀ A) :
    f (sumComponents v) = sumComponents (Finsupp.mapRange.linearMap f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single i a => simp

/-- Explicit finite homogeneous decomposition. This contains proofs, not
assumed instances, and provides the internal direct-sum certificate. -/
structure GradingDecomposition (piece : ι → Submodule ℂ A) where
  components : A →ₗ[ℂ] (ι →₀ A)
  component_mem : ∀ a d, components a d ∈ piece d
  homogeneous : ∀ d a, a ∈ piece d → components a = Finsupp.single d a
  total : ∀ a, sumComponents (components a) = a

namespace GradingDecomposition

variable {piece : ι → Submodule ℂ A} (G : GradingDecomposition piece)

theorem component_directSum (v : DirectSum ι fun d => piece d) (d : ι) :
    G.components (DirectSum.coeLinearMap piece v) d = (v d : A) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of e v =>
    rw [DirectSum.coeLinearMap_of, G.homogeneous e v v.property]
    by_cases h : e = d
    · subst e
      simp
    · simp [Finsupp.single_eq_of_ne' h, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add v w hv hw =>
    simp only [map_add, Finsupp.add_apply, DirectSum.add_apply, Submodule.coe_add]
    rw [hv, hw]

include G in
theorem isInternal : DirectSum.IsInternal piece := by
  classical
  have heq : DirectSum.coeAddMonoidHom piece =
      (DirectSum.coeLinearMap piece).toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro v
    change DirectSum.coeAddMonoidHom piece v = DirectSum.coeLinearMap piece v
    rw [DirectSum.coeLinearMap_eq_dfinsuppSum,
      DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
  unfold DirectSum.IsInternal
  rw [heq]
  change Function.Bijective (DirectSum.coeLinearMap piece)
  constructor
  · intro v w hvw
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    rw [← G.component_directSum v d, ← G.component_directSum w d, hvw]
  · apply LinearMap.range_eq_top.mp
    rw [DirectSum.range_coeLinearMap]
    apply top_unique
    intro a _
    rw [← G.total a]
    change (G.components a).sum (fun _ v => v) ∈ ⨆ d, piece d
    apply Submodule.sum_mem
    intro d _
    exact Submodule.mem_iSup_of_mem d (G.component_mem a d)

variable (S : Submodule ℂ A)
  (hS : ∀ a ∈ S, ∀ d, G.components a d ∈ S)

def restrictComponents : S →ₗ[ℂ] (ι →₀ S) where
  toFun a := Finsupp.onFinset (G.components a).support
    (fun d => ⟨G.components a d, hS a a.property d⟩)
    (fun d hd => Finsupp.mem_support_iff.mpr fun hz => hd (Subtype.ext hz))
  map_add' a b := by
    apply Finsupp.ext
    intro d
    apply Subtype.ext
    exact congrArg (fun v : ι →₀ A => v d) (G.components.map_add a b)
  map_smul' r a := by
    apply Finsupp.ext
    intro d
    apply Subtype.ext
    exact congrArg (fun v : ι →₀ A => v d) (G.components.map_smul r a)

omit [DecidableEq ι] in
@[simp] theorem restrictComponents_apply (a : S) (d : ι) :
    (G.restrictComponents S hS a d : A) = G.components a d := rfl

omit [DecidableEq ι] in
theorem restrictComponents_map (a : S) :
    Finsupp.mapRange.linearMap S.subtype (G.restrictComponents S hS a) =
      G.components a := by
  ext d
  rfl

def restrict : GradingDecomposition (fun d => (piece d).comap S.subtype) where
  components := G.restrictComponents S hS
  component_mem a d := G.component_mem a d
  homogeneous d a ha := by
    apply Finsupp.ext
    intro e
    apply Subtype.ext
    change G.components a e = (Finsupp.single d a e : A)
    rw [G.homogeneous d a ha]
    by_cases h : d = e <;> simp [Finsupp.single_apply, h]
  total a := by
    apply Subtype.ext
    change S.subtype (sumComponents (G.restrictComponents S hS a)) = a
    rw [map_sumComponents, G.restrictComponents_map, G.total]

def quotientComponents : (A ⧸ S) →ₗ[ℂ] (ι →₀ (A ⧸ S)) :=
  S.liftQ ((Finsupp.mapRange.linearMap S.mkQ).comp G.components) (by
    intro a ha
    apply Finsupp.ext
    intro d
    change S.mkQ (G.components a d) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hS a ha d))

omit [DecidableEq ι] in
@[simp] theorem quotientComponents_mk (a : A) :
    G.quotientComponents S hS (S.mkQ a) =
      Finsupp.mapRange.linearMap S.mkQ (G.components a) := rfl

def quotient : GradingDecomposition (fun d => (piece d).map S.mkQ) where
  components := G.quotientComponents S hS
  component_mem := by
    intro a
    induction a using Quotient.inductionOn' with
    | _ a =>
      intro d
      exact ⟨G.components a d, G.component_mem a d, rfl⟩
  homogeneous := by
    intro d a ha
    obtain ⟨v, hv, rfl⟩ := ha
    rw [quotientComponents_mk, G.homogeneous d v hv]
    simp
  total := by
    intro a
    induction a using Quotient.inductionOn' with
    | _ a =>
      change sumComponents (G.quotientComponents S hS (S.mkQ a)) = S.mkQ a
      rw [quotientComponents_mk, ← map_sumComponents, G.total]

end GradingDecomposition

namespace BasisGrading

variable {α : Type*} (degree : α → ι)

def decomposition : GradingDecomposition (piece degree) where
  components := coaction degree
  component_mem a d := by rw [coaction_apply]; exact projection_mem degree d a
  homogeneous := fun _ _ ha => coaction_of_mem degree ha
  total a := by
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => simp [hp, hq]
    | single i a => simp

end BasisGrading
end KhanSL2
