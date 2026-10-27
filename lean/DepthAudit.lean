module

-- Import proof bodies, including private project declarations, for the audit.
import all KhanSL2.Depth.Toolkit
import all KhanSL2.Depth.Descent
import all KhanSL2.Depth.GraphRegular
import all KhanSL2.Depth.Collision
import all KhanSL2.Depth.MonicCoeffs
import all KhanSL2.Depth.FiniteMap
import all KhanSL2.Depth.SourceCoords
import all KhanSL2.Depth.TwoBlock
import all KhanSL2.Depth.SourceModules
import all KhanSL2.Depth.SourceDepth
import all KhanSL2.Depth.SourceDescent
import all KhanSL2.DepthStatement

public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

open Lean Elab Command

/-- Audit every safe project declaration reachable from the depth milestone (paper §7). -/
elab "#audit_depth" : command => do
  let env ← getEnv
  for imported in env.header.modules do
    if (`KhanSL2).isPrefixOf imported.module && !imported.importAll then
      throwError "Audit must import all proof bodies for {imported.module}."
  for name in #[`KhanSL2.Depth.kernel_eq_zero_of_depth,
      `KhanSL2.Depth.kernel_eq_zero_of_depth_of_support,
      `KhanSL2.Depth.depth_JB_ge, `KhanSL2.Depth.depth_J_ge,
      `KhanSL2.Depth.source_kernel_eq_zero, `KhanSL2.Depth.milestoneDepth,
      `KhanSL2.Depth.collisionIdeal_isRegular, `KhanSL2.Depth.depth_coord_ge,
      `KhanSL2.Depth.le_depth_of_le_depth_map, `KhanSL2.Depth.length_le_depth_of_projective,
      `KhanSL2.Depth.graph_isRegular, `KhanSL2.Depth.mem_symmBoth_iff,
      `KhanSL2.Depth.blockE_injective, `KhanSL2.Depth.coordToRoots_comp_nu,
      `KhanSL2.Depth.J_finite, `KhanSL2.Depth.diag_le_radical] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "{name} must be a proved theorem."
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`KhanSL2).isPrefixOf ((privateToUserName? name).getD name) && !info.isUnsafe
    then some name else none
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "Forbidden axiom in {name}: {axiomName}"
  logInfo m!"PASS: {names.length} safe project declarations; no sorryAx or additional axioms."

open KhanSL2.Depth MvPolynomial RingTheory.Sequence

-- These annotations pin the exact statements and definitions.

-- The complex, its homology and its cokernels.
example {R : Type} [CommRing R] (C : ℕ → Type) [∀ p, AddCommGroup (C p)] [∀ p, Module R (C p)]
    (d : ∀ p, C (p + 1) →ₗ[R] C p) : cycles C d 0 = ⊤ := rfl
example {R : Type} [CommRing R] (C : ℕ → Type) [∀ p, AddCommGroup (C p)] [∀ p, Module R (C p)]
    (d : ∀ p, C (p + 1) →ₗ[R] C p) (p : ℕ) : cycles C d (p + 1) = LinearMap.ker (d p) := rfl
example {R : Type} [CommRing R] (C : ℕ → Type) [∀ p, AddCommGroup (C p)] [∀ p, Module R (C p)]
    (d : ∀ p, C (p + 1) →ₗ[R] C p) (p : ℕ) :
    homology C d p = (↥(cycles C d p) ⧸ (LinearMap.range (d p)).comap (cycles C d p).subtype) :=
  rfl

-- Lemma 7.1.
#check (kernel_eq_zero_of_depth : ∀ {R : Type} [CommRing R] {C : ℕ → Type}
    [∀ p, AddCommGroup (C p)] [∀ p, Module R (C p)] {d : ∀ p, C (p + 1) →ₗ[R] C p}
    [IsNoetherianRing R] {rs : List R}, IsRegular R rs →
    ∀ [∀ p, Module.Finite R (C p)] [∀ p, Module.Projective R (C p)],
    (∀ p, rs.length < p → Subsingleton (C p)) →
    (∀ p, (d p).comp (d (p + 1)) = 0) →
    ∀ (J : ℕ → Type) [∀ p, AddCommGroup (J p)] [∀ p, Module R (J p)]
      (f : ∀ p, homology C d p →ₗ[R] J p),
    (∀ p, 2 ≤ p → p ≤ rs.length → Function.Surjective (f p)) →
    (∀ p, ∃ n : ℕ, ∀ x ∈ LinearMap.ker (f p), ∀ a ∈ Ideal.ofList rs ^ n, a • x = 0) →
    (∀ p : ℕ, 2 ≤ p → p ≤ rs.length →
      (p : ℕ∞) ≤ (Ideal.ofList rs).depth (ModuleCat.of R (J p))) →
    ∀ p : ℕ, 2 ≤ p → LinearMap.ker (f p) = ⊥)

-- The collision ideal.
example (B : ℕ) : collisionIdeal B = Ideal.ofList (collisionList B) := rfl
example (B : ℕ) : collisionList B =
    ((List.finRange B).filter fun j : Fin B => (j : ℕ) ≠ 0).map (collisionGen B) := rfl
#check (collisionGen_eq : ∀ (B : ℕ) (j : Fin B), collisionGen B j = X j -
    C ((B.choose ((j : ℕ) + 1) : ℂ)) * (C ((1 : ℂ) / B) * X ⟨0, j.pos⟩) ^ ((j : ℕ) + 1))
#check (collisionIdeal_isRegular : ∀ B : ℕ, ∃ rs : List (RB B),
    Ideal.ofList rs = collisionIdeal B ∧ rs.length = B - 1 ∧ IsRegular (RB B) rs)

-- The source modules.
#check (nuStar_X : ∀ (B r s : ℕ) (j : Fin B), nuStar B r s (X j) =
    rename (tupleMap r s) (esymm (Fin r ⊕ Fin s × Fin 3) ℂ ((j : ℕ) + 1)))
example (r s : ℕ) (i : Fin r) : tupleMap r s (Sum.inl i) = Sum.inl i := rfl
example (r s : ℕ) (a : Fin s) (c : Fin 3) : tupleMap r s (Sum.inr (a, c)) = Sum.inr a := rfl
example (r s : ℕ) (f : ZW r s) : f ∈ symmBoth r s ↔ ∀ (σ : Equiv.Perm (Fin r))
    (τ : Equiv.Perm (Fin s)), rename (Sum.map σ τ) f = f := Iff.rfl
example (r s : ℕ) : Fpoly r s = vandermondeZ r s ^ 2 * vandermondeW r s ^ 3 *
    ∏ i : Fin r, ∏ a : Fin s, (X (Sum.inl i) - X (Sum.inr a)) ^ 2 := rfl
example (r s : ℕ) : vandermondeZ r s =
    ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (X (Sum.inl i) - X (Sum.inl j)) := rfl
example (r s : ℕ) : vandermondeW r s =
    ∏ a : Fin s, ∏ b ∈ Finset.Ioi a, (X (Sum.inr a) - X (Sum.inr b)) := rfl
example (B r s : ℕ) (c : RB B) (f : RootsMod B r s) :
    c • f = (nuStar B r s c : ZW r s) * (show ZW r s from f) := rfl
example (B r s : ℕ) (f : RootsMod B r s) : f ∈ J B r s ↔
    ∃ g : ZW r s, g ∈ symmBoth r s ∧ @Eq (ZW r s) f (Fpoly r s * g) := Iff.rfl
example (B p : ℕ) : JB B p = if p ≤ B ∧ 3 ∣ B - p then J B p ((B - p) / 3) else ⊥ := rfl

-- Lemma 7.2.
#check (depth_JB_ge : ∀ B p : ℕ, 0 < p → p < B →
    (p : ℕ∞) ≤ (collisionIdeal B).depth (ModuleCat.of (RB B) (JB B p)))
#check (depth_J_ge : ∀ B r s : ℕ, B = r + 3 * s → 1 ≤ s →
    ((r + s - 1 : ℕ) : ℕ∞) ≤ (collisionIdeal B).depth (ModuleCat.of (RB B) (J B r s)))

-- Lemmas 7.1 and 7.2 together.
#check (source_kernel_eq_zero : ∀ (B : ℕ) (C : ℕ → Type) [∀ p, AddCommGroup (C p)]
    [∀ p, Module (RB B) (C p)] [∀ p, Module.Finite (RB B) (C p)]
    [∀ p, Module.Projective (RB B) (C p)], (∀ p, B - 1 < p → Subsingleton (C p)) →
    ∀ (d : ∀ p, C (p + 1) →ₗ[RB B] C p), (∀ p, (d p).comp (d (p + 1)) = 0) →
    ∀ (ψ : ∀ p, homology C d p →ₗ[RB B] JB B p),
    (∀ p, 2 ≤ p → p < B → Function.Surjective (ψ p)) →
    (∀ p, ∃ n : ℕ, ∀ x ∈ LinearMap.ker (ψ p), ∀ a ∈ collisionIdeal B ^ n, a • x = 0) →
    ∀ p : ℕ, 2 ≤ p → p < B → LinearMap.ker (ψ p) = ⊥)

#audit_depth
#print axioms KhanSL2.Depth.kernel_eq_zero_of_depth
#print axioms KhanSL2.Depth.depth_JB_ge
#print axioms KhanSL2.Depth.source_kernel_eq_zero
#print axioms KhanSL2.Depth.milestoneDepth
