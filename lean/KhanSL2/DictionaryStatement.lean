module

public import KhanSL2.Chains.RelativeComplex
public import KhanSL2.Chains.Psi

@[expose] public section

/-!
# Milestone M2: relative CE homology, the dictionary, and surjectivity of `ψ`

Notation: `𝔤 = 𝔰𝔩₂`, `𝔩 = 𝔤[z]`, `𝔩₊ = z𝔤[z]`, so `𝔩 = 𝔤 ⋉ 𝔩₊`.

* `K p B S = H_p(𝔩, 𝔤; Λ^B(ε𝔩))_S` is the homology of the relative Chevalley–Eilenberg
  complex `RelChains = (Λ𝔩₊ ⊗ Λ(ε𝔩))_𝔤` with its induced boundary `relBoundary`, in form
  degree `p`, coefficient degree `B` and spin `S`. The chains and the boundary come from the
  general construction `LieChains` (all degrees, `∂² = 0`), and the trigrading is the joint
  eigenspace of three canonical operators (`mem_genPiece_iff`).
* `K p B S` is finite-dimensional.
* `dictionary p B S : cohomologyPiece (B + p, B, S) ≃ₗ[ℂ] Dual (K p B S)`.
* `psiK p B S : K p B S →ₗ[ℂ] Dual (Source.piece (B + p, B, S))` is the transpose of `φ`
  through the dictionary (`psiK_apply`), and it is surjective (`psiK_surjective`).
-/

noncomputable section

namespace KhanSL2.Current

/-- The trigrading index of `K p B S`: total exterior degree `B + p`, `b`-count `B`, spin `S`. -/
def kDegree (p B : ℕ) (S : ℤ) : Degree := (((B + p : ℕ) : ℤ), (B : ℤ), S)

/-- **`K^B_{p,S} = H_p(𝔩, 𝔤; Λ^B(ε𝔩))_S`**, the homology of the relative CE complex. -/
abbrev K (p B : ℕ) (S : ℤ) : Type := RelComplexHomology (kDegree p B S)

/-- The degree pieces of the chains are the joint eigenspaces of form degree, coefficient degree
and spin. -/
theorem mem_kPiece_iff (p B : ℕ) (S : ℤ) (ξ : GenChains) :
    ξ ∈ genPiece (kDegree p B S) ↔
      formDegree ξ = (p : ℂ) • ξ ∧ coeffDegree ξ = (B : ℂ) • ξ ∧ spin ξ = (S : ℂ) • ξ :=
  mem_genPiece_iff p B S ξ

/-- `K p B S` is finite-dimensional. -/
theorem K_finiteDimensional (p B : ℕ) (S : ℤ) : FiniteDimensional ℂ (K p B S) := inferInstance

/-- **The dictionary**: the restricted relative cohomology in degree `(B + p, B, S)` is the
dual of `K p B S`. -/
def dictionary (p B : ℕ) (S : ℤ) :
    cohomologyPiece (kDegree p B S) ≃ₗ[ℂ] Module.Dual ℂ (K p B S) :=
  (cohomologyPieceEquivDualRel (kDegree p B S)).trans
    (relHomologyEquivComplex (kDegree p B S)).symm.dualMap

/-- **`ψ`**: the map `K p B S → Dual (Source.piece (B + p, B, S))`. -/
def psiK (p B : ℕ) (S : ℤ) : K p B S →ₗ[ℂ] Module.Dual ℂ (Source.piece (kDegree p B S)) :=
  psiRel (kDegree p B S) ∘ₗ (relHomologyEquivComplex (kDegree p B S)).symm.toLinearMap

/-- `ψ` is the transpose of `φ` through the dictionary. -/
theorem psiK_apply (p B : ℕ) (S : ℤ) (k : K p B S) (a : Source.piece (kDegree p B S)) :
    psiK p B S k a = dictionary p B S (phiPiece (kDegree p B S) a) k := rfl

/-- **`ψ` is surjective.** -/
theorem psiK_surjective (p B : ℕ) (S : ℤ) : Function.Surjective (psiK p B S) :=
  (psiRel_surjective _).comp (relHomologyEquivComplex _).symm.surjective

/-- **Milestone M2**, in one statement. -/
theorem milestoneM2 (p B : ℕ) (S : ℤ) :
    FiniteDimensional ℂ (K p B S) ∧
      Nonempty (cohomologyPiece (kDegree p B S) ≃ₗ[ℂ] Module.Dual ℂ (K p B S)) ∧
      Function.Surjective (psiK p B S) :=
  ⟨K_finiteDimensional p B S, ⟨dictionary p B S⟩, psiK_surjective p B S⟩

end KhanSL2.Current
