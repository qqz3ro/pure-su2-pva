module

public import KhanSL2.SymmetricFamily.RootAssignmentTransport

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The canonical quotient-map version of root-assignment splitting. Its
component maps are literal quotient maps, including for the zero base algebra. -/

noncomputable section
namespace KhanSL2.SymmetricFamily
open Factorization.WeightedRoots

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]

/-- The canonical map to all actual root-assignment quotients. -/
def rootAssignmentMap {r s : ℕ} (c : Collision.ChartData k r s A) :
    RootBase k A →ₐ[A] ∀ S : Assignment k r, RootBase k A ⧸ assignmentFactorIdeal k A c S :=
  AlgHom.pi fun _ => Ideal.Quotient.mkₐ A _

/-- Coprime root splitting proves that this exact canonical map is bijective. -/
theorem rootAssignmentMap_bijective {r s : ℕ} (c : Collision.ChartData k r s A) :
    Function.Bijective (rootAssignmentMap k A c) := by
  classical
  rcases subsingleton_or_nontrivial (RootBase k A) with ht | ht
  · let := ht
    constructor
    · intro x y _
      exact Subsingleton.elim x y
    · intro y
      exact ⟨0,Subsingleton.elim _ _⟩
  · let := ht
    have hd : (c.f₁.map (algebraMap A (RootBase k A))).natDegree = r :=
      (c.monic₁.natDegree_map _).trans c.degree₁
    let K := fun S : Finset (Fin k) =>
      factorIdeal (c.f₁.map (algebraMap A (RootBase k A)))
        (c.f₂.map (algebraMap A (RootBase k A))) (baseRoot k A) (fun _ => 1) S
    have he := (baseRootSplitting k A c).bijective
    change Function.Bijective (fun (x : RootBase k A)
      (σ : Admissible (fun _ : Fin k => 1) (c.f₁.map (algebraMap A (RootBase k A))).natDegree) =>
        Ideal.Quotient.mk (K (selected σ.val)) x) at he
    have hreindex (d e : ℕ) (h : d = e) :
        Function.Bijective (fun (x : RootBase k A) (σ : Admissible (fun _ : Fin k => 1) d) =>
          Ideal.Quotient.mk (K (selected σ.val)) x) ↔
        Function.Bijective (fun (x : RootBase k A) (σ : Admissible (fun _ : Fin k => 1) e) =>
          Ideal.Quotient.mk (K (selected σ.val)) x) := by
      subst e
      rfl
    have hb := (hreindex _ _ hd).mp he
    let E := (Equiv.piCongrLeft (fun S : Assignment k r => RootBase k A ⧸ K S.val)
      (assignmentEquiv k r)).symm
    change Function.Bijective (fun x : RootBase k A => E (rootAssignmentMap k A c x)) at hb
    constructor
    · intro x y h
      exact hb.1 (congrArg E h)
    · intro y
      obtain ⟨x,hx⟩ := hb.2 (E y)
      exact ⟨x,E.injective hx⟩

/-- Root splitting with the literal canonical component maps. -/
def canonicalRootAssignmentSplitting {r s : ℕ} (c : Collision.ChartData k r s A) :
    RootBase k A ≃ₐ[A] ∀ S : Assignment k r, RootBase k A ⧸ assignmentFactorIdeal k A c S :=
  AlgEquiv.ofBijective (rootAssignmentMap k A c) (rootAssignmentMap_bijective k A c)

@[simp] theorem canonicalRootAssignmentSplitting_apply {r s : ℕ}
    (c : Collision.ChartData k r s A) (x : RootBase k A) (S : Assignment k r) :
    canonicalRootAssignmentSplitting k A c x S = Ideal.Quotient.mk _ x := rfl

/-- The actual quotient decomposition intertwines the honest assignment transport. -/
theorem canonicalRootAssignmentSplitting_equivariant {r s : ℕ}
    (c : Collision.ChartData k r s A) (σ : Equiv.Perm (Fin k))
    (S T : Assignment k r) (h : σ • S = T) (x : RootBase k A) :
    (rootAssignmentTransport k A c).move σ S T h
      (canonicalRootAssignmentSplitting k A c x S) =
        canonicalRootAssignmentSplitting k A c (baseRootPermutation k A σ x) T := rfl

end KhanSL2.SymmetricFamily
