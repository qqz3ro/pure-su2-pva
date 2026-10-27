module

public import KhanSL2.BGG.ColorRootEquivariance
public import KhanSL2.BGG.ExteriorEuler

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The color/root equivalence preserves exterior degree and physical current energy. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.BGG.PositiveCE

def monomialEnergy (s : Finset Mode) : ℕ := ∑ m ∈ s, (m.index + 1)

def piece (d N : ℕ) : Submodule ℂ Cochain :=
  Finsupp.supported ℂ ℂ {s : Finset Mode | s.card = d ∧ monomialEnergy s = N}

/-- Exterior degree counted by an ordinary Euler derivation. -/
def degreeOp : Module.End ℂ Cochain := FiniteExterior.euler (fun _ => 1)

/-- Physical current energy counted by an ordinary Euler derivation. -/
def energyOp : Module.End ℂ Cochain :=
  FiniteExterior.euler (fun m : Mode => ((m.index + 1 : ℕ) : ℂ))

@[simp] theorem energyOp_one : energyOp 1 = 0 := FiniteExterior.euler_one _

@[simp] theorem energyOp_generator (m : Mode) :
    energyOp (FiniteExterior.generator m) =
      ((m.index + 1 : ℕ) : ℂ) • FiniteExterior.generator m := FiniteExterior.euler_generator _ _

theorem energyOp_mul (u v : Cochain) :
    energyOp (u * v) = energyOp u * v + u * energyOp v := FiniteExterior.euler_mul _ _ _

theorem energyOp_monomial (s : Finset Mode) :
    energyOp (FiniteExterior.monomial s) = (monomialEnergy s : ℂ) • FiniteExterior.monomial s := by
  rw [energyOp, FiniteExterior.euler_monomial]
  simp only [monomialEnergy, Nat.cast_sum]

theorem energyOp_apply (u : Cochain) (s : Finset Mode) :
    energyOp u s = (monomialEnergy s : ℂ) * u s := by
  rw [energyOp, FiniteExterior.euler_apply]
  simp only [monomialEnergy, Nat.cast_sum]

theorem mem_piece_iff_euler (u : Cochain) (d N : ℕ) :
    u ∈ piece d N ↔ degreeOp u = (d : ℂ) • u ∧ energyOp u = (N : ℂ) • u :=
  FiniteExterior.mem_degree_energy_iff_euler (fun m : Mode => m.index + 1) d N u

end KhanSL2.BGG.PositiveCE

namespace KhanSL2.BGG.ColorRoot

theorem euler_rootAt (w : ℕ → ℂ) (n : ℕ) (x : G) :
    FiniteExterior.euler (fun i : RootMode => w i.1) (rootAt n x) = w n • rootAt n x := by
  simp [rootAt_apply, map_sum, Finset.smul_sum, smul_smul, mul_comm]

theorem euler_colorAt (w : ℕ → ℂ) (n : ℕ) (x : G) :
    FiniteExterior.euler (fun m : PositiveCE.Mode => w m.index) (colorAt n x) =
      w n • colorAt n x := by
  simp [colorAt_apply, map_sum, Finset.smul_sum, smul_smul, mul_comm]

/-- Any weighting depending only on the current mode is preserved by color/root substitution. -/
theorem euler_toRoot (w : ℕ → ℂ) (u : PositiveCE.Cochain) :
    FiniteExterior.euler (fun i : RootMode => w i.1) (toRoot u) =
      toRoot (FiniteExterior.euler (fun m : PositiveCE.Mode => w m.index) u) := by
  apply FiniteExterior.euler_algHom toRoot
  intro m
  obtain ⟨n, a⟩ := m
  rw [toRoot_generator, euler_rootAt, map_smul, toRoot_generator]

theorem euler_toColor (w : ℕ → ℂ) (u : RootExterior) :
    FiniteExterior.euler (fun m : PositiveCE.Mode => w m.index) (toColor u) =
      toColor (FiniteExterior.euler (fun i : RootMode => w i.1) u) := by
  apply FiniteExterior.euler_algHom toColor
  intro i
  obtain ⟨n, a⟩ := i
  rw [toColor_generator, euler_colorAt, map_smul, toColor_generator]

/-- The specified equivalence preserves both degree and energy, in both directions. -/
theorem toRoot_mem_piece_iff (u : PositiveCE.Cochain) (d N : ℕ) :
    toRoot u ∈ rootExteriorPiece d N ↔ u ∈ PositiveCE.piece d N := by
  rw [show toRoot u ∈ rootExteriorPiece d N ↔
      FiniteExterior.euler (fun _ : RootMode => (1 : ℂ)) (toRoot u) = (d : ℂ) • toRoot u ∧
      FiniteExterior.euler (fun i : RootMode => ((i.1 + 1 : ℕ) : ℂ)) (toRoot u) =
        (N : ℂ) • toRoot u from
    FiniteExterior.mem_degree_energy_iff_euler (fun i : RootMode => i.1 + 1) d N (toRoot u)]
  rw [PositiveCE.mem_piece_iff_euler]
  rw [euler_toRoot (fun _ => 1), euler_toRoot (fun n => ((n + 1 : ℕ) : ℂ))]
  have hinj : Function.Injective toRoot := equiv.injective
  simp only [← map_smul, hinj.eq_iff, PositiveCE.degreeOp, PositiveCE.energyOp]

theorem toColor_mem_piece_iff (u : RootExterior) (d N : ℕ) :
    toColor u ∈ PositiveCE.piece d N ↔ u ∈ rootExteriorPiece d N := by
  have h := (toRoot_mem_piece_iff (toColor u) d N).symm
  have hInv : toRoot (toColor u) = u := equiv.apply_symm_apply u
  simpa only [hInv] using h

/-- The coordinate change restricts to a linear equivalence on each finite degree-energy piece. -/
def pieceEquiv (d N : ℕ) : PositiveCE.piece d N ≃ₗ[ℂ] rootExteriorPiece d N where
  toFun u := ⟨toRoot u, (toRoot_mem_piece_iff u d N).mpr u.property⟩
  invFun u := ⟨toColor u, (toColor_mem_piece_iff u d N).mpr u.property⟩
  left_inv u := Subtype.ext (equiv.symm_apply_apply u)
  right_inv u := Subtype.ext (equiv.apply_symm_apply u)
  map_add' u v := Subtype.ext (map_add toRoot (u : PositiveCE.Cochain) (v : PositiveCE.Cochain))
  map_smul' r u := Subtype.ext (map_smul toRoot r (u : PositiveCE.Cochain))

theorem toRoot_positiveAction (x : G) (u : PositiveCE.Cochain) :
    toRoot (positiveAction x u) = rootExteriorAction x (toRoot u) := by
  rw [positiveAction_apply]
  exact equiv.apply_symm_apply _

end KhanSL2.BGG.ColorRoot

namespace KhanSL2.BGG.PositiveCE

instance finiteDimensional_piece (d N : ℕ) : FiniteDimensional ℂ (piece d N) :=
  FiniteDimensional.of_injective (ColorRoot.pieceEquiv d N).toLinearMap
    (ColorRoot.pieceEquiv d N).injective

theorem positiveAction_mem_piece (x : G) {d N : ℕ} {u : Cochain} (hu : u ∈ piece d N) :
    ColorRoot.positiveAction x u ∈ piece d N := by
  apply (ColorRoot.toRoot_mem_piece_iff _ d N).mp
  rw [ColorRoot.toRoot_positiveAction]
  exact rootExteriorAction_mem_piece x ((ColorRoot.toRoot_mem_piece_iff _ d N).mpr hu)

/-- Fixed degree and energy in the actual pure-positive CE model is a finite-dimensional sl₂ module. -/
def liePiece (d N : ℕ) : LieSubmodule ℂ G Cochain :=
  { piece d N with lie_mem := fun {x _u} hu => positiveAction_mem_piece x hu }

instance finiteDimensional_liePiece (d N : ℕ) : FiniteDimensional ℂ (liePiece d N) :=
  inferInstanceAs (FiniteDimensional ℂ (piece d N))

end KhanSL2.BGG.PositiveCE
namespace KhanSL2.BGG.ColorRoot

/-- The coordinate equivalence on finite pieces also intertwines the actual sl₂ representations. -/
def liePieceEquiv (d N : ℕ) : PositiveCE.liePiece d N ≃ₗ⁅ℂ,G⁆ rootExteriorLiePiece d N :=
  { pieceEquiv d N with map_lie' := fun {x u} => Subtype.ext (toRoot_positiveAction x u) }

end KhanSL2.BGG.ColorRoot