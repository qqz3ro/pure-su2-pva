module

public import KhanSL2.SymmetricFamily.FactorPermutation
public import KhanSL2.Factorization.OrbitStabilizerTwist

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Scalar-character twists of actual group representations. -/

noncomputable section
namespace KhanSL2.SymmetricFamily

/-- Twist the actual linear group action by the specified scalar character. -/
def scalarTwistRepresentation {R G M : Type*} [CommRing R] [Group G]
    [AddCommGroup M] [Module R M] (χ : G →* Rˣ) (ρ : G →* Module.End R M) :
    G →* Module.End R M where
  toFun g := (χ g : R) • ρ g
  map_one' := by simp only [map_one,Units.val_one,one_smul]
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp only [map_mul,Units.val_mul,LinearMap.smul_apply,Module.End.mul_apply,map_smul,smul_smul,mul_comm]

/-- The original permutation sign, evaluated in the coefficient algebra. -/
def permutationSign (n : ℕ) (R : Type*) [CommRing R] : Equiv.Perm (Fin n) →* Rˣ :=
  (Units.map (Int.castRingHom R)).comp Equiv.Perm.sign

@[simp] theorem permutationSign_val (n : ℕ) (R : Type*) [CommRing R]
    (σ : Equiv.Perm (Fin n)) : (permutationSign n R σ : R) = (σ.sign : R) := rfl

end KhanSL2.SymmetricFamily
