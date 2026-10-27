module

public import KhanSL2.CELeibniz
public import KhanSL2.Chains.Transpose

@[expose] public section

/-! Coefficient-mode shifts and their adjoints on the concrete finite exterior algebra. -/

noncomputable section
namespace KhanSL2.Modules

/-- Raise each coefficient mode by `m`, leaving the positive-current factors fixed. -/
def raiseBGenerator (m : ℕ) : Mode → Cochain
  | .b j a => generator (.b (j + m) a)
  | .c _ _ => 0

/-- The transpose generator rule: lower coefficient modes, with zero below degree `m`. -/
def lowerBGenerator (m : ℕ) : Mode → Cochain
  | .b j a => if m ≤ j then generator (.b (j - m) a) else 0
  | .c _ _ => 0

def raiseB (m : ℕ) : Module.End ℂ Cochain := extendDerivation (raiseBGenerator m)
def lowerB (m : ℕ) : Module.End ℂ Cochain := extendDerivation (lowerBGenerator m)

@[simp] theorem raiseB_generator (m : ℕ) (v : Mode) :
    raiseB m (generator v) = raiseBGenerator m v := extendDerivation_generator _ _
@[simp] theorem lowerB_generator (m : ℕ) (v : Mode) :
    lowerB m (generator v) = lowerBGenerator m v := extendDerivation_generator _ _
@[simp] theorem raiseB_one (m : ℕ) : raiseB m 1 = 0 := extendDerivation_one _
@[simp] theorem lowerB_one (m : ℕ) : lowerB m 1 = 0 := extendDerivation_one _

theorem raiseBGenerator_parity (m : ℕ) (v : Mode) :
    cochainParity (raiseBGenerator m v) = -raiseBGenerator m v := by
  cases v <;> simp [raiseBGenerator]

theorem lowerBGenerator_parity (m : ℕ) (v : Mode) :
    cochainParity (lowerBGenerator m v) = -lowerBGenerator m v := by
  cases v <;> simp [lowerBGenerator]
  split <;> simp

theorem raiseB_mul (m : ℕ) (u v : Cochain) :
    raiseB m (u * v) = raiseB m u * v + u * raiseB m v := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective
  intro a
  exact (FiniteExterior.wedge_comm_of_parity_odd Mode.code Mode.code_injective
    (raiseBGenerator m a) (raiseBGenerator_parity m a) u).symm

theorem lowerB_mul (m : ℕ) (u v : Cochain) :
    lowerB m (u * v) = lowerB m u * v + u * lowerB m v := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective
  intro a
  exact (FiniteExterior.wedge_comm_of_parity_odd Mode.code Mode.code_injective
    (lowerBGenerator m a) (lowerBGenerator_parity m a) u).symm

theorem raiseBGenerator_degree (m : ℕ) (v : Mode) :
    raiseBGenerator m v ∈ cochainPiece ((1, (v.bCount : ℤ), (v.weight : ℤ)) + (0, 0, (m : ℤ))) := by
  cases v with
  | b j a => simpa [raiseBGenerator, Mode.bCount, Mode.weight, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
      cochain_generator_mem (.b (j + m) a)
  | c j a => exact (cochainPiece _).zero_mem

theorem lowerBGenerator_degree (m : ℕ) (v : Mode) :
    lowerBGenerator m v ∈ cochainPiece ((1, (v.bCount : ℤ), (v.weight : ℤ)) + (0, 0, -(m : ℤ))) := by
  cases v with
  | b j a =>
    change (if m ≤ j then _ else _) ∈ _
    split_ifs with h
    · have hd : ((1, ((Mode.b (j - m) a).bCount : ℤ), ((Mode.b (j - m) a).weight : ℤ)) : Degree) =
          (1, ((Mode.b j a).bCount : ℤ), ((Mode.b j a).weight : ℤ)) + (0, 0, -(m : ℤ)) := by
        simp only [Mode.bCount, Mode.weight, Prod.mk_add_mk, Nat.cast_one, add_zero, Nat.cast_add]
        congr 2
        omega
      rw [← hd]
      exact cochain_generator_mem _
    · exact (cochainPiece _).zero_mem
  | c j a => exact (cochainPiece _).zero_mem

theorem raiseB_homogeneous (m : ℕ) : IsHomogeneousOp (raiseB m) (0, 0, (m : ℤ)) :=
  fun _ _ hu => extendDerivation_degree _ _ (raiseBGenerator_degree m) hu

theorem lowerB_homogeneous (m : ℕ) : IsHomogeneousOp (lowerB m) (0, 0, -(m : ℤ)) :=
  fun _ _ hu => extendDerivation_degree _ _ (lowerBGenerator_degree m) hu

end KhanSL2.Modules
