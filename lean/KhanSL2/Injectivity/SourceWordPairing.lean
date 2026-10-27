module

public import KhanSL2.Injectivity.CartanFunctional
public import KhanSL2.Injectivity.SourceSectors

/-! The actual canonical map on complete source jet words, evaluated by
closed Cartan functionals. Cochain representatives are chosen only for words;
no algebra lift of the source quotient to cochains is asserted. -/

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity

theorem translation_pow_mem_cycles (n : ℕ) {u : Cochain} (hu : u ∈ relativeCycles) :
    (translation ^ n) u ∈ relativeCycles := by
  induction n with
  | zero => exact hu
  | succ n hn =>
    rw [pow_succ', Module.End.mul_apply]
    exact CohomologyDescent.cycle_translation relativeComplex_laws.translation_commutes hn

theorem target_translation_pow_classOf (n : ℕ) (u : Cochain) (hu : u ∈ relativeCycles) :
    (targetData.translation ^ n) (classOf u hu) =
      classOf ((translation ^ n) u) (translation_pow_mem_cycles n hu) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', Module.End.mul_apply, hn, target_translation_classOf]
    apply congrArg (Submodule.Quotient.mk : CycleSpace → Cohomology)
    apply Subtype.ext
    change translation ((translation ^ n) u) = (translation ^ (n + 1)) u
    rw [pow_succ', Module.End.mul_apply]

def representativeProduct (u : Cochain) (ns : List ℕ) : Cochain :=
  (ns.map fun n => (translation ^ n) u).prod

@[simp] theorem representativeProduct_nil (u : Cochain) : representativeProduct u [] = 1 := rfl

@[simp] theorem representativeProduct_cons (u : Cochain) (n : ℕ) (ns : List ℕ) :
    representativeProduct u (n :: ns) = (translation ^ n) u * representativeProduct u ns := rfl

theorem representativeProduct_mem_cycles (u : Cochain) (hu : u ∈ relativeCycles) (ns : List ℕ) :
    representativeProduct u ns ∈ relativeCycles := by
  induction ns with
  | nil => exact one_mem_cycles
  | cons n ns hn =>
    exact cycle_wedge (translation_pow_mem_cycles n hu) hn

theorem phi_xProduct (xs : List ℕ) :
    phi (Source.xProduct xs) = classOf (representativeProduct xRepresentative xs)
      (representativeProduct_mem_cycles _ xRepresentative_mem_cycles xs) := by
  induction xs with
  | nil =>
    rw [Source.xProduct_nil, phi_one]
    exact target_one_classOf
  | cons n ns hn =>
    rw [Source.xProduct_cons, phi_mul, phi_X, hn]
    change targetData.mul ((targetData.translation ^ n)
      (classOf xRepresentative xRepresentative_mem_cycles)) _ = _
    rw [target_translation_pow_classOf, target_mul_classOf]
    rfl

theorem phi_yProduct (ys : List ℕ) :
    phi (Source.yProduct ys) = classOf (representativeProduct yRepresentative ys)
      (representativeProduct_mem_cycles _ yRepresentative_mem_cycles ys) := by
  induction ys with
  | nil =>
    rw [Source.yProduct_nil, phi_one]
    exact target_one_classOf
  | cons n ns hn =>
    rw [Source.yProduct_cons, phi_mul, phi_Y, hn]
    change targetData.mul ((targetData.translation ^ n)
      (classOf yRepresentative yRepresentative_mem_cycles)) _ = _
    rw [target_translation_pow_classOf, target_mul_classOf]
    rfl

theorem phi_jetMonomial (xs ys : List ℕ) :
    phi (Source.jetMonomial xs ys) =
      classOf (representativeProduct xRepresentative xs * representativeProduct yRepresentative ys)
        (cycle_wedge (representativeProduct_mem_cycles _ xRepresentative_mem_cycles xs)
          (representativeProduct_mem_cycles _ yRepresentative_mem_cycles ys)) := by
  rw [Source.jetMonomial, phi_mul, phi_xProduct, phi_yProduct, target_mul_classOf]
  rfl

namespace Cartan

def jetProduct (u : Cochain) (ns : List ℕ) : Cochain :=
  (ns.map fun n => (translation ^ n) u).prod

@[simp] theorem jetProduct_nil (u : Cochain) : jetProduct u [] = 1 := rfl

@[simp] theorem jetProduct_cons (u : Cochain) (n : ℕ) (ns : List ℕ) :
    jetProduct u (n :: ns) = (translation ^ n) u * jetProduct u ns := rfl

theorem restriction_representativeProduct (u : KhanSL2.Cochain) (ns : List ℕ) :
    restriction (representativeProduct u ns) = jetProduct (restriction u) ns := by
  induction ns with
  | nil => exact map_one restriction
  | cons n ns hn =>
    rw [representativeProduct_cons, map_mul, restriction_translation_pow, hn, jetProduct_cons]

theorem jetProduct_smul (a : ℂ) (u : Cochain) (ns : List ℕ) :
    jetProduct (a • u) ns = a ^ ns.length • jetProduct u ns := by
  induction ns with
  | nil => simp
  | cons n ns hn =>
    simp only [jetProduct_cons, map_smul, hn, List.length_cons,
      smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]

def xBase : Cochain := generator (.neutral 0) * generator (.cartan 0)

def yBase : Cochain := (generator (.neutral 0) * generator (.plus 0)) * generator (.minus 0)

def sourceWord (xs ys : List ℕ) : Cochain := jetProduct xBase xs * jetProduct yBase ys

theorem restriction_jetMonomial_representative (xs ys : List ℕ) :
    restriction (representativeProduct xRepresentative xs * representativeProduct yRepresentative ys) =
      (-2 : ℂ) ^ ys.length • sourceWord xs ys := by
  rw [map_mul, restriction_representativeProduct, restriction_representativeProduct,
    restriction_xRepresentative, restriction_yRepresentative]
  change jetProduct xBase xs * jetProduct ((-2 : ℂ) • yBase) ys = _
  rw [jetProduct_smul, mul_smul_comm]
  rfl

end Cartan

theorem descendCartanFunctional_phi_jetMonomial
    (f : Cartan.Cochain →ₗ[ℂ] ℂ) (hf : ∀ u, f (Cartan.q u) = 0) (xs ys : List ℕ) :
    descendCartanFunctional f hf (phi (Source.jetMonomial xs ys)) =
      (-2 : ℂ) ^ ys.length * f (Cartan.sourceWord xs ys) := by
  rw [phi_jetMonomial]
  change f (Cartan.restriction
    (representativeProduct xRepresentative xs * representativeProduct yRepresentative ys)) = _
  rw [Cartan.restriction_jetMonomial_representative, map_smul, smul_eq_mul]

end KhanSL2.Injectivity
