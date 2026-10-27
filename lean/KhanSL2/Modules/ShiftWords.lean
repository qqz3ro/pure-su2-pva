module

public import KhanSL2.Modules.ShiftJets
public import KhanSL2.Injectivity.TaylorCoefficients

@[expose] public section

/-! Coefficient lowering on full source jet words, with their prescribed cochain representatives. -/

noncomputable section
namespace KhanSL2.Modules
open SourceDual

/-- Ordered product of translated representatives. -/
def jetWord {n : ℕ} (a : Cochain) (f : Fin n → ℕ) : Cochain :=
  (List.ofFn fun i => (translation ^ f i) a).prod

@[simp] theorem jetWord_zero (a : Cochain) (f : Fin 0 → ℕ) : jetWord a f = 1 := by
  simp [jetWord]

theorem jetWord_succ {n : ℕ} (a : Cochain) (f : Fin (n+1) → ℕ) :
    jetWord a f = (translation ^ f 0) a * jetWord a (fun i => f i.succ) := by
  simp [jetWord, List.ofFn_succ]

theorem jetWord_update_zero {n : ℕ} (a : Cochain) (f : Fin (n+1) → ℕ) (k : ℕ) :
    jetWord a (Function.update f 0 k) = (translation ^ k) a * jetWord a (fun i => f i.succ) := by
  rw [jetWord_succ]
  simp [Function.update]

theorem jetWord_update_succ {n : ℕ} (a : Cochain) (f : Fin (n+1) → ℕ) (i : Fin n) (k : ℕ) :
    jetWord a (Function.update f i.succ k) =
      (translation ^ f 0) a * jetWord a (Function.update (fun j => f j.succ) i k) := by
  rw [jetWord_succ]
  have h0 : Function.update f i.succ k 0 = f 0 := Function.update_of_ne (Fin.succ_ne_zero i).symm k f
  have ht : (fun j : Fin n => Function.update f i.succ k j.succ) =
      Function.update (fun j => f j.succ) i k := by
    funext j
    simp [Function.update]
  rw [h0, ht]

/-- The even derivation acts on each factor of the ordered word. -/
theorem lowerB_jetWord (m : ℕ) (a : Cochain) (w : ℂ)
    (ha : ∀ k : ℕ, lowerB m ((translation ^ k) a) =
      (w * (k.descFactorial m : ℂ)) • (translation ^ (k-m)) a)
    {n : ℕ} (f : Fin n → ℕ) :
    lowerB m (jetWord a f) = ∑ i : Fin n,
      (w * ((f i).descFactorial m : ℂ)) • jetWord a (Function.update f i (f i-m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [jetWord_succ, lowerB_mul, ha, ih, Fin.sum_univ_succ, jetWord_update_zero]
    simp_rw [jetWord_update_succ]
    rw [smul_mul_assoc, Finset.mul_sum]
    simp only [mul_smul_comm]

/-- The actual representative used by `phi` on a labelled source monomial. -/
def exponentRepresentative {r s : ℕ} (d : Variables r s →₀ ℕ) : Cochain :=
  jetWord xRepresentative (fun i => d (Sum.inl i)) *
    jetWord yRepresentative (fun i => d (Sum.inr i))

theorem jetWord_eq_representativeProduct {n : ℕ} (a : Cochain) (f : Fin n → ℕ) :
    jetWord a f = Injectivity.representativeProduct a (List.ofFn f) := by
  simp [jetWord, Injectivity.representativeProduct, List.map_ofFn, Function.comp_def]

theorem exponentRepresentative_mem_cycles {r s : ℕ} (d : Variables r s →₀ ℕ) :
    exponentRepresentative d ∈ relativeCycles := by
  unfold exponentRepresentative
  rw [jetWord_eq_representativeProduct, jetWord_eq_representativeProduct]
  exact cycle_wedge
    (Injectivity.representativeProduct_mem_cycles _ xRepresentative_mem_cycles _)
    (Injectivity.representativeProduct_mem_cycles _ yRepresentative_mem_cycles _)

theorem phi_exponentMonomial {r s : ℕ} (d : Variables r s →₀ ℕ) :
    phi (exponentMonomial d) = classOf (exponentRepresentative d)
      (exponentRepresentative_mem_cycles d) := by
  rw [exponentMonomial, Injectivity.phi_jetMonomial]
  congr 1
  unfold exponentRepresentative
  rw [jetWord_eq_representativeProduct, jetWord_eq_representativeProduct]

/-- The number of coefficient factors in one source generator. -/
def wordRootWeight {r s : ℕ} : Variables r s → ℂ
  | Sum.inl _ => 1
  | Sum.inr _ => 3

theorem exponentRepresentative_sub_inl {r s : ℕ} (d : Variables r s →₀ ℕ) (i : Fin r) (m : ℕ) :
    exponentRepresentative (d - Finsupp.single (Sum.inl i) m) =
      jetWord xRepresentative (Function.update (fun j => d (Sum.inl j)) i (d (Sum.inl i)-m)) *
        jetWord yRepresentative (fun j => d (Sum.inr j)) := by
  unfold exponentRepresentative
  congr 1 <;> congr 1 <;> funext j <;> simp [Function.update, Finsupp.single_apply, eq_comm]
  by_cases h : i = j <;> simp [h, eq_comm]

theorem exponentRepresentative_sub_inr {r s : ℕ} (d : Variables r s →₀ ℕ) (i : Fin s) (m : ℕ) :
    exponentRepresentative (d - Finsupp.single (Sum.inr i) m) =
      jetWord xRepresentative (fun j => d (Sum.inl j)) *
        jetWord yRepresentative (Function.update (fun j => d (Sum.inr j)) i (d (Sum.inr i)-m)) := by
  unfold exponentRepresentative
  congr 1 <;> congr 1 <;> funext j <;> simp [Function.update, Finsupp.single_apply, eq_comm]
  by_cases h : i = j <;> simp [h, eq_comm]

/-- Each coefficient mode shift lowers one jet index, with multiplicities one and three. -/
theorem lowerB_exponentRepresentative {r s : ℕ} (m : ℕ) (d : Variables r s →₀ ℕ) :
    lowerB m (exponentRepresentative d) = ∑ i : Variables r s,
      (wordRootWeight i * ((d i).descFactorial m : ℂ)) •
        exponentRepresentative (d - Finsupp.single i m) := by
  rw [exponentRepresentative, lowerB_mul,
    lowerB_jetWord m xRepresentative 1 (by intro k; simpa using lowerB_xJet m k),
    lowerB_jetWord m yRepresentative 3 (lowerB_yJet m), Fintype.sum_sum_type,
    Finset.sum_mul, Finset.mul_sum]
  simp only [wordRootWeight, one_mul, smul_mul_assoc, mul_smul_comm,
    exponentRepresentative_sub_inl, exponentRepresentative_sub_inr]

end KhanSL2.Modules
