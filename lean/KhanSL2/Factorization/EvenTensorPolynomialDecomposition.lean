module

public import KhanSL2.Factorization.EvenTensorPolynomial

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-! Every positive-degree monic complex polynomial is realized by a distinct
support tensor word, with its actual root multiplicities. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace KhanSL2.Factorization.EvenTensorWord

/-- Realize a nonempty finite set of labelled local multiplicities without
introducing repeated support points or changing their product polynomial. -/
theorem exists_of_finset (s : Finset ℂ) (hs : s.Nonempty) (m : ℂ → ℕ) :
    ∃ t : EvenTensorWord, t.Distinct ∧ t.support = (s : Set ℂ) ∧
      t.polynomial = ∏ a ∈ s, (X-C a)^m a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    by_cases hne : s.Nonempty
    · obtain ⟨t,ht,hst,hpt⟩ := ih hne
      refine ⟨.tensor (.leaf a (m a)) t,⟨True.intro,ht,?_⟩,?_,?_⟩
      · apply Set.disjoint_left.mpr
        intro z hz hzt
        have hz' : z=a := hz
        subst z
        rw [hst] at hzt
        exact ha hzt
      · simp only [support,hst,Finset.coe_insert]
        rfl
      · simp only [polynomial,hpt,Finset.prod_insert ha]
    · have hs : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst s
      refine ⟨.leaf a (m a),True.intro,?_,?_⟩
      · simp [support]
      · simp [polynomial]

/-- A positive-degree monic polynomial is the exact polynomial of a distinct-support word. -/
theorem exists_of_monic (f : ℂ[X]) (hf : f.Monic) (hdeg : 0<f.natDegree) :
    ∃ t : EvenTensorWord, t.Distinct ∧ t.support = (f.roots.toFinset : Set ℂ) ∧
      t.polynomial = f ∧ t.weight=f.natDegree := by
  classical
  have hs : f.roots.toFinset.Nonempty := by
    by_contra h
    have he : f.roots = 0 := Multiset.toFinset_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    have hd := (IsAlgClosed.splits f).natDegree_eq_card_roots
    rw [he,Multiset.card_zero] at hd
    omega
  obtain ⟨t,ht,hst,hpt⟩ := exists_of_finset f.roots.toFinset hs (fun a => f.rootMultiplicity a)
  have hp : t.polynomial=f := by
    rw [hpt]
    exact (prod_multiset_root_eq_finset_root (p:=f)).symm.trans
      ((IsAlgClosed.splits f).eq_prod_roots_of_monic hf).symm
  refine ⟨t,ht,hst,hp,?_⟩
  rw [← polynomial_natDegree,hp]

/-- Coprime complex polynomials have disjoint sets of actual roots. -/
theorem root_support_disjoint {f g : ℂ[X]} (hf : f≠0) (hg : g≠0) (h : IsCoprime f g) :
    Disjoint (f.roots.toFinset : Set ℂ) (g.roots.toFinset : Set ℂ) := by
  classical
  apply Set.disjoint_left.mpr
  intro z hz hzg
  have hz' : f.eval z=0 := (mem_roots hf).mp (Multiset.mem_toFinset.mp hz)
  have hzg' : g.eval z=0 := (mem_roots hg).mp (Multiset.mem_toFinset.mp hzg)
  have hc := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ f g).mp h z
  simp only [aeval_def,Algebra.algebraMap_self,eval₂_id,hz',hzg',ne_eq,not_true_eq_false,or_self] at hc

/-- A coprime positive-degree pair is realized by distinct words with disjoint supports. -/
theorem exists_pair_of_coprime (f g : ℂ[X]) (hf : f.Monic) (hg : g.Monic)
    (hfd : 0<f.natDegree) (hgd : 0<g.natDegree) (hfg : IsCoprime f g) :
    ∃ u v : EvenTensorWord, u.Distinct ∧ v.Distinct ∧ Disjoint u.support v.support ∧
      u.polynomial=f ∧ v.polynomial=g ∧ u.weight=f.natDegree ∧ v.weight=g.natDegree := by
  obtain ⟨u,hu,hsu,hpu,hwu⟩ := exists_of_monic f hf hfd
  obtain ⟨v,hv,hsv,hpv,hwv⟩ := exists_of_monic g hg hgd
  refine ⟨u,v,hu,hv,?_,hpu,hpv,hwu,hwv⟩
  rw [hsu,hsv]
  exact root_support_disjoint hf.ne_zero hg.ne_zero hfg

end KhanSL2.Factorization.EvenTensorWord
