module

public import KhanSL2.Depth.SourceDescent

@[expose] public section

/-!
# Support and depth (paper §7, blueprint `sec:depth`)

All depths are mathlib's `Ext`-depth `Ideal.depth`. Everything here is commutative algebra;
none of it uses the rest of the project.

**Lemma 7.1, depth descent** (`kernel_eq_zero_of_depth`). Let `R` be Noetherian and
`I = (r₁, …, r_c)` with `r` an `R`-regular sequence. Let `C_c → ⋯ → C_0` be a complex of finite
projective modules (`C p = 0` for `p > c`) with homology `K_p`. Let `K_p → J_p` be maps,
surjective for `2 ≤ p ≤ c`, whose kernels are killed by a power of `I` (or are supported on `V(I)`,
`kernel_eq_zero_of_depth_of_support`). If `depth_I J_p ≥ p` for `2 ≤ p ≤ c`, the kernels vanish
for `p ≥ 2`.

**Lemma 7.2, depth of the source modules** (`depth_JB_ge`). For `0 < p < B`,
`depth_{P_B} J_{B,p} ≥ p`. Here:
* `R_B = ℂ[e₁, …, e_B]` (`RB`), and `P_B = (e_i - C(B,i)(e₁/B)^i : 2 ≤ i ≤ B)`
  (`collisionIdeal`). Its generators form a regular sequence of length `B - 1`
  (`collisionIdeal_isRegular`).
* `J_{r,s} = F_{r,s} · S_{r,s} ⊆ ℂ[z, w]` with `F_{r,s} = Δ(z)²Δ(w)³∏(zᵢ - w_a)²` and
  `S_{r,s}` the polynomials symmetric in `z` and in `w`. `R_B` acts through
  `ν*(e_k) = e_k(z, w, w, w)` (`J`, `nuStar`). `J_{B,p}` is `J_{p,s}` when `B = p + 3s`, and `0`
  otherwise (`JB`).
* The proof gives more: `depth_{P_B} J_{r,s} ≥ r + s - 1` for `s ≥ 1` (`depth_J_ge`).

**The two together** (`source_kernel_eq_zero`): for a complex of finite projective
`R_B`-modules in degrees `0 … B-1`, with maps `H_p → J_{B,p}` surjective for `2 ≤ p < B`
and with kernels killed by a power of `P_B`, these kernels vanish for `2 ≤ p < B`.
For `B ≥ 1`, the complex is the truncation after splitting off the top term. No surjection onto
the nonzero target `J_{B,B}` is required from its zero degree-`B` homology. The
top-degree isomorphism must be established separately, as in §8 of the paper.
For `B = 0` the stated middle-degree range is empty.

**Supporting results**
* toolkit (`lem:depthkit`):
  - (a) `length_le_depth_of_projective`;
  - (b) `eq_zero_of_one_le_depth_of_pow`;
  - (c) `depth_right_ge`, `depth_left_ge`, `depth_middle_ge`;
  - (e) `exists_pow_smul_eq_zero_of_support_subset`;
* depth along a ring map, in the direction used (`lem:depthfinite`): `le_depth_of_le_depth_map`;
* regular sequences of graph coordinates in polynomial rings: `graph_isRegular`;
* the two-block fundamental theorem of symmetric polynomials: `mem_symmBoth_iff`,
  `blockE_injective`;
* full collision in coefficients: `eq_X_add_C_pow_of_collision`;
* `J_{r,s}` is finite over `R_B` (`J_finite`, blueprint `lem:Jfinite`), and is isomorphic to the
  coordinate ring of pairs `(A, W)` of monic polynomials, an `R_B`-module through
  `(A, W) ↦ AW³` (`srcEquivJ`).

**Not covered here.** The identification of `J_{r,s}` with the graded dual of the `(r, s)`
sector of the source `A` is the paper's Lemma 3.1 (blueprint `lem:functional`, WP6). Applying
Lemma 7.1 to the BGG complex needs `BGGInput` in its `R_B`-linear form.
-/

noncomputable section

namespace KhanSL2.Depth

open RingTheory.Sequence

/-- **The commutative algebra of §7**, in one statement. -/
theorem milestoneDepth :
    (∀ B : ℕ, ∃ rs : List (RB B), Ideal.ofList rs = collisionIdeal B ∧ rs.length = B - 1 ∧
      IsRegular (RB B) rs) ∧
    (∀ B r s : ℕ, B = r + 3 * s → 1 ≤ s →
      ((r + s - 1 : ℕ) : ℕ∞) ≤ (collisionIdeal B).depth (ModuleCat.of (RB B) (J B r s))) ∧
    (∀ B p : ℕ, 0 < p → p < B →
      (p : ℕ∞) ≤ (collisionIdeal B).depth (ModuleCat.of (RB B) (JB B p))) :=
  ⟨collisionIdeal_isRegular, depth_J_ge, depth_JB_ge⟩

end KhanSL2.Depth



