module

public import KhanSL2.StrongMacdonald.SliceRing
public import KhanSL2.StrongMacdonald.Hodge

@[expose] public section

/-!
# FGT Theorem B for `𝔰𝔩₂` in the Macdonald model

`KhanSL2/StrongMacdonald/` formalizes Part I of Fishel–Grojnowski–Teleman for `𝔰𝔩₂`:

* `lap_eq_box_D_K` (FGT Lemma 3.13): `□̄ = □ + D + K` on the super-polynomial algebra `W`;
* `dbar_mul_dbar`: `∂̄² = 0`;
* `mem_harm_iff`: on invariants, harmonic = joint kernel of the `X_a(m)` and `d_a(-m)†`;
* `harmEquivCohom w s`: harmonic invariants of bidegree `(w,s)` ≅ cohomology of `C(w,s)`;
* `harm_free`: the harmonic invariants are the free super-commutative algebra on
  `S(n)` (`n ≥ 0`, even) and `E(n)` (`n ≥ 1`, odd).
-/
