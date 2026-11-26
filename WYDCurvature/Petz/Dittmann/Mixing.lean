/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.ForMathlib.Majorization
import WYDCurvature.Petz.KuboMori.ScalarCurvature

/-!
# The BKM scalar curvature under mixing

Dittmann's Theorem 3: the reduction of Petz's conjecture (the scalar curvature of
the Kubo–Mori metric increases under mixing) to Dittmann's four inequalities (62)–(65) on the
function `hs` of `KuboMori/ScalarCurvature.lean`.

Dittmann states Theorem 3 under his Assertion that `hs` is concave on `ℝ³₊`, which he confirmed
numerically but did not prove. His Lemma 4 derives (62)–(65) from the Assertion, and his proof of
Theorem 3 uses only (62)–(65). So Theorem 3 is stated here with (62)–(65) as its hypothesis
(`DittmannInequalities`), which is weaker than the Assertion. They are proved in
`Dittmann/Plane.lean` and `Dittmann/Inequalities.lean`, from concavity along the segments of
Lemma 4 alone.

`hs` is smooth on the positive octant and fully symmetric,
with the chain rule along a curve in terms of its first partial derivative `hs′`; the eigenvalue
sum `curvSum l = ∑_{[n]³} hs(lᵢ, lⱼ, lₖ) - ∑ᵢ hs(lᵢ, lᵢ, lᵢ)` of Dittmann's formula (58), its
gradient, and Dittmann's identity in the form of a sign: under (62)–(65), `lₐ < l_b` implies
`∂_b curvSum ≤ ∂ₐ curvSum`. With the Schur–Ostrowski criterion
(`ForMathlib/Majorization.lean`) this gives Theorem 3: under (62)–(65) the scalar curvature
increases under mixing. The route differs from Dittmann's (a chain of T-transforms, each changing
two eigenvalues, and the derivative at `t = 0`): the gradient is controlled at every point of the
segment between the sorted eigenvalue vectors.

The strict form follows the same way. The term of (62) in Dittmann's identity is present for every
pair `a, b`, so if (62) is strict, `lₐ < l_b` implies `∂_b curvSum < ∂ₐ curvSum`, and the strict
Schur–Ostrowski criterion gives `S(ϱ) < S(ρ)` when the spectra differ. Strict (62) is proved in
`Dittmann/Plane.lean`.

Mixing is majorization: `ρ` is more mixed than `ϱ` (Dittmann's `ρ ≻ ϱ`, his (60)) when the
eigenvalues of `ρ` are majorized by those of `ϱ`.

## Main definitions

* `PetzCurvature.bkmHsDeriv x y z`: `hs′(x, y, z) = ∂/∂x hs(x, y, z)`.
* `PetzCurvature.DittmannInequalities`: Dittmann's inequalities (62)–(65) (the conclusion of his
  Lemma 4), as hypotheses.
* `PetzCurvature.curvSum`, `PetzCurvature.curvGrad`: the eigenvalue sum of (58) and
  its partial derivatives.

## Main statements

* `PetzCurvature.contDiffAt_bkmIntegral₂`, `PetzCurvature.contDiffAt_bkmIntegral₃`,
  `PetzCurvature.contDiffAt_bkmHs`: `m(x, y)`, `m(x, y, z)` and `hs` are `Cⁿ` on the
  positive quadrant and octant.
* `PetzCurvature.bkmHs_comm₁₂`, `PetzCurvature.bkmHs_comm₂₃`: `hs` is symmetric.
* `PetzCurvature.hasDerivAt_bkmHs_comp`: `d/dt hs(u, v, w) = hs′(u, v, w) u′ +
  hs′(v, u, w) v′ + hs′(w, u, v) w′`.
* `PetzCurvature.hasDerivAt_curvSum`: the derivative of `curvSum` along a curve.
* `PetzCurvature.curvGrad_sub_curvGrad`: **Dittmann's identity**, the expansion of
  `∂ₐ curvSum - ∂_b curvSum`.
* `PetzCurvature.curvGrad_le`: **Dittmann's identity as a sign**, from (62)–(65).
* `PetzCurvature.curvGrad_lt`: the strict sign, from (62)–(65) with (62) strict.
* `PetzCurvature.curvSum_comp_equiv`: `curvSum` is invariant under relabeling.
* `PetzCurvature.curvSum_le_of_isMajorizedBy`: under (62)–(65), `curvSum` increases under
  majorization.
* `PetzCurvature.scalarCurvature_bkmChart_le_of_isMajorizedBy_of_dittmann`: **Dittmann's
  Theorem 3**, Petz's conjecture conditional on (62)–(65).
* `PetzCurvature.curvSum_lt_of_isMajorizedBy`,
  `PetzCurvature.scalarCurvature_bkmChart_lt_of_isMajorizedBy_of_dittmann`: the strict forms,
  for spectra that differ, conditional on (62)–(65) with (62) strict.

## References

* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]

-/

open Finset Filter Topology

namespace PetzCurvature

/-! ### Symmetry -/

/-- `K` is symmetric in its last two arguments. -/
theorem bkmSummand_comm₂₃ (x y z : ℝ) : bkmSummand x y z = bkmSummand x z y := by
  rw [bkmSummand, bkmSummand, bkmIntegral₃_comm₂₃ x z y, bkmIntegral₂_comm x z,
    bkmIntegral₂_comm z y, bkmIntegral₂_comm y x]
  ring

/-- `hs` is symmetric in its first two arguments. -/
theorem bkmHs_comm₁₂ (x y z : ℝ) : bkmHs x y z = bkmHs y x z := by
  rw [bkmHs, bkmHs, bkmSummand_comm₂₃ y x z, bkmSummand_comm₂₃ x y z, bkmSummand_comm₂₃ z x y]
  ring

/-- `hs` is symmetric in its last two arguments; with `bkmHs_comm₁₂`, `hs` is fully symmetric,
though it is only defined as a cyclic symmetrization. -/
theorem bkmHs_comm₂₃ (x y z : ℝ) : bkmHs x y z = bkmHs x z y := by
  rw [bkmHs, bkmHs, bkmSummand_comm₂₃ x y z, bkmSummand_comm₂₃ y z x, bkmSummand_comm₂₃ z x y]
  ring

/-- `hs` is invariant under cyclic permutation of its arguments. -/
theorem bkmHs_cyclic (x y z : ℝ) : bkmHs x y z = bkmHs y z x := by
  rw [bkmHs_comm₁₂, bkmHs_comm₂₃]

/-! ### Smoothness -/

theorem contDiffAt_bkmIntegral₂ {p : ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2) (n : ℕ) :
    ContDiffAt ℝ n (fun q : ℝ × ℝ ↦ bkmIntegral₂ q.1 q.2) p := by
  refine contDiffAt_intervalIntegral_of_contDiffAt n
    (f := fun z : (ℝ × ℝ) × ℝ ↦ ((1 - z.2) * z.1.1 + z.2)⁻¹ * ((1 - z.2) * z.1.2 + z.2)⁻¹)
    fun t ht ↦ ?_
  have h1' := (pathScalar_pos h1 ht).ne'
  have h2' := (pathScalar_pos h2 ht).ne'
  fun_prop (disch := assumption)

theorem contDiffAt_bkmIntegral₃ {p : ℝ × ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2.1)
    (h3 : 0 < p.2.2) (n : ℕ) :
    ContDiffAt ℝ n (fun q : ℝ × ℝ × ℝ ↦ bkmIntegral₃ q.1 q.2.1 q.2.2) p := by
  refine contDiffAt_intervalIntegral_of_contDiffAt n
    (f := fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (1 - z.2) * (((1 - z.2) * z.1.1 + z.2)⁻¹ *
      ((1 - z.2) * z.1.2.1 + z.2)⁻¹ * ((1 - z.2) * z.1.2.2 + z.2)⁻¹)) fun t ht ↦ ?_
  have h1' := (pathScalar_pos h1 ht).ne'
  have h2' := (pathScalar_pos h2 ht).ne'
  have h3' := (pathScalar_pos h3 ht).ne'
  fun_prop (disch := assumption)

section Comp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g h : E → ℝ} {x₀ : E} {n : ℕ}

theorem contDiffAt_bkmIntegral₂_comp (hf : ContDiffAt ℝ n f x₀) (hg : ContDiffAt ℝ n g x₀)
    (hf0 : 0 < f x₀) (hg0 : 0 < g x₀) :
    ContDiffAt ℝ n (fun x ↦ bkmIntegral₂ (f x) (g x)) x₀ :=
  ContDiffAt.comp (g := fun q : ℝ × ℝ ↦ bkmIntegral₂ q.1 q.2) (f := fun x ↦ (f x, g x)) x₀
    (contDiffAt_bkmIntegral₂ (p := (f x₀, g x₀)) hf0 hg0 n) (hf.prodMk hg)

theorem contDiffAt_bkmIntegral₃_comp (hf : ContDiffAt ℝ n f x₀) (hg : ContDiffAt ℝ n g x₀)
    (hh : ContDiffAt ℝ n h x₀) (hf0 : 0 < f x₀) (hg0 : 0 < g x₀) (hh0 : 0 < h x₀) :
    ContDiffAt ℝ n (fun x ↦ bkmIntegral₃ (f x) (g x) (h x)) x₀ :=
  ContDiffAt.comp (g := fun q : ℝ × ℝ × ℝ ↦ bkmIntegral₃ q.1 q.2.1 q.2.2)
    (f := fun x ↦ (f x, g x, h x)) x₀
    (contDiffAt_bkmIntegral₃ (p := (f x₀, g x₀, h x₀)) hf0 hg0 hh0 n) (hf.prodMk (hg.prodMk hh))

theorem contDiffAt_bkmSummand_comp (hf : ContDiffAt ℝ n f x₀) (hg : ContDiffAt ℝ n g x₀)
    (hh : ContDiffAt ℝ n h x₀) (hf0 : 0 < f x₀) (hg0 : 0 < g x₀) (hh0 : 0 < h x₀) :
    ContDiffAt ℝ n (fun x ↦ bkmSummand (f x) (g x) (h x)) x₀ := by
  have a₁ := contDiffAt_bkmIntegral₂_comp hf hg hf0 hg0
  have a₂ := contDiffAt_bkmIntegral₂_comp hg hh hg0 hh0
  have a₃ := contDiffAt_bkmIntegral₂_comp hh hf hh0 hf0
  have a₄ := contDiffAt_bkmIntegral₂_comp hf hh hf0 hh0
  have n₁ := (bkmIntegral₂_pos hf0 hg0).ne'
  have n₂ := (bkmIntegral₂_pos hg0 hh0).ne'
  have n₃ := (bkmIntegral₂_pos hh0 hf0).ne'
  have n₄ := (bkmIntegral₂_pos hf0 hh0).ne'
  exact ContDiffAt.sub (((contDiffAt_bkmIntegral₃_comp hf hg hh hf0 hg0 hh0).pow 2).div
    (contDiffAt_const.mul ((a₁.mul a₂).mul a₃))
      (mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero n₁ n₂) n₃)))
    (((hf.mul (contDiffAt_bkmIntegral₃_comp hf hf hg hf0 hf0 hg0)).mul
      (contDiffAt_bkmIntegral₃_comp hf hf hh hf0 hf0 hh0)).div (a₁.mul a₄) (mul_ne_zero n₁ n₄))

theorem contDiffAt_bkmHs_comp (hf : ContDiffAt ℝ n f x₀) (hg : ContDiffAt ℝ n g x₀)
    (hh : ContDiffAt ℝ n h x₀) (hf0 : 0 < f x₀) (hg0 : 0 < g x₀) (hh0 : 0 < h x₀) :
    ContDiffAt ℝ n (fun x ↦ bkmHs (f x) (g x) (h x)) x₀ :=
  (((contDiffAt_bkmSummand_comp hf hg hh hf0 hg0 hh0).add
    (contDiffAt_bkmSummand_comp hg hh hf hg0 hh0 hf0)).add
      (contDiffAt_bkmSummand_comp hh hf hg hh0 hf0 hg0)).div_const 3

end Comp

/-- `hs` is `Cⁿ` on the positive octant. -/
theorem contDiffAt_bkmHs {p : ℝ × ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2.1) (h3 : 0 < p.2.2)
    (n : ℕ) : ContDiffAt ℝ n (fun q : ℝ × ℝ × ℝ ↦ bkmHs q.1 q.2.1 q.2.2) p :=
  contDiffAt_bkmHs_comp contDiffAt_fst contDiffAt_snd.fst contDiffAt_snd.snd h1 h2 h3

/-! ### The first partial derivative and the chain rule -/

/-- `hs′(x, y, z)`: the partial derivative of `hs` in its first argument. -/
noncomputable def bkmHsDeriv (x y z : ℝ) : ℝ :=
  deriv (fun u ↦ bkmHs u y z) x

/-- The partial derivative of `hs` in the first argument, as a derivative. -/
theorem hasDerivAt_bkmHs_fst {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    HasDerivAt (fun u ↦ bkmHs u y z) (bkmHsDeriv x y z) x :=
  ((contDiffAt_bkmHs_comp (n := 1) contDiffAt_id contDiffAt_const contDiffAt_const hx hy
    hz).differentiableAt one_ne_zero).hasDerivAt

/-- The chain rule for `hs`: `d/dt hs(u, v, w) = hs′(u, v, w) u′ + hs′(v, u, w) v′ +
hs′(w, u, v) w′`. -/
theorem hasDerivAt_bkmHs_comp {u v w : ℝ → ℝ} {u' v' w' t : ℝ} (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) (hu0 : 0 < u t) (hv0 : 0 < v t)
    (hw0 : 0 < w t) :
    HasDerivAt (fun s ↦ bkmHs (u s) (v s) (w s))
      (bkmHsDeriv (u t) (v t) (w t) * u' + bkmHsDeriv (v t) (u t) (w t) * v' +
        bkmHsDeriv (w t) (u t) (v t) * w') t := by
  set F : ℝ × ℝ × ℝ → ℝ := fun q ↦ bkmHs q.1 q.2.1 q.2.2
  set p : ℝ × ℝ × ℝ := (u t, v t, w t)
  have hF : HasFDerivAt F (fderiv ℝ F p) p :=
    ((contDiffAt_bkmHs (p := p) hu0 hv0 hw0 1).differentiableAt one_ne_zero).hasFDerivAt
  have hc : HasDerivAt (fun s ↦ (u s, v s, w s)) (u', v', w') t := hu.prodMk (hv.prodMk hw)
  have line : ∀ (e : ℝ × ℝ × ℝ) (c' : ℝ),
      HasDerivAt (fun r : ℝ ↦ F (p + r • e)) c' 0 → fderiv ℝ F p e = c' := by
    intro e c' h
    have hl : HasDerivAt (fun r : ℝ ↦ p + r • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add p
    exact (hF.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hl (by simp)).unique h
  have e1 : fderiv ℝ F p (1, 0, 0) = bkmHsDeriv (u t) (v t) (w t) := by
    refine line _ _ ?_
    have h0 := HasDerivAt.comp_const_add (u t) 0 (by simpa using hasDerivAt_bkmHs_fst hu0 hv0 hw0)
    have hfun : (fun r : ℝ ↦ F (p + r • ((1, 0, 0) : ℝ × ℝ × ℝ))) =
        fun r ↦ bkmHs (u t + r) (v t) (w t) := by
      funext r
      simp [F, p]
    rw [hfun]
    exact h0
  have e2 : fderiv ℝ F p (0, 1, 0) = bkmHsDeriv (v t) (u t) (w t) := by
    refine line _ _ ?_
    have h0 := HasDerivAt.comp_const_add (v t) 0 (by simpa using hasDerivAt_bkmHs_fst hv0 hu0 hw0)
    have hfun : (fun r : ℝ ↦ F (p + r • ((0, 1, 0) : ℝ × ℝ × ℝ))) =
        fun r ↦ bkmHs (v t + r) (u t) (w t) := by
      funext r
      simp only [F, p, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, mul_zero, add_zero]
      exact bkmHs_comm₁₂ _ _ _
    rw [hfun]
    exact h0
  have e3 : fderiv ℝ F p (0, 0, 1) = bkmHsDeriv (w t) (u t) (v t) := by
    refine line _ _ ?_
    have h0 := HasDerivAt.comp_const_add (w t) 0 (by simpa using hasDerivAt_bkmHs_fst hw0 hu0 hv0)
    have hfun : (fun r : ℝ ↦ F (p + r • ((0, 0, 1) : ℝ × ℝ × ℝ))) =
        fun r ↦ bkmHs (w t + r) (u t) (v t) := by
      funext r
      simp only [F, p, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, mul_zero, add_zero]
      exact (bkmHs_cyclic _ _ _).trans (bkmHs_cyclic _ _ _)
    rw [hfun]
    exact h0
  have hsplit : ((u', v', w') : ℝ × ℝ × ℝ) =
      u' • ((1, 0, 0) : ℝ × ℝ × ℝ) + v' • ((0, 1, 0) : ℝ × ℝ × ℝ) +
        w' • ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    ext <;> simp
  have := hF.comp_hasDerivAt t hc
  rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul, e1, e2, e3] at this
  simp only [smul_eq_mul] at this
  rw [show bkmHsDeriv (u t) (v t) (w t) * u' + bkmHsDeriv (v t) (u t) (w t) * v' +
      bkmHsDeriv (w t) (u t) (v t) * w' = u' * bkmHsDeriv (u t) (v t) (w t) +
        v' * bkmHsDeriv (v t) (u t) (w t) + w' * bkmHsDeriv (w t) (u t) (v t) by ring]
  exact this

theorem bkmHsDeriv_comm₂₃ (x y z : ℝ) : bkmHsDeriv x y z = bkmHsDeriv x z y := by
  simp only [bkmHsDeriv, bkmHs_comm₂₃ _ y z]

/-! ### Dittmann's inequalities and the gradient of the curvature sum -/

/-- **Dittmann's inequalities (62)–(65)** (the conclusion of his Lemma 4), for all positive
`x < y`, `λ`, `µ`, with `hs′` the partial derivative in the first argument. Dittmann derives them
from the concavity of `hs` along the segments from `(x, x, y)`, `(x, x, λ)`, `(x, y, λ)`,
`(x, λ, µ)` to `(y, y, x)`, `(y, y, λ)`, `(y, x, λ)`, `(y, λ, µ)`. -/
structure DittmannInequalities : Prop where
  ineq62 : ∀ x y : ℝ, 0 < x → x < y → 0 ≤ 2 * bkmHsDeriv x x y - bkmHsDeriv y x x -
    2 * bkmHsDeriv y x y + bkmHsDeriv x y y
  ineq63 : ∀ x y l : ℝ, 0 < x → x < y → 0 < l → 0 ≤ bkmHsDeriv x x l - bkmHsDeriv y y l
  ineq64 : ∀ x y l : ℝ, 0 < x → x < y → 0 < l → 0 ≤ bkmHsDeriv x y l - bkmHsDeriv y x l
  ineq65 : ∀ x y l m : ℝ, 0 < x → x < y → 0 < l → 0 < m →
    0 ≤ bkmHsDeriv x l m - bkmHsDeriv y l m

variable {ι : Type*} [Fintype ι]

/-- The eigenvalue part of Dittmann's formula (58):
`∑_{(i, j, k)} hs(lᵢ, lⱼ, lₖ) - ∑ᵢ hs(lᵢ, lᵢ, lᵢ)`. -/
noncomputable def curvSum (l : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, bkmHs (l i) (l j) (l k) - ∑ i, bkmHs (l i) (l i) (l i)

/-- The partial derivative of `curvSum` in `lₐ`: `3 (∑ⱼₖ hs′(lₐ, lⱼ, lₖ) - hs′(lₐ, lₐ, lₐ))`. -/
noncomputable def curvGrad (l : ι → ℝ) (a : ι) : ℝ :=
  3 * (∑ j, ∑ k, bkmHsDeriv (l a) (l j) (l k) - bkmHsDeriv (l a) (l a) (l a))

/-- The derivative of `curvSum` along a curve of positive vectors. -/
theorem hasDerivAt_curvSum {L : ℝ → ι → ℝ} {L' : ι → ℝ} {t : ℝ}
    (hL : ∀ i, HasDerivAt (fun s ↦ L s i) (L' i) t) (hpos : ∀ i, 0 < L t i) :
    HasDerivAt (fun s ↦ curvSum (L s)) (∑ a, curvGrad (L t) a * L' a) t := by
  have h3 := fun i j k ↦ hasDerivAt_bkmHs_comp (hL i) (hL j) (hL k) (hpos i) (hpos j) (hpos k)
  have hd := fun i ↦ hasDerivAt_bkmHs_comp (hL i) (hL i) (hL i) (hpos i) (hpos i) (hpos i)
  have H := (HasDerivAt.fun_sum (u := univ) fun i _ ↦ HasDerivAt.fun_sum (u := univ) fun j _ ↦
    HasDerivAt.fun_sum (u := univ) fun k _ ↦ h3 i j k).sub
      (HasDerivAt.fun_sum (u := univ) fun i _ ↦ hd i)
  refine H.congr_deriv ?_
  have c2 : ∑ i, ∑ j, ∑ k, bkmHsDeriv (L t j) (L t i) (L t k) * L' j =
      ∑ i, ∑ j, ∑ k, bkmHsDeriv (L t i) (L t j) (L t k) * L' i := Finset.sum_comm
  have c3 : ∑ i, ∑ j, ∑ k, bkmHsDeriv (L t k) (L t i) (L t j) * L' k =
      ∑ i, ∑ j, ∑ k, bkmHsDeriv (L t i) (L t j) (L t k) * L' i :=
    (sum_cyclic fun a b c ↦ bkmHsDeriv (L t c) (L t a) (L t b) * L' c).symm
  have hg : ∑ a, curvGrad (L t) a * L' a =
      3 * ∑ i, ∑ j, ∑ k, bkmHsDeriv (L t i) (L t j) (L t k) * L' i -
        3 * ∑ i, bkmHsDeriv (L t i) (L t i) (L t i) * L' i := by
    simp only [curvGrad, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simp only [Finset.sum_add_distrib]
  rw [c2, c3, hg]
  ring

section Split

variable [DecidableEq ι] {a b : ι}

omit [Fintype ι] in
theorem sum_split_two {M : Type*} [AddCommMonoid M] [Fintype ι] (hab : a ≠ b) (f : ι → M) :
    ∑ j, f j = f a + f b + ∑ j ∈ (univ.erase a).erase b, f j := by
  rw [← Finset.add_sum_erase univ f (mem_univ a),
    ← Finset.add_sum_erase (univ.erase a) f (mem_erase.mpr ⟨hab.symm, mem_univ b⟩), add_assoc]

omit [Fintype ι] in
theorem sum_sum_split_two [Fintype ι] (hab : a ≠ b) (f : ι → ι → ℝ) :
    ∑ j, ∑ k, f j k = f a a + f a b + f b a + f b b +
      ∑ r ∈ (univ.erase a).erase b, (f a r + f r a + f b r + f r b) +
        ∑ j ∈ (univ.erase a).erase b, ∑ k ∈ (univ.erase a).erase b, f j k := by
  rw [sum_split_two hab]
  simp only [sum_split_two hab (f _), Finset.sum_add_distrib]
  ring

end Split

/-- **Dittmann's identity**: the expansion of `⅓ (∂ₐ - ∂_b) curvSum` in Dittmann's proof of
Theorem 3, in four groups of terms: the pair `a, b` alone (the expression of (62)), one other
index (those of (63) and (64)), and two other indices (that of (65)). -/
theorem curvGrad_sub_curvGrad [DecidableEq ι] (l : ι → ℝ) {a b : ι} (hne : a ≠ b) :
    curvGrad l a - curvGrad l b = 3 *
      ((2 * bkmHsDeriv (l a) (l a) (l b) - bkmHsDeriv (l b) (l a) (l a) -
        2 * bkmHsDeriv (l b) (l a) (l b) + bkmHsDeriv (l a) (l b) (l b)) +
      2 * ∑ r ∈ (univ.erase a).erase b,
        ((bkmHsDeriv (l a) (l a) (l r) - bkmHsDeriv (l b) (l b) (l r)) +
          (bkmHsDeriv (l a) (l b) (l r) - bkmHsDeriv (l b) (l a) (l r))) +
      ∑ j ∈ (univ.erase a).erase b, ∑ k ∈ (univ.erase a).erase b,
        (bkmHsDeriv (l a) (l j) (l k) - bkmHsDeriv (l b) (l j) (l k))) := by
  have s₁ : ∀ u v, ∑ r ∈ (univ.erase a).erase b, bkmHsDeriv (l u) (l r) (l v) =
      ∑ r ∈ (univ.erase a).erase b, bkmHsDeriv (l u) (l v) (l r) :=
    fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ bkmHsDeriv_comm₂₃ _ _ _
  simp only [curvGrad]
  rw [sum_sum_split_two hne (fun j k ↦ bkmHsDeriv (l a) (l j) (l k)),
    sum_sum_split_two hne (fun j k ↦ bkmHsDeriv (l b) (l j) (l k))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [s₁ a a, s₁ a b, s₁ b a, s₁ b b, bkmHsDeriv_comm₂₃ (l a) (l b) (l a),
    bkmHsDeriv_comm₂₃ (l b) (l b) (l a)]
  ring

/-- Under (63)–(65), the terms of Dittmann's identity other than that of (62) are nonnegative:
`3 E₆₂ ≤ ∂ₐ curvSum - ∂_b curvSum` for `lₐ < l_b`, with `E₆₂` the expression of (62). -/
theorem le_curvGrad_sub_curvGrad (H : DittmannInequalities) {l : ι → ℝ} (hl : ∀ i, 0 < l i)
    {a b : ι} (hab : l a < l b) :
    3 * (2 * bkmHsDeriv (l a) (l a) (l b) - bkmHsDeriv (l b) (l a) (l a) -
      2 * bkmHsDeriv (l b) (l a) (l b) + bkmHsDeriv (l a) (l b) (l b)) ≤
        curvGrad l a - curvGrad l b := by
  classical
  rw [curvGrad_sub_curvGrad l fun h ↦ hab.ne (congrArg l h)]
  have hR : 0 ≤ ∑ r ∈ (univ.erase a).erase b,
      ((bkmHsDeriv (l a) (l a) (l r) - bkmHsDeriv (l b) (l b) (l r)) +
        (bkmHsDeriv (l a) (l b) (l r) - bkmHsDeriv (l b) (l a) (l r))) :=
    Finset.sum_nonneg fun r _ ↦ add_nonneg (H.ineq63 _ _ _ (hl a) hab (hl r))
      (H.ineq64 _ _ _ (hl a) hab (hl r))
  have hRR : 0 ≤ ∑ j ∈ (univ.erase a).erase b, ∑ k ∈ (univ.erase a).erase b,
      (bkmHsDeriv (l a) (l j) (l k) - bkmHsDeriv (l b) (l j) (l k)) :=
    Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun k _ ↦
      H.ineq65 _ _ _ _ (hl a) hab (hl j) (hl k)
  linarith

/-- **Dittmann's identity, as a sign**: under (62)–(65), if `lₐ < l_b` then
`∂_b curvSum ≤ ∂ₐ curvSum`, i.e. moving weight from `l_b` to `lₐ` (mixing) does not decrease
the curvature. The identity is the expansion of `⅓ (∂ₐ - ∂_b) curvSum` in Dittmann's proof of
Theorem 3 (`curvGrad_sub_curvGrad`). Its four groups of terms (the pair `a, b` alone, one other
index, two other indices) are signed by (62), by (63) and (64), and by (65). -/
theorem curvGrad_le (H : DittmannInequalities) {l : ι → ℝ}
    (hl : ∀ i, 0 < l i) {a b : ι} (hab : l a < l b) : curvGrad l b ≤ curvGrad l a := by
  have h := le_curvGrad_sub_curvGrad H hl hab
  have e62 := H.ineq62 _ _ (hl a) hab
  linarith

/-- **Dittmann's identity, as a strict sign**: under (62)–(65), with (62) strict, if `lₐ < l_b`
then `∂_b curvSum < ∂ₐ curvSum`. Only (62) needs to be strict: its term is present for every pair
`a, b`, while the others need further indices. -/
theorem curvGrad_lt (H : DittmannInequalities)
    (H62 : ∀ x y : ℝ, 0 < x → x < y → 0 < 2 * bkmHsDeriv x x y - bkmHsDeriv y x x -
      2 * bkmHsDeriv y x y + bkmHsDeriv x y y)
    {l : ι → ℝ} (hl : ∀ i, 0 < l i) {a b : ι} (hab : l a < l b) :
    curvGrad l b < curvGrad l a := by
  have h := le_curvGrad_sub_curvGrad H hl hab
  have e62 := H62 _ _ (hl a) hab
  linarith

/-- `∂ₐ curvSum` depends on `a` only through `lₐ`. -/
theorem curvGrad_congr {l : ι → ℝ} {a b : ι} (h : l a = l b) : curvGrad l a = curvGrad l b := by
  simp only [curvGrad, h]

/-- `curvSum` is invariant under relabeling. -/
theorem curvSum_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (l : ι → ℝ) :
    curvSum (l ∘ e) = curvSum l := by
  simp only [curvSum, Function.comp_apply]
  congr 1
  · rw [← e.sum_comp (fun i ↦ ∑ j, ∑ k, bkmHs (l i) (l j) (l k))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← e.sum_comp (fun j ↦ ∑ k, bkmHs (l (e i)) (l j) (l k))]
    exact Finset.sum_congr rfl fun j _ ↦ e.sum_comp (fun k ↦ bkmHs (l (e i)) (l (e j)) (l k))
  · exact e.sum_comp (fun i ↦ bkmHs (l i) (l i) (l i))

/-! ### Theorem 3 -/

/-- **Under (62)–(65), `curvSum` increases under mixing**: if `x` is majorized by `y` (both
positive), then `curvSum y ≤ curvSum x`. -/
theorem curvSum_le_of_isMajorizedBy (H : DittmannInequalities) {n : ℕ} {x y : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y) :
    curvSum y ≤ curvSum x := by
  refine le_of_isMajorizedBy (U := {z | ∀ i, 0 < z i}) (grad := curvGrad) ?_ ?_ ?_ ?_ hx hy hxy
  · intro z hz w hw a b ha hb hab i
    have := hz i
    have := hw i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | rfl
    · positivity
    · simp only [zero_mul, zero_add] at hab ⊢
      rw [hab, one_mul]
      exact hw i
  · intro z hz σ
    exact ⟨fun i ↦ hz (σ i), curvSum_comp_equiv σ z⟩
  · intro z hz v
    have h := hasDerivAt_curvSum (L := fun s ↦ z + s • v) (L' := v) (t := 0)
      (fun i ↦ by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (z i))
      (fun i ↦ by simpa using hz i)
    simpa using h
  · intro z hz hmono a b hab
    rcases (hmono hab).lt_or_eq with h | h
    · exact curvGrad_le H hz h
    · exact (curvGrad_congr h).ge

open PetzCurvature.Curvature in
open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **Dittmann's Theorem 3**: if `hs` satisfies (62)–(65), then **the scalar curvature of the
Kubo–Mori metric increases under mixing**: for faithful density matrices `ρ`, `ϱ` of the same size
with the eigenvalues of `ρ` majorized by those of `ϱ` (`ρ` more mixed than `ϱ`), `S(ϱ) ≤ S(ρ)`.
That is Petz's conjecture, conditional on (62)–(65). Dittmann's hypothesis is the stronger
concavity of `hs`. -/
theorem scalarCurvature_bkmChart_le_of_isMajorizedBy_of_dittmann (H : DittmannInequalities)
    {d : Type*} [Fintype d] [DecidableEq d] {ρ ϱ : Matrix d d ℂ} (hρ : ρ.PosDef)
    (hϱ : ϱ.PosDef) (hρtr : ρ.trace = 1) (hϱtr : ϱ.trace = 1)
    (hmix : IsMajorizedBy (hρ.1.eigenvalues ∘ (Fintype.equivFin d).symm)
      (hϱ.1.eigenvalues ∘ (Fintype.equivFin d).symm)) :
    scalarCurvature (bkmChart (tracelessHermitian d) ϱ) 0 ≤
      scalarCurvature (bkmChart (tracelessHermitian d) ρ) 0 := by
  rw [scalarCurvature_bkmChart_eq_hs hρ hρtr, scalarCurvature_bkmChart_eq_hs hϱ hϱtr]
  have h : curvSum (hϱ.1.eigenvalues ∘ (Fintype.equivFin d).symm) ≤
      curvSum (hρ.1.eigenvalues ∘ (Fintype.equivFin d).symm) :=
    curvSum_le_of_isMajorizedBy H (fun _ ↦ hρ.eigenvalues_pos _)
      (fun _ ↦ hϱ.eigenvalues_pos _) hmix
  rw [curvSum_comp_equiv, curvSum_comp_equiv] at h
  simp only [curvSum] at h
  linarith

/-- **Under (62)–(65), with (62) strict, `curvSum` increases strictly under mixing**: if `x` is
majorized by `y` (both positive) and their increasing rearrangements differ, then
`curvSum y < curvSum x`. -/
theorem curvSum_lt_of_isMajorizedBy (H : DittmannInequalities)
    (H62 : ∀ x y : ℝ, 0 < x → x < y → 0 < 2 * bkmHsDeriv x x y - bkmHsDeriv y x x -
      2 * bkmHsDeriv y x y + bkmHsDeriv x y y)
    {n : ℕ} {x y : Fin n → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y)
    (hne : Majorization.sortInc x ≠ Majorization.sortInc y) : curvSum y < curvSum x := by
  refine lt_of_isMajorizedBy (U := {z | ∀ i, 0 < z i}) (grad := curvGrad) ?_ ?_ ?_ ?_
    (fun z hz _ a b hab ↦ curvGrad_lt H H62 hz hab) hx hy hxy hne
  · intro z hz w hw a b ha hb hab i
    have := hz i
    have := hw i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | rfl
    · positivity
    · simp only [zero_mul, zero_add] at hab ⊢
      rw [hab, one_mul]
      exact hw i
  · intro z hz σ
    exact ⟨fun i ↦ hz (σ i), curvSum_comp_equiv σ z⟩
  · intro z hz v
    have h := hasDerivAt_curvSum (L := fun s ↦ z + s • v) (L' := v) (t := 0)
      (fun i ↦ by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (z i))
      (fun i ↦ by simpa using hz i)
    simpa using h
  · intro z hz hmono a b hab
    rcases (hmono hab).lt_or_eq with h | h
    · exact curvGrad_le H hz h
    · exact (curvGrad_congr h).ge

open PetzCurvature.Curvature in
open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **Dittmann's Theorem 3, strict**: if `hs` satisfies (62)–(65), with (62) strict, then for
faithful density matrices `ρ`, `ϱ` of the same size with the eigenvalues of `ρ` majorized by those
of `ϱ`, and spectra that differ (no relabeling of the eigenvalues of `ρ` gives those of `ϱ`),
`S(ϱ) < S(ρ)`. -/
theorem scalarCurvature_bkmChart_lt_of_isMajorizedBy_of_dittmann (H : DittmannInequalities)
    (H62 : ∀ x y : ℝ, 0 < x → x < y → 0 < 2 * bkmHsDeriv x x y - bkmHsDeriv y x x -
      2 * bkmHsDeriv y x y + bkmHsDeriv x y y)
    {d : Type*} [Fintype d] [DecidableEq d] {ρ ϱ : Matrix d d ℂ} (hρ : ρ.PosDef)
    (hϱ : ϱ.PosDef) (hρtr : ρ.trace = 1) (hϱtr : ϱ.trace = 1)
    (hmix : IsMajorizedBy (hρ.1.eigenvalues ∘ (Fintype.equivFin d).symm)
      (hϱ.1.eigenvalues ∘ (Fintype.equivFin d).symm))
    (hne : ∀ σ : Equiv.Perm d, hρ.1.eigenvalues ∘ σ ≠ hϱ.1.eigenvalues) :
    scalarCurvature (bkmChart (tracelessHermitian d) ϱ) 0 <
      scalarCurvature (bkmChart (tracelessHermitian d) ρ) 0 := by
  rw [scalarCurvature_bkmChart_eq_hs hρ hρtr, scalarCurvature_bkmChart_eq_hs hϱ hϱtr]
  set e := Fintype.equivFin d
  have hne' : Majorization.sortInc (hρ.1.eigenvalues ∘ e.symm) ≠
      Majorization.sortInc (hϱ.1.eigenvalues ∘ e.symm) := fun h ↦ by
    obtain ⟨σ, hσ⟩ := Majorization.exists_comp_eq_of_sortInc_eq h
    refine hne ((e.trans σ).trans e.symm) (funext fun i ↦ ?_)
    simpa using congrFun hσ (e i)
  have h : curvSum (hϱ.1.eigenvalues ∘ e.symm) < curvSum (hρ.1.eigenvalues ∘ e.symm) :=
    curvSum_lt_of_isMajorizedBy H H62 (fun _ ↦ hρ.eigenvalues_pos _)
      (fun _ ↦ hϱ.eigenvalues_pos _) hmix hne'
  rw [curvSum_comp_equiv, curvSum_comp_equiv] at h
  simp only [curvSum] at h
  linarith

end PetzCurvature
