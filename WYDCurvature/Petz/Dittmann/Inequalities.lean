/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.Deriv.Prod
import WYDCurvature.Petz.Dittmann.Certificates

/-!
# Dittmann's inequalities (64) and (65)

At pairwise distinct positive arguments, `∂₁₁hs = P₁ / Q₁` and `(∂₁ - ∂₂)²hs = P₃ / Q₃`
(`spaceD₁₁`, `spaceD₁₁_sub_spaceD₁₂_add`), with `Q₁, Q₃ > 0` there: `a = log x - log z` has the
sign of `x - z`, and likewise for `b` and `y - z`, `a - b` and `x - y`. The numerators are
homogeneous in `x`, `y`, `z` (of degrees `9` and `13`), so `z = 1` suffices, and with `x = e^A`,
`y = e^B` the six sectors of the orderings of `A`, `B`, `0` cover the plane; on each, both
numerators are `≤ 0` by a Taylor certificate (`Certificates.lean`). Hence `hs` is concave in its
first argument and along the directions `(1, -1, 0)` off the diagonals: the second-derivative forms
of Dittmann's (65) and (64).

From the signs to the inequalities, as in Dittmann's Lemma 4: `τ ↦ hs′(τ, λ, µ)` does not
increase (`∂₁₁hs ≤ 0`), which is (65) for `λ ≠ µ`, and (65) at `λ = µ` follows by continuity of
`hs′`; `g(τ) = hs(x + τ, y - τ, λ)` is concave on `[0, y - x]`, and `g′(0) = -g′(y - x) =
hs′(x, y, λ) - hs′(y, x, λ)`, which is (64). The segments cross the diagonals at finitely many
points, where `hs′` is continuous (`le_of_hasDerivAt_nonpos_off_finset`). Dittmann derives (64)
and (65) from his Assertion that `hs` is concave on all of `ℝ³₊`. Only the concavity along these
two families of segments is proved here, and only it is needed. With (62) and (63)
(`Dittmann/Plane.lean`) all four of Dittmann's inequalities hold, and his Theorem 3
(`Dittmann/Mixing.lean`) gives Petz's conjecture (`Main.lean`).

## Main statements

* `PetzCurvature.spaceNum₁₁_nonpos`, `PetzCurvature.spaceNum₃_nonpos`: the numerators
  are `≤ 0` at all positive arguments.
* `PetzCurvature.spaceD₁₁_nonpos`: `∂₁₁hs ≤ 0` off the diagonals.
* `PetzCurvature.spaceD₁₁_sub_spaceD₁₂_add_nonpos`: `(∂₁ - ∂₂)²hs ≤ 0` off the diagonals.
* `PetzCurvature.continuousAt_bkmHsDeriv`, `PetzCurvature.bkmHsDeriv_eq_spaceD₁`:
  `hs′` is continuous, and equals the closed form `spaceD₁` off the diagonals.
* `PetzCurvature.bkmHsDeriv_ineq65`, `PetzCurvature.bkmHsDeriv_ineq64`: **Dittmann's
  inequalities (65) and (64)**.
* `PetzCurvature.dittmannInequalities`: all four of Dittmann's inequalities hold.

## References

* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]

-/

namespace PetzCurvature

/-- **The numerator of `∂₁₁hs` is `≤ 0`** at all positive arguments. -/
theorem spaceNum₁₁_nonpos {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    spaceEval spaceNum₁₁ x y z (Real.log x - Real.log z) (Real.log y - Real.log z) ≤ 0 := by
  rw [spaceEval_homogeneous (D := 9) (by decide +kernel) _ _ _ _ hz.ne']
  have h := spaceNum₁₁_nonpos_exp (Real.log (x / z)) (Real.log (y / z))
  rw [Real.exp_log (div_pos hx hz), Real.exp_log (div_pos hy hz), Real.log_div hx.ne' hz.ne',
    Real.log_div hy.ne' hz.ne'] at h
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h

/-- **The numerator of `(∂₁ - ∂₂)²hs` is `≤ 0`** at all positive arguments. -/
theorem spaceNum₃_nonpos {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    spaceEval spaceNum₃ x y z (Real.log x - Real.log z) (Real.log y - Real.log z) ≤ 0 := by
  rw [spaceEval_homogeneous (D := 13) (by decide +kernel) _ _ _ _ hz.ne']
  have h := spaceNum₃_nonpos_exp (Real.log (x / z)) (Real.log (y / z))
  rw [Real.exp_log (div_pos hx hz), Real.exp_log (div_pos hy hz), Real.log_div hx.ne' hz.ne',
    Real.log_div hy.ne' hz.ne'] at h
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h

/-- `log x - log z` has the sign of `x - z`. -/
theorem log_sub_log_mul_sub_pos {x z : ℝ} (hx : 0 < x) (hz : 0 < z) (h : x ≠ z) :
    0 < (Real.log x - Real.log z) * (x - z) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr (Real.log_lt_log hx h)) (sub_neg.mpr h)
  · exact mul_pos (sub_pos.mpr (Real.log_lt_log hz h)) (sub_pos.mpr h)

/-- **`∂₁₁hs ≤ 0` off the diagonals**: `hs` is concave in its first argument there. -/
theorem spaceD₁₁_nonpos {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) :
    spaceD₁₁ x y z (Real.log x - Real.log z) (Real.log y - Real.log z) ≤ 0 := by
  have h1 := log_sub_log_mul_sub_pos hx hz hxz
  have h2 := log_sub_log_mul_sub_pos hy hz hyz
  have h3 := log_sub_log_mul_sub_pos hx hy hxy
  rw [← sub_sub_sub_cancel_right (Real.log x) (Real.log y) (Real.log z)] at h3
  rw [spaceD₁₁]
  refine div_nonpos_iff.mpr (Or.inr ⟨spaceNum₁₁_nonpos hx hy hz, ?_⟩)
  set a := Real.log x - Real.log z
  set b := Real.log y - Real.log z
  have e : 6 * a ^ 3 * b * x ^ 3 * y * z * (a - b) ^ 3 * (x - y) ^ 3 * (x - z) ^ 3 * (y - z) =
      6 * x ^ 3 * y * z * (a * (x - z)) ^ 3 * (b * (y - z)) * ((a - b) * (x - y)) ^ 3 := by ring
  rw [e]
  positivity

/-- **`(∂₁ - ∂₂)²hs ≤ 0` off the diagonals**: `∂₁₁hs - 2 ∂₁₂hs + ∂₂₂hs ≤ 0`, with
`∂₂₂hs(x, y, z) = ∂₁₁hs(y, x, z)`. -/
theorem spaceD₁₁_sub_spaceD₁₂_add_nonpos {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    spaceD₁₁ x y z (Real.log x - Real.log z) (Real.log y - Real.log z) -
        2 * spaceD₁₂ x y z (Real.log x - Real.log z) (Real.log y - Real.log z) +
        spaceD₁₁ y x z (Real.log y - Real.log z) (Real.log x - Real.log z) ≤ 0 := by
  have h1 := log_sub_log_mul_sub_pos hx hz hxz
  have h2 := log_sub_log_mul_sub_pos hy hz hyz
  have h3 := log_sub_log_mul_sub_pos hx hy hxy
  rw [← sub_sub_sub_cancel_right (Real.log x) (Real.log y) (Real.log z)] at h3
  obtain ⟨ha, hb, hab⟩ := space_ne_zero hx hy hz hxy hxz hyz
  rw [spaceD₁₁_sub_spaceD₁₂_add hx.ne' hy.ne' hz.ne' ha hb hab (sub_ne_zero.mpr hxy)
    (sub_ne_zero.mpr hxz) (sub_ne_zero.mpr hyz)]
  refine div_nonpos_iff.mpr (Or.inr ⟨spaceNum₃_nonpos hx hy hz, ?_⟩)
  set a := Real.log x - Real.log z
  set b := Real.log y - Real.log z
  have e : 6 * a ^ 3 * b ^ 3 * x ^ 3 * y ^ 3 * z * (a - b) ^ 3 * (x - y) ^ 3 * (x - z) ^ 3 *
      (y - z) ^ 3 =
      6 * x ^ 3 * y ^ 3 * z * (a * (x - z)) ^ 3 * (b * (y - z)) ^ 3 * ((a - b) * (x - y)) ^ 3 := by
    ring
  rw [e]
  positivity

/-! ### Monotonicity off a finite set -/

section Concavity

open Set Filter Topology

/-- A function continuous on `[a, c]` whose derivative is `≤ 0` on `(a, c)` off a finite set does
not increase from `a` to `c`. -/
theorem le_of_hasDerivAt_nonpos_off_finset {f f' : ℝ → ℝ} (S : Finset ℝ) {a c : ℝ} (hac : a ≤ c)
    (hf : ContinuousOn f (Icc a c))
    (hd : ∀ τ ∈ Ioo a c, τ ∉ S → HasDerivAt f (f' τ) τ ∧ f' τ ≤ 0) : f c ≤ f a := by
  induction S using Finset.induction_on generalizing a c with
  | empty =>
    have hd' := fun x hx ↦ hd x hx (Finset.notMem_empty x)
    refine antitoneOn_of_deriv_nonpos (convex_Icc a c) hf ?_ ?_ (left_mem_Icc.2 hac)
      (right_mem_Icc.2 hac) hac
    · rw [interior_Icc]
      exact fun x hx ↦ (hd' x hx).1.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      exact fun x hx ↦ (hd' x hx).1.deriv ▸ (hd' x hx).2
  | insert p S _ ih =>
    by_cases hp : p ∈ Ioo a c
    · refine (ih hp.2.le (hf.mono (Icc_subset_Icc hp.1.le le_rfl)) fun τ hτ hS ↦
        hd τ ⟨hp.1.trans hτ.1, hτ.2⟩ ?_).trans
        (ih hp.1.le (hf.mono (Icc_subset_Icc le_rfl hp.2.le)) fun τ hτ hS ↦
          hd τ ⟨hτ.1, hτ.2.trans hp.2⟩ ?_)
      · rw [Finset.mem_insert, not_or]
        exact ⟨hτ.1.ne', hS⟩
      · rw [Finset.mem_insert, not_or]
        exact ⟨hτ.2.ne, hS⟩
    · exact ih hac hf fun τ hτ hS ↦ hd τ hτ (by
        rw [Finset.mem_insert, not_or]
        exact ⟨fun h ↦ hp (h ▸ hτ), hS⟩)

/-! ### `hs′` off the diagonals -/

/-- `hs′` is continuous on the positive octant. -/
theorem continuousAt_bkmHsDeriv {p : ℝ × ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2.1)
    (h3 : 0 < p.2.2) : ContinuousAt (fun q : ℝ × ℝ × ℝ ↦ bkmHsDeriv q.1 q.2.1 q.2.2) p := by
  set F : ℝ × ℝ × ℝ → ℝ := fun q ↦ bkmHs q.1 q.2.1 q.2.2
  have hpos : ∀ᶠ q in 𝓝 p, 0 < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2 :=
    (continuousAt_fst.tendsto.eventually (lt_mem_nhds h1)).and
      ((continuous_snd.fst.continuousAt.tendsto.eventually (lt_mem_nhds h2)).and
        (continuous_snd.snd.continuousAt.tendsto.eventually (lt_mem_nhds h3)))
  have heq : (fun q ↦ fderiv ℝ F q (1, 0, 0)) =ᶠ[𝓝 p]
      fun q ↦ bkmHsDeriv q.1 q.2.1 q.2.2 := by
    filter_upwards [hpos] with q hq
    have hF : HasFDerivAt F (fderiv ℝ F q) q :=
      ((contDiffAt_bkmHs hq.1 hq.2.1 hq.2.2 1).differentiableAt one_ne_zero).hasFDerivAt
    have hl : HasDerivAt (fun u : ℝ ↦ (u, q.2.1, q.2.2)) (1, 0, 0) q.1 :=
      (hasDerivAt_id _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
    exact (hF.comp_hasDerivAt_of_eq q.1 hl rfl).unique (hasDerivAt_bkmHs_fst hq.1 hq.2.1 hq.2.2)
  have hc : ContinuousAt (fderiv ℝ F) p :=
    ((contDiffAt_bkmHs h1 h2 h3 2).fderiv_right (m := 0) (by norm_num)).continuousAt
  exact (hc.clm_apply continuousAt_const).congr heq

/-- `hs′` along a curve of positive points is continuous. -/
theorem ContinuousAt.bkmHsDeriv {u v w : ℝ → ℝ} {t : ℝ} (hu : ContinuousAt u t)
    (hv : ContinuousAt v t) (hw : ContinuousAt w t) (hu0 : 0 < u t) (hv0 : 0 < v t)
    (hw0 : 0 < w t) : ContinuousAt (fun s ↦ bkmHsDeriv (u s) (v s) (w s)) t :=
  (continuousAt_bkmHsDeriv (p := (u t, v t, w t)) hu0 hv0 hw0).comp (f := fun s ↦ (u s, v s, w s))
    (hu.prodMk (hv.prodMk hw))

/-- **`hs′` in closed form off the diagonals**: `hs′ = spaceD₁`. -/
theorem bkmHsDeriv_eq_spaceD₁ {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) :
    bkmHsDeriv x y z = spaceD₁ x y z (Real.log x - Real.log z) (Real.log y - Real.log z) := by
  have h := hasDerivAt_spaceHs (X := id) (Y := fun _ ↦ y) (z := z) (hasDerivAt_id x)
    (hasDerivAt_const x y) hx hy hz hxy hxz hyz
  have hev : (fun u ↦ bkmHs u y z) =ᶠ[𝓝 x] fun u ↦
      spaceHs (id u) y z (Real.log (id u) - Real.log z) (Real.log y - Real.log z) := by
    filter_upwards [lt_mem_nhds hx, eventually_ne_nhds hxy, eventually_ne_nhds hxz] with u h1 h2 h3
    exact bkmHs_space h1 hy hz h2 h3 hyz
  have := (hasDerivAt_bkmHs_fst hx hy hz).unique (h.congr_of_eventuallyEq hev)
  simpa using this

/-- **The derivative of `hs′` along a line**, off the diagonals:
`d/dt hs′(X, Y, z) = dx ∂₁₁hs(X, Y, z) + dy ∂₁₂hs(X, Y, z)`. -/
theorem hasDerivAt_bkmHsDeriv {X Y : ℝ → ℝ} {dx dy t z : ℝ} (hX : HasDerivAt X dx t)
    (hY : HasDerivAt Y dy t) (hX0 : 0 < X t) (hY0 : 0 < Y t) (hz : 0 < z) (hXY : X t ≠ Y t)
    (hXz : X t ≠ z) (hYz : Y t ≠ z) :
    HasDerivAt (fun t ↦ bkmHsDeriv (X t) (Y t) z)
      (dx * spaceD₁₁ (X t) (Y t) z (Real.log (X t) - Real.log z) (Real.log (Y t) - Real.log z) +
        dy * spaceD₁₂ (X t) (Y t) z (Real.log (X t) - Real.log z)
          (Real.log (Y t) - Real.log z)) t := by
  refine (hasDerivAt_spaceD₁ hX hY hX0 hY0 hz hXY hXz hYz).congr_of_eventuallyEq ?_
  have hXc := hX.continuousAt
  have hYc := hY.continuousAt
  filter_upwards [continuousAt_const.eventually_lt hXc hX0,
    continuousAt_const.eventually_lt hYc hY0, (hXc.sub hYc).eventually_ne (sub_ne_zero.mpr hXY),
    hXc.eventually_ne hXz, hYc.eventually_ne hYz] with s h1 h2 h3 h4 h5
  exact bkmHsDeriv_eq_spaceD₁ h1 h2 hz (sub_ne_zero.mp h3) h4 h5

/-! ### Dittmann's (65) and (64) -/

/-- (65) for `λ ≠ µ`: the segment `τ ↦ (τ, λ, µ)` crosses the diagonals only at `τ = λ, µ`. -/
theorem bkmHsDeriv_ineq65_of_ne {x y l m : ℝ} (hx : 0 < x) (hxy : x < y) (hl : 0 < l)
    (hm : 0 < m) (hlm : l ≠ m) : 0 ≤ bkmHsDeriv x l m - bkmHsDeriv y l m := by
  have h := le_of_hasDerivAt_nonpos_off_finset (f := fun τ ↦ bkmHsDeriv τ l m) {l, m} hxy.le
    (fun τ hτ ↦ (ContinuousAt.bkmHsDeriv continuousAt_id continuousAt_const continuousAt_const
      (by linarith [hτ.1] : (0 : ℝ) < τ) hl hm).continuousWithinAt) fun τ hτ hS ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hS
      have hτ0 : 0 < τ := by linarith [hτ.1]
      refine ⟨hasDerivAt_bkmHsDeriv (X := id) (Y := fun _ ↦ l) (hasDerivAt_id τ)
        (hasDerivAt_const τ l) hτ0 hl hm hS.1 hS.2 hlm, ?_⟩
      simpa using spaceD₁₁_nonpos hτ0 hl hm hS.1 hS.2 hlm
  linarith

/-- **Dittmann's inequality (65)**: `hs′(x, λ, µ) ≥ hs′(y, λ, µ)` for positive `x < y` and `λ`,
`µ`. -/
theorem bkmHsDeriv_ineq65 {x y l m : ℝ} (hx : 0 < x) (hxy : x < y) (hl : 0 < l) (hm : 0 < m) :
    0 ≤ bkmHsDeriv x l m - bkmHsDeriv y l m := by
  rcases ne_or_eq l m with hlm | rfl
  · exact bkmHsDeriv_ineq65_of_ne hx hxy hl hm hlm
  have hc : ContinuousAt (fun m' ↦ bkmHsDeriv x l m' - bkmHsDeriv y l m') l :=
    (ContinuousAt.bkmHsDeriv continuousAt_const continuousAt_const continuousAt_id hx hl hl).sub
      (ContinuousAt.bkmHsDeriv continuousAt_const continuousAt_const continuousAt_id
        (hx.trans hxy) hl hl)
  have hT : Tendsto (fun m' ↦ bkmHsDeriv x l m' - bkmHsDeriv y l m') (𝓝[≠] l)
      (𝓝 (bkmHsDeriv x l l - bkmHsDeriv y l l)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hT ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds hl)] with m' hne hpos
  exact bkmHsDeriv_ineq65_of_ne hx hxy hl hpos (Ne.symm hne)

/-- **Dittmann's inequality (64)**: `hs′(x, y, λ) ≥ hs′(y, x, λ)` for positive `x < y` and `λ`. -/
theorem bkmHsDeriv_ineq64 {x y l : ℝ} (hx : 0 < x) (hxy : x < y) (hl : 0 < l) :
    0 ≤ bkmHsDeriv x y l - bkmHsDeriv y x l := by
  have hX : ∀ τ, HasDerivAt (fun τ ↦ x + τ) 1 τ := fun τ ↦ (hasDerivAt_id τ).const_add x
  have hY : ∀ τ, HasDerivAt (fun τ ↦ y - τ) (-1) τ := fun τ ↦ (hasDerivAt_id τ).const_sub y
  have h := le_of_hasDerivAt_nonpos_off_finset
    (f := fun τ ↦ bkmHsDeriv (x + τ) (y - τ) l - bkmHsDeriv (y - τ) (x + τ) l)
    {(y - x) / 2, l - x, y - l} (sub_nonneg.mpr hxy.le) (fun τ hτ ↦ by
      have h1 : 0 < x + τ := by linarith [hτ.1]
      have h2 : 0 < y - τ := by linarith [hτ.2]
      exact ((ContinuousAt.bkmHsDeriv (by fun_prop) (by fun_prop) continuousAt_const h1 h2
        hl).sub (ContinuousAt.bkmHsDeriv (by fun_prop) (by fun_prop) continuousAt_const h2 h1
          hl)).continuousWithinAt) fun τ hτ hS ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hS
      have h1 : 0 < x + τ := by linarith [hτ.1]
      have h2 : 0 < y - τ := by linarith [hτ.2]
      have hXY : x + τ ≠ y - τ := fun h ↦ hS.1 (by linarith)
      have hXl : x + τ ≠ l := fun h ↦ hS.2.1 (by linarith)
      have hYl : y - τ ≠ l := fun h ↦ hS.2.2 (by linarith)
      refine ⟨(hasDerivAt_bkmHsDeriv (hX τ) (hY τ) h1 h2 hl hXY hXl hYl).sub
        (hasDerivAt_bkmHsDeriv (hY τ) (hX τ) h2 h1 hl hXY.symm hYl hXl), ?_⟩
      have := spaceD₁₁_sub_spaceD₁₂_add_nonpos h1 h2 hl hXY hXl hYl
      rw [spaceD₁₂_swap (x + τ) (y - τ)]
      linarith
  rw [show x + (y - x) = y by ring, show y - (y - x) = x by ring, add_zero, sub_zero] at h
  linarith

end Concavity

/-! ### All four inequalities -/

/-- **Dittmann's inequalities (62)–(65) hold.** -/
theorem dittmannInequalities : DittmannInequalities where
  ineq62 _ _ hx hxy := bkmHsDeriv_ineq62 hx hxy
  ineq63 _ _ _ hx hxy hl := bkmHsDeriv_ineq63 hx hxy hl
  ineq64 _ _ _ hx hxy hl := bkmHsDeriv_ineq64 hx hxy hl
  ineq65 _ _ _ _ hx hxy hl hm := bkmHsDeriv_ineq65 hx hxy hl hm

end PetzCurvature
