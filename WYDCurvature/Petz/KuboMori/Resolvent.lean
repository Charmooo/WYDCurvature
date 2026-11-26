/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import WYDCurvature.Petz.KuboMori.ScalarCurvature

/-!
# The BKM form as the resolvent integral

The Bogoliubov–Kubo–Mori metric is usually written as the resolvent integral
`∫₀^∞ Re tr(A (ρ + t)⁻¹ B (ρ + t)⁻¹) dt`. The curvature computation uses the form `bkmForm` on
`[0, 1]` instead (`KuboMori/Form.lean`). This file proves that the two agree at every positive
definite `ρ` and for all matrices `A`, `B` (`bkmForm_eq_integral_resolvent`), so that the
statement of Petz's conjecture (`Main.lean`) is about the usual metric.

The proof goes through an eigenbasis of `ρ` rather than the substitution `t = s / (1 - s)`. At a
diagonal `ρ = diag(λ)` the resolvent is `diag(1/(λᵢ + t))`, the integrand is
`∑ᵢⱼ Re(Aᵢⱼ Bⱼᵢ) / ((λᵢ + t)(λⱼ + t))`, and each scalar integral is the BKM kernel:
`∫₀^∞ dt / ((x + t)(y + t)) = bkm x y` (`PetzKernel.integral_inv_mul_inv`), from the
antiderivative `log((x + t)/(y + t))/(y − x)`. So the integral is `bkmForm (diag λ) A B`
(`bkmForm_diagonal`). Both sides are invariant under conjugation by a unitary, which gives every
positive definite `ρ`.

## Main statements

* `PetzCurvature.PetzKernel.integral_inv_mul_inv`: the BKM kernel is the resolvent integral
  `∫₀^∞ dt / ((x + t)(y + t))`, and the integrand is integrable.
* `PetzCurvature.bkmForm_eq_integral_resolvent`: `bkmForm ρ A B` is the resolvent integral.

## References

* [Petz, *Monotone metrics on matrix spaces*][petz1996]
* [Lesniewski, Ruskai, *Monotone Riemannian metrics and relative entropy on noncommutative
  probability spaces*][lesniewski1999]
-/

open scoped Matrix.Norms.L2Operator ComplexOrder Topology
open Matrix MeasureTheory Set Filter

namespace PetzCurvature

namespace PetzKernel

/-- An antiderivative of `s ↦ 1/((x + s)(y + s))` on `s > −min(x, y)`. -/
noncomputable def bkmPrimitive (x y s : ℝ) : ℝ :=
  if x = y then -(x + s)⁻¹ else (Real.log (x + s) - Real.log (y + s)) / (y - x)

/-- `bkmPrimitive x y` is an antiderivative of `s ↦ 1/((x + s)(y + s))` where both factors are
positive. -/
theorem hasDerivAt_bkmPrimitive {x y s : ℝ} (hx : 0 < x + s) (hy : 0 < y + s) :
    HasDerivAt (bkmPrimitive x y) ((x + s)⁻¹ * (y + s)⁻¹) s := by
  unfold bkmPrimitive
  by_cases h : x = y
  · subst h
    simp only [↓reduceIte]
    have h1 : HasDerivAt (fun t ↦ x + t) 1 s := (hasDerivAt_id s).const_add x
    convert (h1.inv hx.ne').neg using 1
    field_simp
  · simp only [h, ↓reduceIte]
    have h1 : HasDerivAt (fun t ↦ Real.log (x + t)) (1 / (x + s)) s := by
      simpa using ((hasDerivAt_id s).const_add x).log hx.ne'
    have h2 : HasDerivAt (fun t ↦ Real.log (y + t)) (1 / (y + s)) s := by
      simpa using ((hasDerivAt_id s).const_add y).log hy.ne'
    convert (h1.sub h2).div_const (y - x) using 1
    have hyx : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    field_simp
    ring

/-- The antiderivative vanishes at infinity: `(x + s)/(y + s) → 1`. -/
theorem tendsto_bkmPrimitive (x y : ℝ) : Tendsto (bkmPrimitive x y) atTop (𝓝 0) := by
  unfold bkmPrimitive
  by_cases h : x = y
  · subst h
    simp only [↓reduceIte]
    have : Tendsto (fun s ↦ x + s) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
    simpa using (tendsto_inv_atTop_zero.comp this).neg
  · simp only [h, ↓reduceIte]
    have hq : Tendsto (fun s ↦ (x + s) / (y + s)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun s : ℝ ↦ (x - y) / (y + s)) atTop (𝓝 0) :=
        (tendsto_atTop_add_const_left _ _ tendsto_id).const_div_atTop _
      have h2 := h1.const_add 1
      rw [add_zero] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop (-y)] with s hs
      have : y + s ≠ 0 := by linarith
      field_simp
      ring
    have hl := ((Real.continuousAt_log one_ne_zero).tendsto.comp hq)
    rw [Real.log_one] at hl
    have hl' := hl.div_const (y - x)
    rw [zero_div] at hl'
    refine hl'.congr' ?_
    filter_upwards [eventually_gt_atTop (-x), eventually_gt_atTop (-y)] with s hsx hsy
    simp only [Function.comp_apply]
    rw [Real.log_div (by linarith) (by linarith)]

/-- Minus the antiderivative at `0` is the BKM kernel. -/
theorem bkmPrimitive_zero (x y : ℝ) : -bkmPrimitive x y 0 = bkm x y := by
  unfold bkmPrimitive bkm
  by_cases h : x = y
  · simp [h]
  · simp only [h, ↓reduceIte, add_zero]
    rw [← neg_div, neg_sub, ← neg_div_neg_eq, neg_sub, neg_sub]

/-- **The BKM kernel is the resolvent integral** `∫₀^∞ ds / ((x + s)(y + s))`, and the integrand is
integrable. -/
theorem integral_inv_mul_inv {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun s ↦ (x + s)⁻¹ * (y + s)⁻¹) (Ioi 0) ∧
      ∫ s in Ioi 0, (x + s)⁻¹ * (y + s)⁻¹ = bkm x y := by
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (bkmPrimitive x y) ((x + s)⁻¹ * (y + s)⁻¹) s :=
    fun s hs ↦ hasDerivAt_bkmPrimitive (by linarith [hs.out]) (by linarith [hs.out])
  have hpos : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ (x + s)⁻¹ * (y + s)⁻¹ := fun s hs ↦ by
    have := hs.out
    positivity
  have hc : ContinuousWithinAt (bkmPrimitive x y) (Ici 0) 0 :=
    (hd 0 self_mem_Ici).continuousAt.continuousWithinAt
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos (tendsto_bkmPrimitive x y), ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hc (fun s hs ↦ hd s (Ioi_subset_Ici_self hs)) hpos
    (tendsto_bkmPrimitive x y), zero_sub, bkmPrimitive_zero x y]

end PetzKernel

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The resolvent of a diagonal matrix with positive entries, at `t ≥ 0`. -/
theorem inv_diagonal_add_smul_one {l : d → ℝ} (hl : ∀ i, 0 < l i) {t : ℝ} (ht : 0 ≤ t) :
    (diagonal (fun i ↦ (l i : ℂ)) + (t : ℂ) • 1)⁻¹ =
      diagonal fun i ↦ (((l i + t)⁻¹ : ℝ) : ℂ) := by
  have e : diagonal (fun i ↦ (l i : ℂ)) + (t : ℂ) • 1 = diagonal fun i ↦ ((l i + t : ℝ) : ℂ) := by
    rw [smul_one_eq_diagonal, diagonal_add]
    push_cast
    rfl
  rw [e, inv_diagonal_ofReal fun i ↦ (by linarith [hl i] : l i + t ≠ 0)]

/-- The resolvent integrand at a diagonal matrix. -/
theorem re_trace_resolvent_diagonal {l : d → ℝ} (hl : ∀ i, 0 < l i) (A B : Matrix d d ℂ)
    {t : ℝ} (ht : 0 ≤ t) :
    (A * (diagonal (fun i ↦ (l i : ℂ)) + (t : ℂ) • 1)⁻¹ * B *
        (diagonal (fun i ↦ (l i : ℂ)) + (t : ℂ) • 1)⁻¹).trace.re =
      ∑ i, ∑ j, (l i + t)⁻¹ * (l j + t)⁻¹ * (A i j * B j i).re := by
  rw [inv_diagonal_add_smul_one hl ht]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.mul_diagonal, ← Complex.re_ofReal_mul]
  congr 1
  push_cast
  ring

/-- **The resolvent integral at a diagonal state** is the BKM form. -/
theorem bkmForm_diagonal_eq_integral {l : d → ℝ} (hl : ∀ i, 0 < l i) (A B : Matrix d d ℂ) :
    bkmForm (diagonal fun i ↦ (l i : ℂ)) A B =
      ∫ t in Ioi (0 : ℝ), (A * (diagonal (fun i ↦ (l i : ℂ)) + (t : ℂ) • 1)⁻¹ * B *
        (diagonal (fun i ↦ (l i : ℂ)) + (t : ℂ) • 1)⁻¹).trace.re := by
  have hI := fun i j ↦ PetzKernel.integral_inv_mul_inv (hl i) (hl j)
  rw [setIntegral_congr_fun measurableSet_Ioi fun t ht ↦
    re_trace_resolvent_diagonal hl A B (le_of_lt ht.out), integral_finsetSum, bkmForm_diagonal hl]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [integral_mul_const, (hI i j).2, bkmIntegral₂_eq_bkm (hl i) (hl j)]
    · exact fun j _ ↦ ((hI i j).1).mul_const _
  · exact fun i _ ↦ integrable_finsetSum _ fun j _ ↦ ((hI i j).1).mul_const _

/-- **The resolvent integral at `U diag(l) U*`**: both the BKM form and the resolvent integral
are invariant under conjugation by the unitary `U`, so the diagonal case
(`bkmForm_diagonal_eq_integral`) carries over. -/
theorem bkmForm_unitaryConjL_diagonal_eq_integral {U : Matrix d d ℂ} (hU : U ∈ unitaryGroup d ℂ)
    {l : d → ℝ} (hl : ∀ i, 0 < l i) (A B : Matrix d d ℂ) :
    bkmForm (unitaryConjL hU (diagonal fun i ↦ (l i : ℂ))) A B =
      ∫ t in Ioi (0 : ℝ), (A * (unitaryConjL hU (diagonal fun i ↦ (l i : ℂ)) + (t : ℂ) • 1)⁻¹ *
        B * (unitaryConjL hU (diagonal fun i ↦ (l i : ℂ)) + (t : ℂ) • 1)⁻¹).trace.re := by
  set D : Matrix d d ℂ := diagonal fun i ↦ (l i : ℂ)
  have hshift : ∀ t : ℝ, unitaryConjL hU D + (t : ℂ) • 1 = unitaryConjL hU (D + (t : ℂ) • 1) :=
    fun t ↦ by
      rw [map_add, unitaryConjL_apply (A := (t : ℂ) • 1), Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, Unitary.mul_star_self_of_mem hU]
  have hint : ∀ t : ℝ, (A * (unitaryConjL hU D + (t : ℂ) • 1)⁻¹ * B *
      (unitaryConjL hU D + (t : ℂ) • 1)⁻¹).trace.re =
      ((unitaryConjL hU).symm A * (D + (t : ℂ) • 1)⁻¹ * (unitaryConjL hU).symm B *
        (D + (t : ℂ) • 1)⁻¹).trace.re := fun t ↦ by
    rw [← sandwichForm_apply, ← sandwichForm_apply, hshift, inv_unitaryConjL,
      ← sandwichForm_unitaryConjL hU _ ((unitaryConjL hU).symm A),
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp_rw [hint]
  rw [← bkmForm_diagonal_eq_integral hl, ← bkmForm_unitaryConjL_apply hU D,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- **The BKM form is the resolvent integral**: for positive definite `ρ` and all matrices `A`,
`B`, `bkmForm ρ A B = ∫₀^∞ Re tr(A (ρ + t)⁻¹ B (ρ + t)⁻¹) dt`. -/
theorem bkmForm_eq_integral_resolvent {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) (A B : Matrix d d ℂ) :
    bkmForm ρ A B =
      ∫ t in Ioi (0 : ℝ), (A * (ρ + (t : ℂ) • 1)⁻¹ * B * (ρ + (t : ℂ) • 1)⁻¹).trace.re := by
  have hU := hρ.1.eigenvectorUnitary.2
  have hρU : ρ = unitaryConjL hU (diagonal fun i ↦ (hρ.1.eigenvalues i : ℂ)) := by
    conv_lhs => rw [hρ.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have h := bkmForm_unitaryConjL_diagonal_eq_integral hU hρ.eigenvalues_pos A B
  rwa [← hρU] at h

end PetzCurvature
