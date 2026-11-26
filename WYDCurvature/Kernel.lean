/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.ForMathlib.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The kernels of the WYD metric in logarithmic coordinates

`e1`, `e2` are the first and second divided differences of `exp`, as integrals over `[0,1]`.
With `b = β`, `1 - β`:
* `metK β x y = e1(βx, βy) e1((1-β)x, (1-β)y)`: the metric, in the coordinates `D log ρ [X]`;
* `cubK β x k y = β e2(βx, βk, βy) e1((1-β)x, (1-β)y) - (1-β) e2((1-β)x,...) e1(βx, βy)`: the
  cubic form, symmetric in its three arguments.
-/

open Set Filter MeasureTheory Real
open scoped Topology Interval

namespace WYD

/-! ### Divided differences of `exp` -/

/-- The first divided difference of `exp`. -/
noncomputable def e1 (x y : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, exp (t * x + (1 - t) * y)

/-- The second divided difference of `exp`. -/
noncomputable def e2 (x y z : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t * e1 (t * x + (1 - t) * z) (t * y + (1 - t) * z)

theorem e1_mul_sub (x y : ℝ) : e1 x y * (x - y) = exp x - exp y := by
  have h : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t ↦ exp (t * x + (1 - t) * y))
      (exp (t * x + (1 - t) * y) * (x - y)) t := fun t _ ↦ by
    have := ((hasDerivAt_id t).mul_const x).add (((hasDerivAt_id t).const_sub 1).mul_const y)
    exact this.exp.congr_deriv (by simp; ring)
  rw [e1, ← intervalIntegral.integral_mul_const,
    intervalIntegral.integral_eq_sub_of_hasDerivAt h (by
      apply Continuous.intervalIntegrable; fun_prop)]
  simp

theorem e1_self (x : ℝ) : e1 x x = exp x := by
  rw [e1]
  have : ∀ t : ℝ, t * x + (1 - t) * x = x := fun t ↦ by ring
  simp [this]

theorem e1_of_ne {x y : ℝ} (h : x ≠ y) : e1 x y = (exp x - exp y) / (x - y) :=
  eq_div_of_mul_eq (sub_ne_zero.2 h) (e1_mul_sub x y)

theorem e1_comm (x y : ℝ) : e1 x y = e1 y x := by
  rcases eq_or_ne x y with rfl | h
  · rfl
  · rw [e1_of_ne h, e1_of_ne h.symm, ← neg_div_neg_eq, neg_sub, neg_sub]

theorem e1_pos (x y : ℝ) : 0 < e1 x y :=
  intervalIntegral.intervalIntegral_pos_of_pos
    (Continuous.intervalIntegrable (by fun_prop) _ _) (fun _ ↦ exp_pos _) one_pos

theorem contDiff_e1 (n : ℕ) : ContDiff ℝ n fun p : ℝ × ℝ ↦ e1 p.1 p.2 :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_intervalIntegral_of_contDiffAt n
    (f := fun z : (ℝ × ℝ) × ℝ ↦ exp (z.2 * z.1.1 + (1 - z.2) * z.1.2)) fun _ _ ↦ by fun_prop

theorem contDiff_e1_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ}
    {n : ℕ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) : ContDiff ℝ n fun x ↦ e1 (f x) (g x) := by
  simpa only [Function.comp_def] using (contDiff_e1 n).comp (hf.prodMk hg)

theorem continuous_e1_comp {E : Type*} [TopologicalSpace E] {f g : E → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x ↦ e1 (f x) (g x) := by
  simpa only [Function.comp_def] using (contDiff_e1 0).continuous.comp (hf.prodMk hg)

theorem contDiff_e2 (n : ℕ) : ContDiff ℝ n fun p : ℝ × ℝ × ℝ ↦ e2 p.1 p.2.1 p.2.2 := by
  refine contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_intervalIntegral_of_contDiffAt n
    (f := fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2 * e1 (z.2 * z.1.1 + (1 - z.2) * z.1.2.2)
      (z.2 * z.1.2.1 + (1 - z.2) * z.1.2.2)) fun _ _ ↦ ?_
  refine (contDiff_snd.mul (contDiff_e1_comp ?_ ?_)).contDiffAt <;> fun_prop

theorem contDiff_e2_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g h : E → ℝ}
    {n : ℕ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hh : ContDiff ℝ n h) :
    ContDiff ℝ n fun x ↦ e2 (f x) (g x) (h x) := by
  simpa only [Function.comp_def] using (contDiff_e2 n).comp (hf.prodMk (hg.prodMk hh))

theorem e2_mul_sub (x y z : ℝ) : e2 x y z * (x - y) = e1 x z - e1 y z := by
  rw [e2, ← intervalIntegral.integral_mul_const, e1, e1, ← intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have := e1_mul_sub (t * x + (1 - t) * z) (t * y + (1 - t) * z)
  linear_combination this

theorem e2_self_mul_sub (x z : ℝ) : e2 x x z * (x - z) = exp x - e1 x z := by
  have h : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t ↦ t * exp (t * x + (1 - t) * z))
      (exp (t * x + (1 - t) * z) + t * exp (t * x + (1 - t) * z) * (x - z)) t := fun t _ ↦ by
    have := ((hasDerivAt_id t).mul_const x).add (((hasDerivAt_id t).const_sub 1).mul_const z)
    exact ((hasDerivAt_id t).mul this.exp).congr_deriv (by simp; ring)
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt h (by
      apply Continuous.intervalIntegrable; fun_prop)
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_mul_const] at h2
  simp only [e2, e1_self]
  simp only [one_mul, sub_self, zero_mul, add_zero, sub_zero] at h2
  rw [e1]
  linarith

theorem e2_self (x : ℝ) : e2 x x x = exp x / 2 := by
  have h : ∀ t : ℝ, t * x + (1 - t) * x = x := fun t ↦ by ring
  simp only [e2, h, e1_self]
  rw [intervalIntegral.integral_mul_const, integral_id]
  ring

theorem e2_comm₁₂ (x y z : ℝ) : e2 x y z = e2 y x z := by
  simp only [e2, e1_comm (_ * x + _)]

theorem e2_mul_sub_right (x y z : ℝ) : e2 x y z * (y - z) = e1 x y - e1 x z := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [e2_self_mul_sub, e1_self]
  have hxy' := sub_ne_zero.2 hxy
  have h := e2_mul_sub x y z
  apply mul_right_cancel₀ hxy'
  rw [mul_right_comm, h]
  rcases eq_or_ne x z with rfl | hxz
  · rw [e1_comm y x]; ring
  rcases eq_or_ne y z with rfl | hyz
  · simp
  rw [e1_of_ne hxz, e1_of_ne hyz, e1_of_ne hxy]
  have := sub_ne_zero.2 hxz; have := sub_ne_zero.2 hyz
  field_simp
  ring

theorem e2_comm₂₃ (x y z : ℝ) : e2 x y z = e2 x z y := by
  rcases eq_or_ne y z with rfl | h
  · rfl
  apply mul_right_cancel₀ (sub_ne_zero.2 h)
  have h1 := e2_mul_sub_right x y z
  have h2 := e2_mul_sub_right x z y
  linarith

/-! ### The metric and cubic kernels -/

variable (β : ℝ)

/-- The metric kernel in logarithmic coordinates. -/
noncomputable def metK (x y : ℝ) : ℝ := e1 (β * x) (β * y) * e1 ((1 - β) * x) ((1 - β) * y)

/-- The cubic kernel in logarithmic coordinates. -/
noncomputable def cubK (x k y : ℝ) : ℝ :=
  β * e2 (β * x) (β * k) (β * y) * e1 ((1 - β) * x) ((1 - β) * y) -
    (1 - β) * e2 ((1 - β) * x) ((1 - β) * k) ((1 - β) * y) * e1 (β * x) (β * y)

variable {β}

theorem metK_pos (x y : ℝ) : 0 < metK β x y := mul_pos (e1_pos _ _) (e1_pos _ _)

theorem metK_comm (x y : ℝ) : metK β x y = metK β y x := by
  rw [metK, metK, e1_comm, e1_comm ((1 - β) * x)]

theorem metK_self (x : ℝ) : metK β x x = exp x := by
  rw [metK, e1_self, e1_self, ← exp_add]; congr 1; ring

theorem cubK_mul_sub (x k y : ℝ) : cubK β x k y * (x - k) =
    e1 (β * x) (β * y) * e1 ((1 - β) * k) ((1 - β) * y) -
      e1 (β * k) (β * y) * e1 ((1 - β) * x) ((1 - β) * y) := by
  have h1 := e2_mul_sub (β * x) (β * k) (β * y)
  have h2 := e2_mul_sub ((1 - β) * x) ((1 - β) * k) ((1 - β) * y)
  rw [cubK]
  linear_combination (e1 ((1 - β) * x) ((1 - β) * y)) * h1 - e1 (β * x) (β * y) * h2

theorem cubK_comm₁₂ (x k y : ℝ) : cubK β x k y = cubK β k x y := by
  rcases eq_or_ne x k with rfl | h
  · rfl
  apply mul_right_cancel₀ (sub_ne_zero.2 h)
  have h1 := cubK_mul_sub (β := β) x k y
  have h2 := cubK_mul_sub (β := β) k x y
  linarith

theorem cubK_comm₁₃ (x k y : ℝ) : cubK β x k y = cubK β y k x := by
  have h : ∀ x y z, e2 x y z = e2 z y x := fun x y z ↦ by
    rw [e2_comm₁₂, e2_comm₂₃, e2_comm₁₂]
  rw [cubK, cubK, e1_comm, e1_comm (β * x), h (β * x), h ((1 - β) * x)]

theorem cubK_comm₂₃ (x k y : ℝ) : cubK β x k y = cubK β x y k := by
  rw [cubK_comm₁₂, cubK_comm₁₃, cubK_comm₁₂]

theorem cubK_self (x : ℝ) : cubK β x x x = (2 * β - 1) / 2 * exp x := by
  have : exp (β * x) * exp ((1 - β) * x) = exp x := by rw [← exp_add]; congr 1; ring
  rw [cubK, e2_self, e2_self, e1_self, e1_self]
  linear_combination (2 * β - 1) / 2 * this

/-- `C(x, x, y) + C(x, y, y) = (2β - 1) M(x, y)`. -/
theorem cubK_add (x y : ℝ) : cubK β x x y + cubK β x y y = (2 * β - 1) * metK β x y := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [cubK_self, metK_self]; ring
  apply mul_right_cancel₀ (sub_ne_zero.2 hxy)
  have h1 := cubK_mul_sub (β := β) x y x
  have h2 := cubK_mul_sub (β := β) x y y
  rw [cubK_comm₂₃ x y x, e1_self, e1_self, e1_comm ((1 - β) * y), e1_comm (β * y)] at h1
  rw [e1_self, e1_self] at h2
  have a1 := e1_mul_sub (β * x) (β * y)
  have a2 := e1_mul_sub ((1 - β) * x) ((1 - β) * y)
  rw [metK]
  linear_combination h1 + h2 - e1 ((1 - β) * x) ((1 - β) * y) * a1 + e1 (β * x) (β * y) * a2

/-! ### The curvature kernel -/

variable (β)

/-- The curvature kernel before symmetrization, in logarithmic coordinates. -/
noncomputable def curvK (x y z : ℝ) : ℝ :=
  cubK β x y z ^ 2 / (2 * (metK β x y * metK β y z * metK β z x)) -
    cubK β x x y * cubK β x x z / (metK β x x * (metK β x y * metK β x z))

/-- The symmetrized curvature kernel in logarithmic coordinates. -/
noncomputable def hsL (x y z : ℝ) : ℝ := (curvK β x y z + curvK β y z x + curvK β z x y) / 3

/-- **The curvature function `hs_β`** of the WYD metric, on eigenvalues. -/
noncomputable def wydHs (x y z : ℝ) : ℝ := hsL β (log x) (log y) (log z)

variable {β}

theorem curvK_comm₂₃ (x y z : ℝ) : curvK β x y z = curvK β x z y := by
  rw [curvK, curvK, cubK_comm₂₃ x y z, metK_comm x y, metK_comm y z, metK_comm z x]
  ring

theorem hsL_comm₁₂ (x y z : ℝ) : hsL β x y z = hsL β y x z := by
  rw [hsL, hsL, curvK_comm₂₃ x y z, curvK_comm₂₃ y z x, curvK_comm₂₃ z x y]; ring

theorem hsL_comm₂₃ (x y z : ℝ) : hsL β x y z = hsL β x z y := by
  rw [hsL, hsL, curvK_comm₂₃ x y z, curvK_comm₂₃ y z x, curvK_comm₂₃ z x y]; ring

theorem wydHs_comm₁₂ (x y z : ℝ) : wydHs β x y z = wydHs β y x z := hsL_comm₁₂ _ _ _

theorem wydHs_comm₂₃ (x y z : ℝ) : wydHs β x y z = wydHs β x z y := hsL_comm₂₃ _ _ _

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g h : E → ℝ} {n : ℕ}

theorem contDiff_metK (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n fun x ↦ metK β (f x) (g x) :=
  (contDiff_e1_comp (contDiff_const.mul hf) (contDiff_const.mul hg)).mul
    (contDiff_e1_comp (contDiff_const.mul hf) (contDiff_const.mul hg))

theorem contDiff_cubK (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hh : ContDiff ℝ n h) :
    ContDiff ℝ n fun x ↦ cubK β (f x) (g x) (h x) := by
  have c : ∀ (a : ℝ) {u : E → ℝ}, ContDiff ℝ n u → ContDiff ℝ n fun x ↦ a * u x :=
    fun a _ hu ↦ contDiff_const.mul hu
  exact ((c β (contDiff_e2_comp (c _ hf) (c _ hg) (c _ hh))).mul
    (contDiff_e1_comp (c _ hf) (c _ hh))).sub
      ((c (1 - β) (contDiff_e2_comp (c _ hf) (c _ hg) (c _ hh))).mul
        (contDiff_e1_comp (c _ hf) (c _ hh)))

theorem contDiff_curvK (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hh : ContDiff ℝ n h) :
    ContDiff ℝ n fun x ↦ curvK β (f x) (g x) (h x) := by
  refine ContDiff.sub (ContDiff.div ((contDiff_cubK hf hg hh).pow 2) (contDiff_const.mul
    (((contDiff_metK hf hg).mul (contDiff_metK hg hh)).mul (contDiff_metK hh hf))) fun x ↦ ?_)
    (ContDiff.div ((contDiff_cubK hf hf hg).mul (contDiff_cubK hf hf hh))
      ((contDiff_metK hf hf).mul ((contDiff_metK hf hg).mul (contDiff_metK hf hh))) fun x ↦ ?_)
  · have := metK_pos (β := β) (f x) (g x); have := metK_pos (β := β) (g x) (h x)
    have := metK_pos (β := β) (h x) (f x); positivity
  · have := metK_pos (β := β) (f x) (f x); have := metK_pos (β := β) (f x) (g x)
    have := metK_pos (β := β) (f x) (h x); positivity

theorem contDiff_hsL (n : ℕ) : ContDiff ℝ n fun p : ℝ × ℝ × ℝ ↦ hsL β p.1 p.2.1 p.2.2 := by
  have h1 : ContDiff ℝ n fun p : ℝ × ℝ × ℝ ↦ p.1 := contDiff_fst
  have h2 : ContDiff ℝ n fun p : ℝ × ℝ × ℝ ↦ p.2.1 := contDiff_snd.fst
  have h3 : ContDiff ℝ n fun p : ℝ × ℝ × ℝ ↦ p.2.2 := contDiff_snd.snd
  exact (((contDiff_curvK h1 h2 h3).add (contDiff_curvK h2 h3 h1)).add
    (contDiff_curvK h3 h1 h2)).div_const 3

/-- `hs_β` is smooth on the positive octant. -/
theorem contDiffAt_wydHs {p : ℝ × ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2.1) (h3 : 0 < p.2.2)
    (n : ℕ) : ContDiffAt ℝ n (fun q : ℝ × ℝ × ℝ ↦ wydHs β q.1 q.2.1 q.2.2) p :=
  (contDiff_hsL n).contDiffAt.comp (f := fun q : ℝ × ℝ × ℝ ↦ (log q.1, log q.2.1, log q.2.2)) p
    ((contDiffAt_fst.log h1.ne').prodMk ((contDiffAt_snd.fst.log h2.ne').prodMk
      (contDiffAt_snd.snd.log h3.ne')))

end Smooth

end WYD
