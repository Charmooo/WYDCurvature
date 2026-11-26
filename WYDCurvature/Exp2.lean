/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.ForMathlib.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The second derivative of the exponential

The second-order part of `TimelibBeta/Mathlib/Analysis/Normed/Algebra/ExponentialDeriv` and
`TimelibBeta/Mathlib/Analysis/Matrix/DaleckiiKrein` in the Time Library project, by the same
author, on top of `AlphaCurvature.ForMathlib.ExpDeriv`.
-/

open Finset Metric Nat NormedSpace
open scoped RightActions

namespace AlphaCurvature

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

omit [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸] in
private theorem norm_pow_le_one_add' (y : 𝔸) (k : ℕ) : ‖y ^ k‖ ≤ (‖(1 : 𝔸)‖ + 1) * ‖y‖ ^ k := by
  rcases k with _ | k
  · simp
  · calc ‖y ^ (k + 1)‖ ≤ ‖y‖ ^ (k + 1) := norm_pow_le' y k.succ_pos
      _ ≤ (‖(1 : 𝔸)‖ + 1) * ‖y‖ ^ (k + 1) :=
        le_mul_of_one_le_left (by positivity) (by linarith [norm_nonneg (1 : 𝔸)])

private theorem summable_powDeriv' (x : 𝔸) :
    Summable fun n : ℕ => (n !⁻¹ : 𝕂) • powDeriv 𝕂 x n := by
  have hb : Summable fun n : ℕ => (n ! : ℝ)⁻¹ * ((‖(1 : 𝔸)‖ + 1) ^ 2 * (n * ‖x‖ ^ n.pred)) := by
    have h : Summable fun n : ℕ => (n ! : ℝ)⁻¹ * (n * ‖x‖ ^ n.pred) := by
      refine (summable_nat_add_iff 1).mp ?_
      refine (Real.summable_pow_div_factorial ‖x‖).congr fun n => ?_
      simp only [Nat.pred_succ, Nat.cast_add, Nat.cast_one, Nat.factorial_succ, Nat.cast_mul]
      field_simp
    exact (h.mul_left ((‖(1 : 𝔸)‖ + 1) ^ 2)).congr fun n => by ring
  refine Summable.of_norm_bounded hb fun n => ?_
  rw [norm_smul, norm_inv, RCLike.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_powDeriv_le x n) (by positivity)

/-! ### The second derivative -/

variable (𝕂) in
/-- The derivative of `y ↦ powDeriv y n` at `x`:
`k ↦ (h ↦ ∑_{i<n} (x^{n−1−i} h powDeriv x i k + powDeriv x (n−1−i) k h xⁱ))`. -/
noncomputable def powDeriv2 (x : 𝔸) (n : ℕ) : 𝔸 →L[𝕂] 𝔸 →L[𝕂] 𝔸 :=
  ∑ i ∈ range n, ((ContinuousLinearMap.mulLeftRight 𝕂 𝔸).precompR 𝔸 (x ^ (n.pred - i))
      (powDeriv 𝕂 x i) +
    (ContinuousLinearMap.mulLeftRight 𝕂 𝔸).precompL 𝔸 (powDeriv 𝕂 x (n.pred - i)) (x ^ i))

omit [CompleteSpace 𝔸] in
theorem powDeriv2_apply (x : 𝔸) (n : ℕ) (k h : 𝔸) :
    powDeriv2 𝕂 x n k h = ∑ i ∈ range n,
      (x ^ (n.pred - i) * h * powDeriv 𝕂 x i k + powDeriv 𝕂 x (n.pred - i) k * h * x ^ i) := by
  simp [powDeriv2]

omit [CompleteSpace 𝔸] in
theorem hasFDerivAt_powDeriv (x : 𝔸) (n : ℕ) :
    HasFDerivAt (fun y : 𝔸 => powDeriv 𝕂 y n) (powDeriv2 𝕂 x n) x := by
  have hfun : (fun y : 𝔸 => powDeriv 𝕂 y n) = fun y => ∑ i ∈ range n,
      ContinuousLinearMap.mulLeftRight 𝕂 𝔸 (y ^ (n.pred - i)) (y ^ i) := by
    funext y
    ext h
    simp [powDeriv_apply]
  rw [hfun]
  exact HasFDerivAt.fun_sum fun i _ =>
    (ContinuousLinearMap.mulLeftRight 𝕂 𝔸).hasFDerivAt_of_bilinear
      (hasFDerivAt_pow_powDeriv x _) (hasFDerivAt_pow_powDeriv x i)

omit [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸] in
private theorem norm_pow_le_of_le {x : 𝔸} {R : ℝ} (hR : 1 ≤ R) (hx : ‖x‖ ≤ R) {m n : ℕ}
    (hmn : m ≤ n) : ‖x ^ m‖ ≤ (‖(1 : 𝔸)‖ + 1) * R ^ n :=
  (norm_pow_le_one_add' x m).trans (mul_le_mul_of_nonneg_left
    ((pow_le_pow_left₀ (norm_nonneg _) hx m).trans (pow_le_pow_right₀ hR hmn)) (by positivity))

omit [CompleteSpace 𝔸] in
private theorem norm_powDeriv_le_of_le {x : 𝔸} {R : ℝ} (hR : 1 ≤ R) (hx : ‖x‖ ≤ R) {m n : ℕ}
    (hmn : m ≤ n) : ‖powDeriv 𝕂 x m‖ ≤ (‖(1 : 𝔸)‖ + 1) ^ 2 * (n * R ^ n) := by
  refine (norm_powDeriv_le x m).trans (mul_le_mul_of_nonneg_left (mul_le_mul
    (Nat.cast_le.mpr hmn) ?_ (by positivity) (by positivity)) (by positivity))
  exact (pow_le_pow_left₀ (norm_nonneg _) hx _).trans
    (pow_le_pow_right₀ hR ((Nat.pred_le m).trans hmn))

omit [CompleteSpace 𝔸] in
theorem norm_powDeriv2_le {x : 𝔸} {R : ℝ} (hR : 1 ≤ R) (hx : ‖x‖ ≤ R) (n : ℕ) :
    ‖powDeriv2 𝕂 x n‖ ≤ 2 * (‖(1 : 𝔸)‖ + 1) ^ 3 * (n * (n * (R ^ n * R ^ n))) := by
  set K := ‖(1 : 𝔸)‖ + 1
  have hK : 0 ≤ K := by positivity
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun k h => ?_
  rw [powDeriv2_apply]
  calc ‖∑ i ∈ range n, (x ^ (n.pred - i) * h * powDeriv 𝕂 x i k +
        powDeriv 𝕂 x (n.pred - i) k * h * x ^ i)‖
      ≤ ∑ i ∈ range n, ‖x ^ (n.pred - i) * h * powDeriv 𝕂 x i k +
        powDeriv 𝕂 x (n.pred - i) k * h * x ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range n, 2 * K ^ 3 * (n * (R ^ n * R ^ n)) * ‖k‖ * ‖h‖ := by
        refine sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := (mem_range.mp hi).le
        have hα : n.pred - i ≤ n := (Nat.sub_le _ _).trans (Nat.pred_le n)
        have p1 := norm_pow_le_of_le hR hx hα
        have p2 := norm_pow_le_of_le hR hx hi'
        have q1 := norm_powDeriv_le_of_le (𝕂 := 𝕂) hR hx hi'
        have q2 := norm_powDeriv_le_of_le (𝕂 := 𝕂) hR hx hα
        have e1 : ‖x ^ (n.pred - i) * h * powDeriv 𝕂 x i k‖ ≤
            K * R ^ n * ‖h‖ * (K ^ 2 * (n * R ^ n) * ‖k‖) :=
          (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right p1 (norm_nonneg _)))
            ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right q1 (norm_nonneg _))) (norm_nonneg _) (by positivity))
        have e2 : ‖powDeriv 𝕂 x (n.pred - i) k * h * x ^ i‖ ≤
            K ^ 2 * (n * R ^ n) * ‖k‖ * ‖h‖ * (K * R ^ n) :=
          (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right q2 (norm_nonneg _))) (norm_nonneg _))) p2
            (norm_nonneg _) (by positivity))
        exact (norm_add_le _ _).trans ((add_le_add e1 e2).trans_eq (by ring))
    _ = 2 * K ^ 3 * (n * (n * (R ^ n * R ^ n))) * ‖k‖ * ‖h‖ := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring

private theorem summable_bound2 {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    Summable fun n : ℕ => (n ! : ℝ)⁻¹ * (C * (n * (n * (R ^ n * R ^ n)))) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((Real.summable_pow_div_factorial (2 * 2 * (R * R))).mul_left C)
  have h2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast n.lt_two_pow_self.le
  have h4 : (n : ℝ) * (n * (R ^ n * R ^ n)) ≤ (2 * 2 * (R * R)) ^ n := by
    rw [mul_pow, mul_pow, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul h2 h2 (by positivity) (by positivity))
      (by positivity)
  calc (n ! : ℝ)⁻¹ * (C * (n * (n * (R ^ n * R ^ n))))
      = C * ((n * (n * (R ^ n * R ^ n))) * (n ! : ℝ)⁻¹) := by ring
    _ ≤ C * ((2 * 2 * (R * R)) ^ n * (n ! : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 (by positivity)) hC
    _ = C * ((2 * 2 * (R * R)) ^ n / n !) := by rw [div_eq_mul_inv]

omit [CompleteSpace 𝔸] in
private theorem norm_term2_le {x : 𝔸} {R : ℝ} (hR : 1 ≤ R) (hx : ‖x‖ ≤ R) (n : ℕ) :
    ‖(n !⁻¹ : 𝕂) • powDeriv2 𝕂 x n‖ ≤
      (n ! : ℝ)⁻¹ * (2 * (‖(1 : 𝔸)‖ + 1) ^ 3 * (n * (n * (R ^ n * R ^ n)))) := by
  rw [norm_smul, norm_inv, RCLike.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_powDeriv2_le hR hx n) (by positivity)

private theorem summable_powDeriv2 (x : 𝔸) :
    Summable fun n : ℕ => (n !⁻¹ : 𝕂) • powDeriv2 𝕂 x n :=
  Summable.of_norm_bounded (summable_bound2 (by positivity) (by positivity))
    (norm_term2_le (R := ‖x‖ + 1) (by simp) (by simp))

variable (𝕂) in
/-- The second derivative of the exponential at `x`: `∑ₙ (1/n!) powDeriv2 x n`. -/
noncomputable def expDeriv2 (x : 𝔸) : 𝔸 →L[𝕂] 𝔸 →L[𝕂] 𝔸 :=
  ∑' n : ℕ, (n !⁻¹ : 𝕂) • powDeriv2 𝕂 x n

/-- **The second derivative of the exponential**: `expDeriv` has derivative `expDeriv2 x` at `x`. -/
theorem hasFDerivAt_expDeriv (x : 𝔸) : HasFDerivAt (expDeriv 𝕂) (expDeriv2 𝕂 x) x := by
  let : NormedSpace ℝ 𝔸 := NormedSpace.restrictScalars ℝ 𝕂 𝔸
  set R := ‖x‖ + 1
  have hR : 1 ≤ R := by simp [R]
  have hs : x ∈ ball (0 : 𝔸) R := by simp [R]
  exact hasFDerivAt_tsum_of_isPreconnected (f := fun n y => (n !⁻¹ : 𝕂) • powDeriv 𝕂 y n)
    (f' := fun n y => (n !⁻¹ : 𝕂) • powDeriv2 𝕂 y n)
    (summable_bound2 (by positivity) (zero_le_one.trans hR)) isOpen_ball
    (convex_ball _ _).isPreconnected
    (fun n y _ => (hasFDerivAt_powDeriv (𝕂 := 𝕂) y n).const_smul (n !⁻¹ : 𝕂))
    (fun n y hy => norm_term2_le hR (mem_ball_zero_iff.mp hy).le n) hs
    (summable_powDeriv' x) hs

/-- The series of `expDeriv2 x k h`. -/
theorem hasSum_expDeriv2 (x k h : 𝔸) :
    HasSum (fun n : ℕ => (n !⁻¹ : 𝕂) • ∑ i ∈ range n,
      (x ^ (n.pred - i) * h * powDeriv 𝕂 x i k + powDeriv 𝕂 x (n.pred - i) k * h * x ^ i))
      (expDeriv2 𝕂 x k h) := by
  have hsum := ((summable_powDeriv2 (𝕂 := 𝕂) x).hasSum.mapL
    (ContinuousLinearMap.apply 𝕂 (𝔸 →L[𝕂] 𝔸) k)).mapL (ContinuousLinearMap.apply 𝕂 𝔸 h)
  simp only [ContinuousLinearMap.apply_apply, smul_apply, powDeriv2_apply] at hsum
  exact hsum

/-- The derivative of the exponential is `expDeriv` everywhere. -/
theorem fderiv_exp' : fderiv 𝕂 (exp : 𝔸 → 𝔸) = expDeriv 𝕂 :=
  funext fun y => (hasFDerivAt_exp' y).fderiv

/-- **The second derivative of the exponential is symmetric**:
`expDeriv2 x k h = expDeriv2 x h k`. -/
theorem expDeriv2_comm (x k h : 𝔸) : expDeriv2 𝕂 x k h = expDeriv2 𝕂 x h k := by
  have hc : ContDiffAt 𝕂 (⊤ : WithTop ℕ∞) (exp : 𝔸 → 𝔸) x := (exp_analytic (𝕂 := 𝕂) x).contDiffAt
  have hs := hc.isSymmSndFDerivAt le_top k h
  rwa [fderiv_exp', (hasFDerivAt_expDeriv x).fderiv] at hs

namespace Matrix

open _root_.Matrix
open scoped Matrix.Norms.L2Operator

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
private noncomputable def entryCLM (i j : d) : Matrix d d ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (entryLinearMap ℂ ℂ i j)

omit [DecidableEq d] in
private theorem entryCLM_apply (i j : d) (M : Matrix d d ℂ) : entryCLM i j M = M i j :=
  rfl

private def hterm (m : ℕ) (y z : ℂ) : ℂ :=
  ∑ p ∈ range m, y ^ (m.pred - p) * z ^ p

/-- The coefficient of `h k` in the second derivative of `yⁿ` at a diagonal matrix. -/
private def termL (n : ℕ) (x y z : ℂ) : ℂ :=
  ∑ i ∈ range n, x ^ (n.pred - i) * hterm i y z

/-- The coefficient of `k h` in the second derivative of `yⁿ` at a diagonal matrix. -/
private def termR (n : ℕ) (x y z : ℂ) : ℂ :=
  ∑ i ∈ range n, hterm (n.pred - i) x y * z ^ i

private theorem hterm_mul_sub (m : ℕ) (y z : ℂ) : hterm m y z * (y - z) = y ^ m - z ^ m := by
  have e : hterm m y z = ∑ i ∈ range m, y ^ i * z ^ (m - 1 - i) := by
    rw [hterm, ← sum_range_reflect]
    refine sum_congr rfl fun i hi => ?_
    have := mem_range.mp hi
    rw [Nat.pred_eq_sub_one]
    congr 2
    omega
  rw [e, geom_sum₂_mul]

private theorem hterm_self (m : ℕ) (x : ℂ) : hterm m x x = m * x ^ m.pred := by
  rw [hterm, sum_congr rfl fun i hi => (show x ^ (m.pred - i) * x ^ i = x ^ m.pred by
    rw [← pow_add, Nat.sub_add_cancel
      (by have := mem_range.mp hi; rw [Nat.pred_eq_sub_one]; omega)]),
    sum_const, card_range, nsmul_eq_mul]

private theorem powDeriv_diagonal_apply (a : d → ℂ) (m : ℕ) (k : Matrix d d ℂ) (l j : d) :
    powDeriv ℂ (diagonal a) m k l j = hterm m (a l) (a j) * k l j := by
  rw [powDeriv_apply, Matrix.sum_apply, hterm, sum_mul]
  refine sum_congr rfl fun p _ => ?_
  rw [diagonal_pow_mul_mul_diagonal_pow_apply]
  ring

private theorem diagonal_mul_mul_apply (v : d → ℂ) (h M : Matrix d d ℂ) (r c : d) :
    (diagonal v * h * M) r c = ∑ l, v r * h r l * M l c := by
  rw [Matrix.mul_assoc, diagonal_mul, Matrix.mul_apply, mul_sum]
  exact sum_congr rfl fun l _ => by ring

private theorem mul_mul_diagonal_apply (w : d → ℂ) (h M : Matrix d d ℂ) (r c : d) :
    (M * h * diagonal w) r c = ∑ l, M r l * h l c * w c := by
  rw [mul_diagonal, Matrix.mul_apply, sum_mul]

private theorem expDeriv2_term_apply (a : d → ℂ) (k h : Matrix d d ℂ) (n : ℕ) (r c : d) :
    (∑ i ∈ range n, (diagonal a ^ (n.pred - i) * h * powDeriv ℂ (diagonal a) i k +
      powDeriv ℂ (diagonal a) (n.pred - i) k * h * diagonal a ^ i)) r c =
      ∑ l, (termL n (a r) (a l) (a c) * (h r l * k l c) +
        termR n (a r) (a l) (a c) * (k r l * h l c)) := by
  simp only [Matrix.sum_apply, Matrix.add_apply, diagonal_pow, diagonal_mul_mul_apply,
    mul_mul_diagonal_apply, powDeriv_diagonal_apply, Pi.pow_apply, termL, termR, sum_mul,
    sum_add_distrib]
  rw [sum_comm (s := range n), sum_comm (s := range n) (t := univ)]
  refine congrArg₂ (· + ·) ?_ ?_ <;> refine sum_congr rfl fun l _ => sum_congr rfl fun i _ => by ring

private theorem hasSum_entry2 (a : d → ℂ) (k h : Matrix d d ℂ) (r c : d) :
    HasSum (fun n : ℕ => (n !⁻¹ : ℂ) * ∑ l, (termL n (a r) (a l) (a c) * (h r l * k l c) +
        termR n (a r) (a l) (a c) * (k r l * h l c)))
      (expDeriv2 ℂ (diagonal a) k h r c) := by
  have hs := (hasSum_expDeriv2 (𝕂 := ℂ) (diagonal a) k h).mapL (entryCLM r c)
  simp only [entryCLM_apply, _root_.Matrix.smul_apply, smul_eq_mul] at hs
  refine hs.congr_fun fun n => ?_
  rw [expDeriv2_term_apply]

/-- The **second divided difference of the exponential**:
`e^{[2]}(x, y, z) = ∑ₙ (1/n!) ∑_{i<n} x^{n−1−i} ∑_{p<i} y^{i−1−p} zᵖ`. -/
noncomputable def expDividedDiff2 (x y z : ℂ) : ℂ :=
  ∑' n : ℕ, (n !⁻¹ : ℂ) * ∑ i ∈ range n, x ^ (n.pred - i) * ∑ p ∈ range i, y ^ (i.pred - p) * z ^ p

private theorem hasSum_termL (x y z : ℂ) :
    HasSum (fun n : ℕ => (n !⁻¹ : ℂ) * termL n x y z) (expDividedDiff2 x y z) := by
  refine Summable.hasSum ?_
  have hs := (hasSum_entry2 ![x, y, z] (Matrix.single 1 2 1) (Matrix.single 0 1 1) 0 2).summable
  simpa [Fin.sum_univ_three, Matrix.single_apply] using hs

/-- The same divided difference, from the other order of the factors. -/
private noncomputable def expDividedDiff2R (x y z : ℂ) : ℂ :=
  ∑' n : ℕ, (n !⁻¹ : ℂ) * termR n x y z

private theorem hasSum_termR (x y z : ℂ) :
    HasSum (fun n : ℕ => (n !⁻¹ : ℂ) * termR n x y z) (expDividedDiff2R x y z) := by
  refine Summable.hasSum ?_
  have hs := (hasSum_entry2 ![x, y, z] (Matrix.single 0 1 1) (Matrix.single 1 2 1) 0 2).summable
  simpa [Fin.sum_univ_three, Matrix.single_apply] using hs

private theorem expDeriv2_diagonal_apply' (a : d → ℂ) (k h : Matrix d d ℂ) (r c : d) :
    expDeriv2 ℂ (diagonal a) k h r c = ∑ l, (expDividedDiff2 (a r) (a l) (a c) * (h r l * k l c) +
      expDividedDiff2R (a r) (a l) (a c) * (k r l * h l c)) := by
  refine (hasSum_entry2 a k h r c).unique ?_
  refine (hasSum_sum fun l _ => ((hasSum_termL (a r) (a l) (a c)).mul_right (h r l * k l c)).add
    ((hasSum_termR (a r) (a l) (a c)).mul_right (k r l * h l c))).congr_fun fun n => ?_
  simp only [mul_sum]
  exact sum_congr rfl fun l _ => by ring

private theorem expDividedDiff2R_eq (x y z : ℂ) :
    expDividedDiff2R x y z = expDividedDiff2 x y z := by
  have h := congrFun (congrFun (expDeriv2_comm (𝕂 := ℂ) (diagonal ![x, y, z])
    (Matrix.single 1 2 1) (Matrix.single 0 1 1)) 0) 2
  rw [expDeriv2_diagonal_apply', expDeriv2_diagonal_apply'] at h
  simpa [Fin.sum_univ_three, Matrix.single_apply] using h.symm

/-- **The Daleckii–Krein formula for the second derivative of the exponential**: at `diag(a)`,
`(D² exp(diag a)[k, h])_{rc} = ∑_l e^{[2]}(a_r, a_l, a_c)(h_{rl} k_{lc} + k_{rl} h_{lc})`. -/
theorem expDeriv2_diagonal_apply (a : d → ℂ) (k h : Matrix d d ℂ) (r c : d) :
    expDeriv2 ℂ (diagonal a) k h r c =
      ∑ l, expDividedDiff2 (a r) (a l) (a c) * (h r l * k l c + k r l * h l c) := by
  rw [expDeriv2_diagonal_apply']
  simp only [expDividedDiff2R_eq, mul_add]

private theorem termL_mul_sub (n : ℕ) (x y z : ℂ) :
    termL n x y z * (y - z) = hterm n x y - hterm n x z := by
  rw [termL, sum_mul, hterm, hterm, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_assoc, hterm_mul_sub]
  ring

private theorem termR_mul_sub (n : ℕ) (x y z : ℂ) :
    termR n x y z * (x - y) = hterm n x z - hterm n y z := by
  rw [termR, sum_mul, hterm, hterm, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_right_comm, hterm_mul_sub]
  ring

/-- `e^{[2]}(x, y, z)(y − z) = e^{[1]}(x, y) − e^{[1]}(x, z)`. -/
theorem expDividedDiff2_mul_sub_right (x y z : ℂ) :
    expDividedDiff2 x y z * (y - z) = expDividedDiff x y - expDividedDiff x z := by
  refine ((hasSum_termL x y z).mul_right (y - z)).unique ?_
  refine ((hasSum_expDividedDiff x y).sub (hasSum_expDividedDiff x z)).congr_fun fun n => ?_
  rw [mul_assoc, termL_mul_sub, mul_sub]
  rfl

/-- `e^{[2]}(x, y, z)(x − y) = e^{[1]}(x, z) − e^{[1]}(y, z)`. -/
theorem expDividedDiff2_mul_sub_left (x y z : ℂ) :
    expDividedDiff2 x y z * (x - y) = expDividedDiff x z - expDividedDiff y z := by
  rw [← expDividedDiff2R_eq]
  refine ((hasSum_termR x y z).mul_right (x - y)).unique ?_
  refine ((hasSum_expDividedDiff x z).sub (hasSum_expDividedDiff y z)).congr_fun fun n => ?_
  rw [mul_assoc, termR_mul_sub, mul_sub]
  rfl

theorem expDividedDiff2_of_ne_right {x y z : ℂ} (h : y ≠ z) :
    expDividedDiff2 x y z = (expDividedDiff x y - expDividedDiff x z) / (y - z) :=
  eq_div_of_mul_eq (sub_ne_zero.mpr h) (expDividedDiff2_mul_sub_right x y z)

theorem expDividedDiff2_of_ne_left {x y z : ℂ} (h : x ≠ y) :
    expDividedDiff2 x y z = (expDividedDiff x z - expDividedDiff y z) / (x - y) :=
  eq_div_of_mul_eq (sub_ne_zero.mpr h) (expDividedDiff2_mul_sub_left x y z)

private theorem termL_self_mul_two (n : ℕ) (x : ℂ) :
    termL n x x x * 2 = n * ((n.pred : ℕ) * x ^ n.pred.pred) := by
  have hterm' : ∀ i ∈ range n, x ^ (n.pred - i) * hterm i x x = (i : ℂ) * x ^ n.pred.pred := by
    intro i hi
    rw [hterm_self]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp
    · rw [mul_left_comm, ← pow_add]
      congr 2
      have := mem_range.mp hi
      simp only [Nat.pred_eq_sub_one]
      omega
  have hs : (∑ i ∈ range n, (i : ℂ)) * 2 = n * (n.pred : ℕ) := by
    rw [Nat.pred_eq_sub_one, ← Nat.cast_sum]
    exact_mod_cast sum_range_id_mul_two n
  rw [termL, sum_congr rfl hterm', ← sum_mul, mul_right_comm, hs]
  ring

/-- `e^{[2]}(x, x, x) = eˣ / 2`. -/
theorem expDividedDiff2_self (x : ℂ) : expDividedDiff2 x x x = exp x / 2 := by
  have h1 := hasSum_factorial_mul_pred (g := fun m => x ^ m)
    ((exp_series_hasSum_exp' (𝕂 := ℂ) x).congr_fun fun m => smul_eq_mul _ _)
  have h2 := hasSum_factorial_mul_pred (g := fun m => (m : ℂ) * x ^ m.pred) h1
  refine eq_div_of_mul_eq two_ne_zero (((hasSum_termL x x x).mul_right 2).unique ?_)
  refine h2.congr_fun fun n => ?_
  rw [mul_assoc, termL_self_mul_two]
end Matrix

end AlphaCurvature
