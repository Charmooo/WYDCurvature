/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.ClosedForm

/-!
# The WYD scalar curvature at a diagonal state
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set
open AlphaCurvature AlphaCurvature.Curvature AlphaCurvature.Quantum

namespace WYD

variable {d : Type*} [Fintype d] [DecidableEq d] {β : ℝ} {l : d → ℝ}

/-! ### Linearity of `kerMat` in the kernel -/

omit [DecidableEq d] in
theorem kerMat_add_kernel (p q : d → d → d → ℝ) (X Y : Matrix d d ℂ) :
    kerMat p X Y + kerMat q X Y = kerMat (fun i k j ↦ p i k j + q i k j) X Y := by
  ext i j
  simp only [Matrix.add_apply, kerMat_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  push_cast; ring

omit [DecidableEq d] in
theorem kerMat_neg_kernel (q : d → d → d → ℝ) (X Y : Matrix d d ℂ) :
    -kerMat q X Y = kerMat (fun i k j ↦ -q i k j) X Y := by
  ext i j
  simp only [Matrix.neg_apply, kerMat_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  push_cast; ring

omit [DecidableEq d] in
theorem kerMat_smul_kernel (c : ℝ) (q : d → d → d → ℝ) (X Y : Matrix d d ℂ) :
    c • kerMat q X Y = kerMat (fun i k j ↦ c * q i k j) X Y := by
  ext i j
  simp only [Matrix.smul_apply, kerMat_apply, Complex.real_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  push_cast; ring

/-- The symmetric part of the two connections. -/
noncomputable def lγ (β : ℝ) (l : d → ℝ) (i k j : d) : ℝ :=
  (lq l β i k j + lq l (1 - β) i k j) / 2 - lq l 1 i k j

/-- The difference kernel of the two connections. -/
noncomputable def ln (β : ℝ) (l : d → ℝ) (i k j : d) : ℝ := lC β l i k j / lm β l i j

omit [Fintype d] [DecidableEq d] in
theorem ln_eq (i k j : d) : ln β l i k j = lq l β i k j - lq l (1 - β) i k j := by
  rw [ln, lC, lm, lq, lq, cubK, metK]
  have h1 := (e1_pos (β * Real.log (l i)) (β * Real.log (l j))).ne'
  have h2 := (e1_pos ((1 - β) * Real.log (l i)) ((1 - β) * Real.log (l j))).ne'
  generalize e1 (β * Real.log (l i)) (β * Real.log (l j)) = a at *
  generalize e1 ((1 - β) * Real.log (l i)) ((1 - β) * Real.log (l j)) = b at *
  field_simp

/-- `Γ(v, w)`. -/
noncomputable def lΓ (β : ℝ) (l : d → ℝ) (v w : tracelessHermitian d) : Matrix d d ℂ :=
  kerMat (lγ β l) (lX l v) (lX l w)

/-- `N(v, w)`. -/
noncomputable def lN (β : ℝ) (l : d → ℝ) (X Y : Matrix d d ℂ) : Matrix d d ℂ :=
  kerMat (fun i k j ↦ lC β l i k j / lm β l i j) X Y

theorem split_left (hl : ∀ i, 0 < l i) (v w : tracelessHermitian d) :
    kerMat (lq l β) (lX l v) (lX l w) + lXX l v w =
      lΓ β l v w + (2⁻¹ : ℝ) • lN β l (lX l v) (lX l w) := by
  rw [lXX_eq hl, kerMat_neg_kernel, kerMat_add_kernel, lΓ, lN, kerMat_smul_kernel,
    kerMat_add_kernel]
  congr 1
  funext i k j
  have := ln_eq (β := β) (l := l) i k j
  rw [ln] at this
  rw [this, lγ]
  ring

theorem split_right (hl : ∀ i, 0 < l i) (v w : tracelessHermitian d) :
    kerMat (lq l (1 - β)) (lX l v) (lX l w) + lXX l v w =
      lΓ β l v w - (2⁻¹ : ℝ) • lN β l (lX l v) (lX l w) := by
  rw [lXX_eq hl, kerMat_neg_kernel, kerMat_add_kernel, lΓ, lN, kerMat_smul_kernel,
    sub_eq_add_neg (kerMat _ _ _), kerMat_neg_kernel, kerMat_add_kernel]
  congr 1
  funext i k j
  have := ln_eq (β := β) (l := l) i k j
  rw [ln] at this
  rw [this, lγ]
  ring

theorem lΓ_isHermitian (hl : ∀ i, 0 < l i) (v w : tracelessHermitian d) :
    (lΓ β l v w).IsHermitian :=
  kerMat_isHermitian (fun i k j ↦ by simp only [lγ, lq_comm _ i k j]) (lX_isHermitian hl v)
    (lX_isHermitian hl w)

/-! ### The unit normal -/

theorem mform_one (hl : ∀ i, 0 < l i) (Y : Matrix d d ℂ) :
    mform (lm β l) Y 1 = ∑ i, l i * (Y i i).re := by
  rw [mform_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single i]
  · rw [lm_self hl, Matrix.one_apply_eq, mul_one]
  · intro j _ hj
    rw [Matrix.one_apply_ne hj]; simp
  · simp

theorem mform_lX_one (hl : ∀ i, 0 < l i) (w : tracelessHermitian d) :
    mform (lm β l) (lX l w) 1 = 0 := by
  rw [mform_one hl]
  have h : ∀ i, l i * (lX l w i i).re = ((w : Matrix d d ℂ) i i).re := fun i ↦ by
    rw [← e1_mul_lX hl w i i, Complex.re_ofReal_mul, e1_self, Real.exp_log (hl i)]
  simp only [h, ← Complex.re_sum]
  have := (mem_tracelessHermitian.1 w.2).2
  rw [Matrix.trace] at this
  simp only [Matrix.diag_apply] at this
  rw [this, Complex.zero_re]

theorem mform_one_one (hl : ∀ i, 0 < l i) (htr : ∑ i, l i = 1) :
    mform (lm β l) (1 : Matrix d d ℂ) 1 = 1 := by
  rw [mform_one hl]
  simp [htr]

/-- The kernel identity behind the second fundamental form of the unit normal. -/
theorem kernel_normal (s x y : ℝ) :
    Real.exp x * (s * e2 (s * x) (s * y) (s * x) / e1 (s * x) (s * x)) +
      Real.exp y * (s * e2 (s * y) (s * x) (s * y) / e1 (s * y) (s * y)) =
        e1 x y - (1 - s) * (e1 (s * x) (s * y) * e1 ((1 - s) * x) ((1 - s) * y)) := by
  have hx : Real.exp x = Real.exp (s * x) * Real.exp ((1 - s) * x) := by
    rw [← Real.exp_add]; congr 1; ring
  have hy : Real.exp y = Real.exp (s * y) * Real.exp ((1 - s) * y) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1_self, e1_self]
  have e0 := Real.exp_pos (s * x); have e0' := Real.exp_pos (s * y)
  rcases eq_or_ne x y with rfl | hxy
  · rw [e2_self, e1_self, e1_self, e1_self, hx]
    field_simp
    ring
  have hxy' := sub_ne_zero.2 hxy
  apply mul_right_cancel₀ hxy'
  have a1 : s * e2 (s * x) (s * y) (s * x) * (x - y) = Real.exp (s * x) - e1 (s * x) (s * y) := by
    have := e2_self_mul_sub (s * x) (s * y)
    rw [e2_comm₂₃] at this
    linear_combination this
  have a2 : s * e2 (s * y) (s * x) (s * y) * (y - x) = Real.exp (s * y) - e1 (s * x) (s * y) := by
    have := e2_self_mul_sub (s * y) (s * x)
    rw [e2_comm₂₃, e1_comm] at this
    linear_combination this
  have a3 := e1_mul_sub x y
  have a4 := e1_mul_sub ((1 - s) * x) ((1 - s) * y)
  have b1 : Real.exp x * (s * e2 (s * x) (s * y) (s * x) / Real.exp (s * x)) * (x - y) =
      Real.exp ((1 - s) * x) * (Real.exp (s * x) - e1 (s * x) (s * y)) := by
    rw [← a1, hx]; field_simp
  have b2 : Real.exp y * (s * e2 (s * y) (s * x) (s * y) / Real.exp (s * y)) * (y - x) =
      Real.exp ((1 - s) * y) * (Real.exp (s * y) - e1 (s * x) (s * y)) := by
    rw [← a2, hy]; field_simp
  rw [hx, hy] at a3
  linear_combination b1 - b2 - a3 + e1 (s * x) (s * y) * a4

/-- **The second fundamental form of the unit normal**: `⟨Γ(v, w), 1⟩ = -½ G(v, w)`. -/
theorem mform_lΓ_one (hl : ∀ i, 0 < l i) (v w : tracelessHermitian d) :
    mform (lm β l) (lΓ β l v w) 1 = -(mform (lm β l) (lX l v) (lX l w)) / 2 := by
  rw [mform_one hl]
  set Z : d → d → ℝ := fun i k ↦ (lX l v i k * lX l w k i + lX l w i k * lX l v k i).re with hZ
  have hZs : ∀ i k, Z i k = Z k i := fun i k ↦ by
    simp only [hZ]; congr 1; ring
  have h1 : ∑ i, l i * (lΓ β l v w i i).re = ∑ i, ∑ k, l i * lγ β l i k i * Z i k := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [lΓ, kerMat_apply, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Complex.re_ofReal_mul, mul_assoc]
  have h2 : ∀ i k, l i * lγ β l i k i + l k * lγ β l k i k = -(lm β l i k) / 2 := by
    intro i k
    have k1 := kernel_normal β (Real.log (l i)) (Real.log (l k))
    have k2 := kernel_normal (1 - β) (Real.log (l i)) (Real.log (l k))
    have k3 := kernel_normal 1 (Real.log (l i)) (Real.log (l k))
    rw [Real.exp_log (hl i), Real.exp_log (hl k)] at k1 k2 k3
    rw [show (1 : ℝ) - (1 - β) = β by ring] at k2
    rw [lγ, lγ, lm, metK]
    simp only [lq]
    linear_combination k1 / 2 + k2 / 2 - k3
  have h3 : 2 * ∑ i, ∑ k, l i * lγ β l i k i * Z i k =
      ∑ i, ∑ k, -(lm β l i k) / 2 * Z i k := by
    rw [two_mul]
    nth_rw 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hZs k i, ← add_mul, h2]
  have h4 : ∑ i, ∑ k, -(lm β l i k) / 2 * Z i k = -mform (lm β l) (lX l v) (lX l w) := by
    have e1 : mform (lm β l) (lX l v) (lX l w) = ∑ i, ∑ k, lm β l i k / 2 * Z i k := by
      have e2 := mform_comm (lm_comm (β := β) (l := l)) (lX l v) (lX l w)
      have e3 : mform (lm β l) (lX l v) (lX l w) = (mform (lm β l) (lX l v) (lX l w) +
        mform (lm β l) (lX l w) (lX l v)) / 2 := by rw [← e2]; ring
      rw [e3, mform_apply, mform_apply, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← mul_add, ← Complex.add_re]
      ring
    rw [e1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [h1]
  linarith

/-- The unit normal in the cubic form: `N(1, Y) = (2β - 1) Y`. -/
theorem lN_one (Y : Matrix d d ℂ) : lN β l 1 Y = (2 * β - 1) • Y := by
  ext i j
  rw [lN, kerMat_apply, Matrix.smul_apply, Complex.real_smul]
  have h : ∀ k, ((lC β l i k j / lm β l i j : ℝ) : ℂ) *
      ((1 : Matrix d d ℂ) i k * Y k j + Y i k * (1 : Matrix d d ℂ) k j) =
      (if i = k then ((lC β l i i j / lm β l i j : ℝ) : ℂ) * Y i j else 0) +
        if k = j then ((lC β l i j j / lm β l i j : ℝ) : ℂ) * Y i j else 0 := fun k ↦ by
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases h1 : i = k
    · subst h1
      by_cases h2 : i = j
      · subst h2; simp; ring
      · simp [h2]
    · by_cases h2 : k = j
      · subst h2; simp [h1]
      · simp [h1, h2]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  rw [← add_mul, ← Complex.ofReal_add, ← add_div]
  congr 2
  rw [div_eq_iff (lm_pos i j).ne', lC, lC, lm]
  exact cubK_add _ _

end WYD
