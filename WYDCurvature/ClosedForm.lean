/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Metric
import WYDCurvature.Frame
import WYDCurvature.Contract

/-!
# The closed form of the WYD scalar curvature

At a diagonal state `diag(l)` the scalar curvature of the WYD metric is
`∑ᵢⱼₖ hs_β(lᵢ, lⱼ, lₖ) - ∑ᵢ hs_β(lᵢ, lᵢ, lᵢ) + (n² - 1)(n² - 2)/4`
(`scalarCurvature_wydMetric_diagonal`).
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set
open AlphaCurvature AlphaCurvature.Curvature AlphaCurvature.Quantum

namespace WYD

variable {d : Type*} [Fintype d] [DecidableEq d] {β : ℝ} {l : d → ℝ}

/-- The diagonal state. -/
noncomputable abbrev diagS (l : d → ℝ) : Matrix d d ℂ := Matrix.diagonal fun i ↦ (l i : ℂ)

/-- The tangent vector `w` in logarithmic coordinates. -/
noncomputable def lX (l : d → ℝ) (w : tracelessHermitian d) : Matrix d d ℂ :=
  fderiv ℝ (logChart (tracelessHermitian d) (diagS l)) 0 w

/-- The second derivative of the logarithm. -/
noncomputable def lXX (l : d → ℝ) (v w : tracelessHermitian d) : Matrix d d ℂ :=
  fderiv ℝ (fderiv ℝ (logChart (tracelessHermitian d) (diagS l))) 0 v w

/-- Entrywise multiplication by the divided differences of `e^{s·}` at the logarithms. -/
noncomputable def lA (l : d → ℝ) (s : ℝ) (Y : Matrix d d ℂ) : Matrix d d ℂ :=
  Matrix.of fun i j ↦ ((s * e1 (s * Real.log (l i)) (s * Real.log (l j)) : ℝ) : ℂ) * Y i j

/-- The kernel of the second derivative. -/
noncomputable def lq (l : d → ℝ) (s : ℝ) (i k j : d) : ℝ :=
  s * e2 (s * Real.log (l i)) (s * Real.log (l k)) (s * Real.log (l j)) /
    e1 (s * Real.log (l i)) (s * Real.log (l j))

/-- The metric weights. -/
noncomputable def lm (β : ℝ) (l : d → ℝ) (i j : d) : ℝ := metK β (Real.log (l i)) (Real.log (l j))

/-- The cubic coefficients. -/
noncomputable def lC (β : ℝ) (l : d → ℝ) (i j k : d) : ℝ :=
  cubK β (Real.log (l i)) (Real.log (l j)) (Real.log (l k))

omit [Fintype d] [DecidableEq d] in
theorem lm_comm (i j : d) : lm β l i j = lm β l j i := metK_comm _ _

omit [Fintype d] [DecidableEq d] in
theorem lm_pos (i j : d) : 0 < lm β l i j := metK_pos _ _

omit [Fintype d] [DecidableEq d] in
theorem lm_self (hl : ∀ i, 0 < l i) (i : d) : lm β l i i = l i := by
  rw [lm, metK_self, Real.exp_log (hl i)]

omit [Fintype d] [DecidableEq d] in
theorem lC_comm₁₂ (i j k : d) : lC β l j i k = lC β l i j k := cubK_comm₁₂ _ _ _

omit [Fintype d] [DecidableEq d] in
theorem lC_comm₂₃ (i j k : d) : lC β l i k j = lC β l i j k := cubK_comm₂₃ _ _ _

omit [Fintype d] [DecidableEq d] in
theorem lq_comm (s : ℝ) (i k j : d) : lq l s i k j = lq l s j k i := by
  rw [lq, lq, e1_comm, e2_comm₁₂, e2_comm₂₃, e2_comm₁₂]

theorem expDeriv_diag (hl : ∀ i, 0 < l i) (s : ℝ) (Y : Matrix d d ℂ) (i j : d) :
    expDeriv ℝ (s • matLog (diagS l)) Y i j =
      (e1 (s * Real.log (l i)) (s * Real.log (l j)) : ℂ) * Y i j := by
  rw [smul_matLog_diagonal s hl, expDeriv_real_eq, Matrix.expDeriv_diagonal_apply,
    expDividedDiff_eq]

theorem expDeriv2_diag (hl : ∀ i, 0 < l i) (s : ℝ) (Y Z : Matrix d d ℂ) (i j : d) :
    expDeriv2 ℝ (s • matLog (diagS l)) Y Z i j = ∑ k, (e2 (s * Real.log (l i))
      (s * Real.log (l k)) (s * Real.log (l j)) : ℂ) * (Z i k * Y k j + Y i k * Z k j) := by
  rw [smul_matLog_diagonal s hl, expDeriv2_real_eq, Matrix.expDeriv2_diagonal_apply]
  simp only [expDividedDiff2_eq]

/-- The first derivative of a power in the chart. -/
theorem fderiv_powChart_diag (hl : ∀ i, 0 < l i) (s : ℝ) (w : tracelessHermitian d) :
    fderiv ℝ (fun z : tracelessHermitian d ↦
      matPow s ((tracelessHermitian d).subtypeL z + diagS l)) 0 w = lA l s (lX l w) := by
  rw [fderiv_powChart s (posDef_diagonal_ofReal hl)]
  ext i j
  rw [expDeriv_diag hl, lA, Matrix.of_apply, Matrix.smul_apply, Complex.real_smul, lX]
  push_cast
  ring

/-- The second derivative of a power in the chart. -/
theorem fderiv_fderiv_powChart_diag (hl : ∀ i, 0 < l i) (s : ℝ) (v w : tracelessHermitian d) :
    fderiv ℝ (fderiv ℝ (fun z : tracelessHermitian d ↦
      matPow s ((tracelessHermitian d).subtypeL z + diagS l))) 0 v w =
        lA l s (kerMat (lq l s) (lX l v) (lX l w) + lXX l v w) := by
  rw [fderiv_fderiv_powChart s (posDef_diagonal_ofReal hl)]
  ext i j
  have he : (e1 (s * Real.log (l i)) (s * Real.log (l j)) : ℂ) ≠ 0 := by
    exact_mod_cast (e1_pos _ _).ne'
  rw [Matrix.add_apply, expDeriv_diag hl, expDeriv2_diag hl, lA, Matrix.of_apply,
    Matrix.add_apply, mul_add, kerMat_apply, Finset.mul_sum, ← lX, ← lX, ← lXX]
  congr 1
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Matrix.smul_apply, Complex.real_smul, lq]
    push_cast
    field_simp
    ring
  · rw [Matrix.smul_apply, Complex.real_smul]
    push_cast
    ring

theorem matPow_one {x : Matrix d d ℂ} (hx : x.PosDef) : matPow 1 x = x := by
  obtain ⟨U, hU, l, hl, rfl⟩ := exists_unitary_diagonal_of_posDef hx
  rw [matPow_conj 1 hU, matPow_diagonal 1 hl]
  simp

theorem powChart_one_eventuallyEq (hl : ∀ i, 0 < l i) :
    (fun z : tracelessHermitian d ↦ matPow 1 ((tracelessHermitian d).subtypeL z + diagS l))
      =ᶠ[𝓝 0] fun z ↦ (tracelessHermitian d).subtypeL z + diagS l :=
  (eventually_posDef_chart (posDef_diagonal_ofReal hl)
    fun _ hv ↦ (mem_tracelessHermitian.1 hv).1).mono fun _ hz ↦ matPow_one hz

/-- **The logarithmic coordinates**: `e1(hᵢ, hⱼ) Xᵢⱼ = wᵢⱼ`. -/
theorem e1_mul_lX (hl : ∀ i, 0 < l i) (w : tracelessHermitian d) (i j : d) :
    (e1 (Real.log (l i)) (Real.log (l j)) : ℂ) * lX l w i j = (w : Matrix d d ℂ) i j := by
  have h1 := fderiv_powChart_diag hl 1 w
  rw [(powChart_one_eventuallyEq hl).fderiv_eq, (hasFDerivAt_chart (0 : tracelessHermitian d)).fderiv] at h1
  have h2 := congrFun (congrFun h1 i) j
  rw [lA, Matrix.of_apply] at h2
  simp only [one_mul] at h2
  exact h2.symm

theorem lXX_eq (hl : ∀ i, 0 < l i) (v w : tracelessHermitian d) :
    lXX l v w = -kerMat (lq l 1) (lX l v) (lX l w) := by
  have h1 := fderiv_fderiv_powChart_diag hl 1 v w
  have h0 : fderiv ℝ (fderiv ℝ (fun z : tracelessHermitian d ↦
      matPow 1 ((tracelessHermitian d).subtypeL z + diagS l))) 0 v w = 0 := by
    rw [(powChart_one_eventuallyEq hl).fderiv.fderiv_eq]
    have : fderiv ℝ (fun z : tracelessHermitian d ↦ (tracelessHermitian d).subtypeL z + diagS l) =
        fun _ ↦ (tracelessHermitian d).subtypeL :=
      funext fun z ↦ (hasFDerivAt_chart z).fderiv
    rw [this]
    simp
  rw [h0] at h1
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  rw [lA, Matrix.of_apply, Matrix.add_apply] at h2
  have he : ((1 * e1 (1 * Real.log (l i)) (1 * Real.log (l j)) : ℝ) : ℂ) ≠ 0 := by
    rw [one_mul]
    exact_mod_cast (e1_pos _ _).ne'
  rw [Matrix.neg_apply]
  rcases mul_eq_zero.1 h2.symm with h | h
  · exact absurd h he
  · linear_combination h

/-- `lX` is Hermitian. -/
theorem lX_isHermitian (hl : ∀ i, 0 < l i) (w : tracelessHermitian d) : (lX l w).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j ↦ ?_
  have he : (e1 (Real.log (l i)) (Real.log (l j)) : ℂ) ≠ 0 := by
    exact_mod_cast (e1_pos _ _).ne'
  apply mul_left_cancel₀ he
  have hw := (mem_tracelessHermitian.1 w.2).1
  rw [e1_mul_lX hl, ← hw.apply i j, ← e1_mul_lX hl w j i, star_mul', e1_comm]
  simp [Complex.conj_ofReal]

/-! ### The pairing in logarithmic coordinates -/

theorem hsForm_lA (β : ℝ) (Y Z : Matrix d d ℂ) :
    hsForm (lA l β Y) (lA l (1 - β) Z) = β * (1 - β) * mform (lm β l) Y Z := by
  rw [hsForm_apply, Matrix.trace, Complex.re_sum, mform_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [lA, lA, Matrix.of_apply, Matrix.of_apply, mul_mul_mul_comm, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul, lm, metK, e1_comm ((1 - β) * Real.log (l j))]
  ring

theorem wydPairing_lA (h0 : β ≠ 0) (h1 : β ≠ 1) (Y Y' Z Z' : Matrix d d ℂ) :
    wydPairing β (lA l β Y, lA l (1 - β) Y') (lA l β Z, lA l (1 - β) Z') =
      (mform (lm β l) Y Z' + mform (lm β l) Z Y') / 2 := by
  have h1' : 1 - β ≠ 0 := sub_ne_zero.2 h1.symm
  rw [wydPairing_apply, hsForm_lA, hsForm_lA]
  field_simp

theorem fderiv_wydChart_diag (hl : ∀ i, 0 < l i) (w : tracelessHermitian d) :
    fderiv ℝ (wydChart β (tracelessHermitian d) (diagS l)) 0 w =
      (lA l β (lX l w), lA l (1 - β) (lX l w)) := by
  have hD := posDef_diagonal_ofReal hl
  have h := (((contDiffAt_powChart (V := tracelessHermitian d) β hD 1).differentiableAt
    one_ne_zero).hasFDerivAt.prodMk ((contDiffAt_powChart (V := tracelessHermitian d)
      (1 - β) hD 1).differentiableAt one_ne_zero).hasFDerivAt)
  have h' : HasFDerivAt (wydChart β (tracelessHermitian d) (diagS l)) _ 0 := h
  rw [h'.fderiv, ContinuousLinearMap.prod_apply, fderiv_powChart_diag hl, fderiv_powChart_diag hl]

theorem fderiv_fderiv_wydChart_diag (hl : ∀ i, 0 < l i) (v w : tracelessHermitian d) :
    fderiv ℝ (fderiv ℝ (wydChart β (tracelessHermitian d) (diagS l))) 0 v w =
      (lA l β (kerMat (lq l β) (lX l v) (lX l w) + lXX l v w),
        lA l (1 - β) (kerMat (lq l (1 - β)) (lX l v) (lX l w) + lXX l v w)) := by
  have hD := posDef_diagonal_ofReal hl
  have c1 := contDiffAt_powChart (V := tracelessHermitian d) β hD 2
  have c2 := contDiffAt_powChart (V := tracelessHermitian d) (1 - β) hD 2
  have hev : fderiv ℝ (wydChart β (tracelessHermitian d) (diagS l)) =ᶠ[𝓝 0] fun z ↦
      (fderiv ℝ (fun z : tracelessHermitian d ↦
        matPow β ((tracelessHermitian d).subtypeL z + diagS l)) z).prod
      (fderiv ℝ (fun z : tracelessHermitian d ↦
        matPow (1 - β) ((tracelessHermitian d).subtypeL z + diagS l)) z) := by
    filter_upwards [c1.eventually (by simp), c2.eventually (by simp)] with z h1 h2
    exact ((h1.differentiableAt (by simp)).hasFDerivAt.prodMk
      (h2.differentiableAt (by simp)).hasFDerivAt).fderiv
  have d1 := ((c1.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  have d2 := ((c2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  have dw : ∀ {f : tracelessHermitian d → tracelessHermitian d →L[ℝ] Matrix d d ℂ},
      DifferentiableAt ℝ f 0 → HasFDerivAt (fun z ↦ f z w) ((fderiv ℝ f 0).flip w) 0 :=
    fun hf ↦ by simpa using hf.hasFDerivAt.clm_apply (hasFDerivAt_const w 0)
  have c3 := contDiffAt_wydChart (β := β) (V := tracelessHermitian d) hD 2
  have d3 := ((c3.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  have h3 : HasFDerivAt (fun z ↦ fderiv ℝ (wydChart β (tracelessHermitian d) (diagS l)) z w)
      ((fderiv ℝ (fderiv ℝ (wydChart β (tracelessHermitian d) (diagS l))) 0).flip w) 0 := by
    simpa using d3.hasFDerivAt.clm_apply (hasFDerivAt_const w 0)
  have h4 := ((dw d1).prodMk (dw d2)).congr_of_eventuallyEq
    (hev.mono fun z hz ↦ by simpa using congrArg (fun L ↦ L w) hz)
  have h5 := congrArg (fun L ↦ L v) (h3.unique h4)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.prod_apply] at h5
  rw [h5, fderiv_fderiv_powChart_diag hl, fderiv_fderiv_powChart_diag hl]

end WYD
