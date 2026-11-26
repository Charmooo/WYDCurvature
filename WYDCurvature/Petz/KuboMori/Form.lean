/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import AlphaCurvature.ForMathlib.ParametricIntervalIntegral

/-!
# The BKM kernel and the BKM metric as a smooth field of bilinear forms

By Petz's classification, the monotone metrics on the density matrices correspond to the
operator monotone functions `f` with `f(1) = 1` and `f(t) = t f(1/t)`, through the
**Morozova–Chentsov function** `c(x, y) = 1 / (y f(x / y))`. The Kubo–Mori metric is the one with
`f(t) = (t − 1) / log t`, and its Morozova–Chentsov function is the **BKM kernel**
`bkm x y = (log x − log y)/(x − y)`, with value `1/x` on the diagonal (`PetzKernel.bkm`): the
reciprocal of the logarithmic mean, and the first divided difference of `log`. In an eigenbasis of
`ρ` the BKM metric is `(A, B) ↦ ∑ᵢⱼ bkm(λᵢ, λⱼ) Re(Aᵢⱼ Bⱼᵢ)` (`bkmForm_diagonal`, in
`KuboMori/Chart.lean`), which is `Re tr(A · D log(ρ)[B])` by the Daleckii–Krein formula.

Among the monotone metrics the Kubo–Mori metric is singled out by the identity
`(y − x) c(y, x) + (x − z) c(x, z) + (z − y) c(z, y) = 0`, which here reads
`(log y − log x) + (log x − log z) + (log z − log y) = 0`. It forces
`(y − x) c(y, x) = F(y) − F(x)`, and the normalization `c(x, x) = 1/x` forces `F = log`. It is
the reason the derivative of the metric is totally symmetric (Dittmann, the remark before his
(59)): the BKM metric is the Hessian of `ρ ↦ Tr ρ log ρ`, so its curvature is that of a Hessian
metric (`Curvature/Hessian.lean`).

The Bogoliubov–Kubo–Mori metric at a positive definite matrix `ρ` is
`(A, B) ↦ ∫₀^∞ Re tr(A (ρ + s)⁻¹ B (ρ + s)⁻¹) ds`. After the substitution `s ↦ s / (1 - s)` it
becomes an integral over `[0, 1]`: `bkmForm ρ A B = ∫₀¹ Re tr(A R B R) ds`,
`R = ((1 - s) ρ + s)⁻¹`. This file takes that form as the definition, as a field `ρ ↦ bkmForm ρ`
of real bilinear forms on all complex `d × d` matrices, and proves what the curvature theorems for
fields with a totally symmetric derivative (`Curvature/Hessian.lean`) ask of it: smoothness,
symmetry, and total symmetry of the derivative, near every positive definite matrix.

The integrand is smooth wherever the path `(1 - s) x + s` is invertible, and that holds near
`{ρ} × [0, 1]` for positive definite `ρ`, including at nearby non-Hermitian `x`; differentiation
under the integral sign over a compact interval does the rest
(`ForMathlib/ParametricIntervalIntegral.lean`).

## Main definitions

* `PetzCurvature.PetzKernel.bkm`: the BKM kernel.
* `PetzCurvature.sandwichForm R`: the real bilinear form `(A, B) ↦ Re tr(A R B R)`.
* `PetzCurvature.bkmPath`: the path `(1 - s) x + s`.
* `PetzCurvature.bkmForm`: the BKM form, `∫₀¹ sandwichForm ((1 - s) x + s)⁻¹ ds`.
* `PetzCurvature.tripleSandwich R Z A B = Re tr(A R Z R B R) + Re tr(A R B R Z R)`.

## Main statements

* `PetzCurvature.PetzKernel.bkm_pos`: the BKM kernel is positive at positive arguments.
* `PetzCurvature.contDiffAt_bkmForm`: the BKM form is `Cⁿ` at positive definite `ρ`.
* `PetzCurvature.fderiv_bkmForm_apply`: its derivative is
  `D bkmForm_x (Z) (A, B) = -∫₀¹ (1 - s) tripleSandwich R Z A B ds`.
* `PetzCurvature.eventually_bkmForm_comm`,
  `PetzCurvature.eventually_fderiv_bkmForm_comm`: near a positive definite matrix the form
  and its derivative are symmetric.

## References

* [D. Petz, *Monotone metrics on matrix spaces*][petz1996]
* [A. Lesniewski and M. B. Ruskai, *Monotone Riemannian metrics and relative entropy on
  noncommutative probability spaces*][lesniewski1999]
* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]
-/

open scoped Matrix.Norms.L2Operator Topology Interval ComplexOrder MatrixOrder
open Matrix ContinuousLinearMap Filter Set

namespace PetzCurvature

namespace PetzKernel

/-- The **BKM kernel**, the reciprocal logarithmic mean: `(log x − log y)/(x − y)`, and `1/x` on
the diagonal. -/
noncomputable def bkm (x y : ℝ) : ℝ := if x = y then x⁻¹ else (Real.log x - Real.log y) / (x - y)

/-- On the diagonal the BKM kernel is `1/x`, the normalization `c(x, x) = 1/x` of a
Morozova–Chentsov function. -/
theorem bkm_self (x : ℝ) : bkm x x = x⁻¹ := by simp [bkm]

/-- The BKM kernel is positive at positive arguments: `log` is increasing. -/
theorem bkm_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < bkm x y := by
  unfold bkm
  by_cases h : x = y
  · simp only [h, ↓reduceIte]
    positivity
  · simp only [h, ↓reduceIte]
    rcases lt_or_gt_of_ne h with hxy | hxy
    · exact div_pos_of_neg_of_neg (by linarith [Real.log_lt_log hx hxy]) (by linarith)
    · exact div_pos (by linarith [Real.log_lt_log hy hxy]) (by linarith)

end PetzKernel

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The **sandwich form** of a matrix `R`: the real bilinear form `(A, B) ↦ Re tr(A R B R)`. -/
noncomputable def sandwichForm (R : Matrix d d ℂ) : Matrix d d ℂ →L[ℝ] Matrix d d ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Matrix d d ℂ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun A B ↦ (A * R * B * R).trace.re)
        (fun A A' B ↦ by simp [Matrix.add_mul, Matrix.trace_add])
        (fun c A B ↦ by simp [Matrix.trace_smul])
        (fun A B B' ↦ by simp [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add])
        (fun c A B ↦ by simp [Matrix.trace_smul]))

@[simp]
theorem sandwichForm_apply (R A B : Matrix d d ℂ) :
    sandwichForm R A B = (A * R * B * R).trace.re := rfl

/-- The sandwich form is symmetric: `Re tr(A R B R) = Re tr(B R A R)`. -/
theorem sandwichForm_comm (R A B : Matrix d d ℂ) : sandwichForm R A B = sandwichForm R B A := by
  have h1 : A * R * B * R = (A * R) * (B * R) := by simp [Matrix.mul_assoc]
  have h2 : B * R * (A * R) = B * R * A * R := by simp [Matrix.mul_assoc]
  simp only [sandwichForm_apply]
  rw [h1, Matrix.trace_mul_comm, h2]

/-- `R ↦ sandwichForm R` is smooth. -/
theorem contDiff_sandwichForm {n : WithTop ℕ∞} :
    ContDiff ℝ n (sandwichForm : Matrix d d ℂ → _) := by
  refine contDiff_clm_apply_iff.2 fun A ↦ contDiff_clm_apply_iff.2 fun B ↦ ?_
  simp only [sandwichForm_apply]
  have h : ContDiff ℝ n fun X : Matrix d d ℂ ↦ X.trace.re :=
    (Complex.reCLM.comp (LinearMap.toContinuousLinearMap (traceLinearMap d ℝ ℂ))).contDiff
  exact h.comp (((contDiff_const.mul contDiff_id).mul contDiff_const).mul contDiff_id)

/-- The path `(1 - s) ρ + s` from `ρ` (at `s = 0`) to `1` (at `s = 1`). -/
noncomputable def bkmPath (z : Matrix d d ℂ × ℝ) : Matrix d d ℂ :=
  (1 - z.2) • z.1 + z.2 • (1 : Matrix d d ℂ)

/-- The integrand of the BKM form: `(ρ, s) ↦ sandwichForm ((1 - s) ρ + s)⁻¹`. -/
noncomputable def bkmIntegrand (z : Matrix d d ℂ × ℝ) :
    Matrix d d ℂ →L[ℝ] Matrix d d ℂ →L[ℝ] ℝ :=
  sandwichForm (bkmPath z)⁻¹

/-- The **BKM form** `bkmForm ρ A B = ∫₀¹ Re tr(A R B R) ds`, `R = ((1 - s) ρ + s)⁻¹`: the BKM
metric at `ρ` as a field of real bilinear forms on all complex matrices. -/
noncomputable def bkmForm (ρ : Matrix d d ℂ) : Matrix d d ℂ →L[ℝ] Matrix d d ℂ →L[ℝ] ℝ :=
  ∫ s in (0 : ℝ)..1, bkmIntegrand (ρ, s)

/-- The path `(1 - s) x + s` is smooth (it is affine in `x` for fixed `s`, and polynomial). -/
theorem contDiff_bkmPath {n : WithTop ℕ∞} : ContDiff ℝ n (bkmPath : Matrix d d ℂ × ℝ → _) :=
  ((contDiff_const.sub contDiff_snd).smul contDiff_fst).add (contDiff_snd.smul contDiff_const)

omit [Fintype d] in
/-- For positive definite `ρ` the path `(1 - s) ρ + s`, `s ∈ [0, 1]`, is positive definite. -/
theorem posDef_bkmPath {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (bkmPath (ρ, s)).PosDef := by
  rcases lt_or_eq_of_le hs.2 with h | rfl
  · exact (hρ.smul (sub_pos.2 h)).add_posSemidef (PosSemidef.one.smul hs.1)
  · simpa [bkmPath] using PosDef.one

/-- `bkmIntegrand` is smooth at every `(ρ, s)` where the path is invertible. -/
theorem contDiffAt_bkmIntegrand {n : WithTop ℕ∞} {z : Matrix d d ℂ × ℝ}
    (hz : IsUnit (bkmPath z)) : ContDiffAt ℝ n bkmIntegrand z := by
  have h : (bkmIntegrand : Matrix d d ℂ × ℝ → _) =
      fun z ↦ sandwichForm (Ring.inverse (bkmPath z)) :=
    funext fun z ↦ by rw [bkmIntegrand, nonsing_inv_eq_ringInverse]
  rw [h]
  exact (contDiff_sandwichForm (d := d)).contDiffAt.comp z
    ((contDiffAt_ringInverse ℝ hz.unit).comp z contDiff_bkmPath.contDiffAt)

/-- Invertibility of the whole path `(1 - s) x + s`, `s ∈ [0, 1]`, is an open condition on `x`. -/
theorem eventually_isUnit_bkmPath {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (x, t))) :
    ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (y, t)) :=
  isCompact_Icc.eventually_forall_of_forall_eventually fun t ht ↦
    (contDiff_bkmPath (n := 0)).continuous.continuousAt.eventually (Units.isOpen.mem_nhds (hx t ht))

/-- For positive definite `ρ` the whole path `(1 - s) ρ + s`, `s ∈ [0, 1]`, is invertible. -/
theorem isUnit_bkmPath_of_posDef {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) :
    ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (ρ, t)) :=
  fun _ ht ↦ (posDef_bkmPath hρ ht).isUnit

/-- Where the whole path is invertible, the integrand is smooth at every point of `{x} × [0, 1]`:
the hypothesis of differentiation under the integral sign. -/
theorem contDiffAt_bkmIntegrand_of_mem {n : WithTop ℕ∞} {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (x, t))) :
    ∀ t ∈ [[(0 : ℝ), 1]], ContDiffAt ℝ n bkmIntegrand (x, t) := fun t ht ↦
  contDiffAt_bkmIntegrand (hx t (by rwa [uIcc_of_le zero_le_one] at ht))

/-- **The BKM form is smooth** wherever the path `(1 - s) x + s` stays invertible: `Cⁿ` for every
`n`. -/
theorem contDiffAt_bkmForm_of_isUnit {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (x, t))) (n : ℕ) :
    ContDiffAt ℝ n bkmForm x :=
  contDiffAt_intervalIntegral_of_contDiffAt n (contDiffAt_bkmIntegrand_of_mem hx)

/-- **The BKM form is smooth** at a positive definite matrix: `Cⁿ` for every `n`. -/
theorem contDiffAt_bkmForm {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) (n : ℕ) :
    ContDiffAt ℝ n bkmForm ρ :=
  contDiffAt_bkmForm_of_isUnit (isUnit_bkmPath_of_posDef hρ) n

/-- The values of the BKM form are the integrals of the sandwich forms. -/
theorem bkmForm_apply {x : Matrix d d ℂ} (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (x, t)))
    (A B : Matrix d d ℂ) :
    bkmForm x A B = ∫ t in (0 : ℝ)..1, sandwichForm (bkmPath (x, t))⁻¹ A B := by
  have hc : ContinuousOn (fun t ↦ bkmIntegrand (x, t)) [[(0 : ℝ), 1]] := fun t ht ↦
    ((contDiffAt_bkmIntegrand_of_mem (n := 0) hx t ht).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  rw [bkmForm, ContinuousLinearMap.intervalIntegral_apply hc.intervalIntegrable,
    ContinuousLinearMap.intervalIntegral_apply
      (hc.clm_apply continuousOn_const).intervalIntegrable]
  rfl

/-- The BKM form is symmetric. -/
theorem bkmForm_comm {x : Matrix d d ℂ} (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (x, t)))
    (A B : Matrix d d ℂ) : bkmForm x A B = bkmForm x B A := by
  simp only [bkmForm_apply hx, sandwichForm_comm _ A B]

/-- The **triple sandwich** `Re tr(A R Z R B R) + Re tr(A R B R Z R)`: minus the derivative of the
sandwich form of `R = P⁻¹` along `P ↦ P + Z`. It is totally symmetric in `Z, A, B`
(`tripleSandwich_comm₁₂`, `tripleSandwich_comm₂₃`): its two terms are the two cyclic orders of
the three factors `A R`, `Z R`, `B R` under the trace, and every transposition of `Z, A, B`
exchanges them. -/
noncomputable def tripleSandwich (R Z A B : Matrix d d ℂ) : ℝ :=
  (A * R * Z * R * B * R).trace.re + (A * R * B * R * Z * R).trace.re

omit [DecidableEq d] in
/-- The triple sandwich is symmetric in `Z, A`: by cyclicity of the trace, each term of one side
is the other term of the other side. -/
theorem tripleSandwich_comm₁₂ (R Z A B : Matrix d d ℂ) :
    tripleSandwich R Z A B = tripleSandwich R A Z B := by
  have h1 : (Z * R * A * R * B * R).trace = (A * R * B * R * Z * R).trace := by
    rw [show Z * R * A * R * B * R = (Z * R) * (A * R * B * R) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : (Z * R * B * R * A * R).trace = (A * R * Z * R * B * R).trace := by
    rw [show Z * R * B * R * A * R = (Z * R * B * R) * (A * R) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [tripleSandwich, tripleSandwich, h1, h2, add_comm]

omit [DecidableEq d] in
/-- The triple sandwich is symmetric in `A, B`, by cyclicity of the trace. -/
theorem tripleSandwich_comm₂₃ (R Z A B : Matrix d d ℂ) :
    tripleSandwich R Z A B = tripleSandwich R Z B A := by
  have h1 : (B * R * Z * R * A * R).trace = (A * R * B * R * Z * R).trace := by
    rw [show B * R * Z * R * A * R = (B * R * Z * R) * (A * R) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : (B * R * A * R * Z * R).trace = (A * R * Z * R * B * R).trace := by
    rw [show B * R * A * R * Z * R = (B * R) * (A * R * Z * R) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [tripleSandwich, tripleSandwich, h1, h2, add_comm]

/-- The derivative of one slice of the integrand: along `Z`, the sandwich form of
`((1 - t) x + t)⁻¹` changes at the rate `-(1 - t)` times the triple sandwich. -/
theorem fderiv_bkmIntegrand_apply {x : Matrix d d ℂ} {t : ℝ} (hz : IsUnit (bkmPath (x, t)))
    (Z A B : Matrix d d ℂ) :
    fderiv ℝ (fun y ↦ bkmIntegrand (y, t) A B) x Z =
      -((1 - t) * tripleSandwich (bkmPath (x, t))⁻¹ Z A B) := by
  set R := (bkmPath (x, t))⁻¹ with hR
  have hRi : Ring.inverse (bkmPath (x, t)) = R := (nonsing_inv_eq_ringInverse _).symm
  have hF : (fun y ↦ bkmIntegrand (y, t) A B) =
      fun y ↦ (A * Ring.inverse (bkmPath (y, t)) * B * Ring.inverse (bkmPath (y, t))).trace.re :=
    funext fun y ↦ by simp [bkmIntegrand, nonsing_inv_eq_ringInverse]
  have hd : DifferentiableAt ℝ (fun y ↦ bkmIntegrand (y, t) A B) x :=
    ((((contDiffAt_bkmIntegrand (n := 1) hz).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).clm_apply contDiffAt_const).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  have h1 : HasDerivAt (fun ε : ℝ ↦ (fun y ↦ bkmIntegrand (y, t) A B) (x + ε • Z))
      (fderiv ℝ (fun y ↦ bkmIntegrand (y, t) A B) x Z) 0 :=
    hd.hasFDerivAt.hasLineDerivAt Z
  rw [hF] at h1
  have hP : HasDerivAt (fun ε : ℝ ↦ bkmPath (x + ε • Z, t)) ((1 - t) • Z) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).smul_const Z).const_add x).const_smul (1 - t)).add_const
      (t • (1 : Matrix d d ℂ))
    simpa [bkmPath] using this
  have hP0 : bkmPath (x + (0 : ℝ) • Z, t) = ↑hz.unit := by simp
  have hu : (↑hz.unit⁻¹ : Matrix d d ℂ) = R := by
    rw [hR, nonsing_inv_eq_ringInverse, ← Ring.inverse_unit, IsUnit.unit_spec]
  have hI : HasDerivAt (fun ε : ℝ ↦ Ring.inverse (bkmPath (x + ε • Z, t)))
      (-(R * ((1 - t) • Z) * R)) 0 := by
    have h := hasFDerivAt_ringInverse (𝕜 := ℝ) hz.unit
    rw [← hP0] at h
    refine (h.comp_hasDerivAt (0 : ℝ) hP).congr_deriv ?_
    simp only [_root_.neg_apply, mulLeftRight_apply, hu]
  have hI0 : Ring.inverse (bkmPath (x + (0 : ℝ) • Z, t)) = R := by simp [hRi]
  have hM := (((hasDerivAt_const (0 : ℝ) A).mul hI).mul (hasDerivAt_const (0 : ℝ) B)).mul hI
  have h2 := (Complex.reCLM.comp (LinearMap.toContinuousLinearMap
    (traceLinearMap d ℝ ℂ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hM
  rw [hF, h1.unique h2]
  simp only [hI0, Pi.mul_apply, zero_mul, zero_add, mul_zero, add_zero,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, tripleSandwich,
    Matrix.mul_assoc]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_toContinuousLinearMap', traceLinearMap_apply, Complex.reCLM_apply, trace_add,
    trace_neg, trace_smul, Complex.add_re, Complex.neg_re, Complex.smul_re, smul_eq_mul]
  ring

/-- **The derivative of the BKM form**:
`D bkmForm_x (Z) (A, B) = -∫₀¹ (1 - t) (Re tr(A R Z R B R) + Re tr(A R B R Z R)) dt`, with
`R = ((1 - t) x + t)⁻¹`. -/
theorem fderiv_bkmForm_apply {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (x, t))) (Z A B : Matrix d d ℂ) :
    fderiv ℝ bkmForm x Z A B =
      -∫ t in (0 : ℝ)..1, (1 - t) * tripleSandwich (bkmPath (x, t))⁻¹ Z A B := by
  have hdiff : DifferentiableAt ℝ bkmForm x :=
    (contDiffAt_bkmForm_of_isUnit hx 1).differentiableAt one_ne_zero
  have hdA : DifferentiableAt ℝ (fun y ↦ bkmForm y A) x :=
    hdiff.clm_apply (differentiableAt_const A)
  have e1 : fderiv ℝ (fun y ↦ bkmForm y A B) x Z = fderiv ℝ bkmForm x Z A B := by
    rw [fderiv_clm_apply hdA (differentiableAt_const B), fderiv_clm_apply hdiff
      (differentiableAt_const A)]
    simp
  have e2 : (fun y ↦ bkmForm y A B) =ᶠ[𝓝 x]
      fun y ↦ ∫ t in (0 : ℝ)..1, bkmIntegrand (y, t) A B := by
    filter_upwards [eventually_isUnit_bkmPath hx] with y hy
    exact bkmForm_apply hy A B
  have h3 := fderiv_intervalIntegral_apply_of_contDiffAt (a := 0) (b := 1)
    (f := fun z ↦ bkmIntegrand z A B) (x₀ := x) (fun t ht ↦
      ((contDiffAt_bkmIntegrand_of_mem hx t ht).clm_apply contDiffAt_const).clm_apply
        contDiffAt_const) Z
  rw [← e1, e2.fderiv_eq]
  refine h3.trans ?_
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  exact fderiv_bkmIntegrand_apply (hx t (by rwa [uIcc_of_le zero_le_one] at ht)) Z A B

/-- The derivative of the BKM form is symmetric in its first two arguments. -/
theorem fderiv_bkmForm_comm₁₂ {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (x, t))) (Z A B : Matrix d d ℂ) :
    fderiv ℝ bkmForm x Z A B = fderiv ℝ bkmForm x A Z B := by
  simp only [fderiv_bkmForm_apply hx, tripleSandwich_comm₁₂ _ Z A B]

/-- The derivative of the BKM form is symmetric in its last two arguments. -/
theorem fderiv_bkmForm_comm₂₃ {x : Matrix d d ℂ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (x, t))) (Z A B : Matrix d d ℂ) :
    fderiv ℝ bkmForm x Z A B = fderiv ℝ bkmForm x Z B A := by
  simp only [fderiv_bkmForm_apply hx, tripleSandwich_comm₂₃ _ Z A B]

/-- Near a positive definite matrix the BKM form is symmetric: the hypothesis `hGs` of the
curvature theorems for fields with totally symmetric derivative. -/
theorem eventually_bkmForm_comm {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) :
    ∀ᶠ x in 𝓝 ρ, ∀ A B, bkmForm x A B = bkmForm x B A := by
  filter_upwards [eventually_isUnit_bkmPath (isUnit_bkmPath_of_posDef hρ)] with x hx
  exact bkmForm_comm hx

/-- Near a positive definite matrix the derivative of the BKM form is symmetric in its first two
arguments (hence totally symmetric): the hypothesis `hT` of the curvature theorems. -/
theorem eventually_fderiv_bkmForm_comm {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) :
    ∀ᶠ x in 𝓝 ρ, ∀ Z A B, fderiv ℝ bkmForm x Z A B = fderiv ℝ bkmForm x A Z B := by
  filter_upwards [eventually_isUnit_bkmPath (isUnit_bkmPath_of_posDef hρ)] with x hx
  exact fderiv_bkmForm_comm₁₂ hx

/-- The sandwich form of a positive definite matrix is positive on nonzero Hermitian matrices:
`Re tr(A R A R) > 0`. With `S = √R` it is `tr(Mᴴ M)` for `M = S A S`. -/
theorem sandwichForm_self_pos {R A : Matrix d d ℂ} (hR : R.PosDef) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) : 0 < sandwichForm R A A := by
  set S := CFC.sqrt R
  have hSS : S * S = R := CFC.sqrt_mul_sqrt_self R (nonneg_iff_posSemidef.2 hR.posSemidef)
  have hSh : Sᴴ = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg R)).star_eq
  have hSu : IsUnit S := isUnit_of_mul_isUnit_left (hSS ▸ hR.isUnit)
  set M := S * A * S with hM
  have hMh : Mᴴ = M := by simp [hM, conjTranspose_mul, hA.eq, hSh, Matrix.mul_assoc]
  have htr : (A * (S * S) * A * (S * S)).trace = (Mᴴ * M).trace := by
    rw [hMh, hM, show A * (S * S) * A * (S * S) = (A * S * S * A * S) * S by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hM0 : M ≠ 0 := fun h ↦ hA0 <| (hSu.mul_right_eq_zero).1 <| hSu.mul_left_eq_zero.1 h
  have hnn : 0 ≤ (Mᴴ * M).trace := (posSemidef_conjTranspose_mul_self M).trace_nonneg
  have hne : (Mᴴ * M).trace ≠ 0 := fun h ↦ hM0 (trace_conjTranspose_mul_self_eq_zero_iff.1 h)
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.1 hnn
  rw [sandwichForm_apply, ← hSS, htr]
  exact lt_of_le_of_ne hre fun h ↦ hne (Complex.ext (by simp [← h]) (by simp [← him]))

/-- **The BKM form is positive definite on Hermitian matrices** at a positive definite `ρ`. -/
theorem bkmForm_self_pos {ρ A : Matrix d d ℂ} (hρ : ρ.PosDef) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) : 0 < bkmForm ρ A A := by
  have hx := isUnit_bkmPath_of_posDef hρ
  have hc : ContinuousOn (fun t ↦ bkmIntegrand (ρ, t) A A) [[(0 : ℝ), 1]] := fun t ht ↦
    ((((contDiffAt_bkmIntegrand_of_mem (n := 0) hx t ht).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).clm_apply continuousAt_const).clm_apply
        continuousAt_const).continuousWithinAt
  rw [bkmForm_apply hx]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on hc.intervalIntegrable
    (fun t ht ↦ sandwichForm_self_pos (posDef_bkmPath hρ (Ioo_subset_Icc_self ht)).inv hA hA0)
    zero_lt_one

end PetzCurvature
