/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.Curvature.Gauss
import AlphaCurvature.Quantum.Hypersurface
import AlphaCurvature.Quantum.ClosedForm
import WYDCurvature.Exp2
import WYDCurvature.Kernel

/-!
# The WYD metric

The **Wigner–Yanase–Dyson metric** `g^β(u, w) = Re tr (D(ρ^β)[u] D(ρ^{1-β})[w]) / (β(1-β))` is the
pullback of the constant symmetric pairing `wydPairing β` on pairs of matrices by the embedding
`ρ ↦ (ρ^β, ρ^{1-β})`, in the affine chart `z ↦ ρ₀ + z` of the states. This file has the metric
(`wydMetric`, `wydMetric_apply`) and the first and second derivatives of the embedding at a
diagonal state, in the logarithmic coordinates `X = D log ρ [u]`.
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set
open AlphaCurvature AlphaCurvature.Curvature AlphaCurvature.Quantum

namespace WYD

/-! ### The real kernels -/

theorem expDividedDiff_eq (x y : ℝ) :
    AlphaCurvature.Matrix.expDividedDiff (x : ℂ) y = (e1 x y : ℂ) := by
  rcases eq_or_ne x y with rfl | h
  · rw [AlphaCurvature.Matrix.expDividedDiff_self, e1_self, ← Complex.exp_eq_exp_ℂ,
      Complex.ofReal_exp]
  · rw [AlphaCurvature.Matrix.expDividedDiff_of_ne (by exact_mod_cast h), e1_of_ne h]
    simp only [← Complex.exp_eq_exp_ℂ]
    push_cast
    rfl

theorem expDividedDiff2_eq (x y z : ℝ) :
    AlphaCurvature.Matrix.expDividedDiff2 (x : ℂ) y z = (e2 x y z : ℂ) := by
  rcases eq_or_ne y z with rfl | h
  · rcases eq_or_ne x y with rfl | h
    · rw [AlphaCurvature.Matrix.expDividedDiff2_self, e2_self, ← Complex.exp_eq_exp_ℂ]
      push_cast
      rfl
    · have hc : (x : ℂ) - y ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
      apply mul_right_cancel₀ hc
      rw [AlphaCurvature.Matrix.expDividedDiff2_mul_sub_left, expDividedDiff_eq, expDividedDiff_eq]
      exact_mod_cast (e2_mul_sub x y y).symm
  · have hc : (y : ℂ) - z ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
    apply mul_right_cancel₀ hc
    rw [AlphaCurvature.Matrix.expDividedDiff2_mul_sub_right, expDividedDiff_eq, expDividedDiff_eq]
    exact_mod_cast (e2_mul_sub_right x y z).symm

/-! ### Real and complex derivatives of the exponential -/

section RealComplex

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
  [IsScalarTower ℝ ℂ 𝔸]

omit [CompleteSpace 𝔸] in
theorem inv_factorial_smul (n : ℕ) (M : 𝔸) :
    ((n.factorial : ℝ)⁻¹) • M = ((n.factorial : ℂ)⁻¹) • M := by
  have := smul_assoc ((n.factorial : ℝ)⁻¹) (1 : ℂ) M
  rw [one_smul, Complex.real_smul, mul_one] at this
  rw [← this]
  push_cast
  rfl

theorem expDeriv_real_eq (x h : 𝔸) : expDeriv ℝ x h = expDeriv ℂ x h := by
  refine (hasSum_expDeriv (𝕂 := ℝ) x h).unique ?_
  simpa only [inv_factorial_smul] using hasSum_expDeriv (𝕂 := ℂ) x h

theorem expDeriv2_real_eq (x k h : 𝔸) : expDeriv2 ℝ x k h = expDeriv2 ℂ x k h := by
  refine (hasSum_expDeriv2 (𝕂 := ℝ) x k h).unique ?_
  have := hasSum_expDeriv2 (𝕂 := ℂ) x k h
  simpa only [inv_factorial_smul, powDeriv_apply] using this

end RealComplex

/-! ### The derivatives of `exp ∘ Λ` -/

section Chain

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {L : E → 𝔸} {x : E}

theorem fderiv_exp_comp (hL : DifferentiableAt ℝ L x) (w : E) :
    fderiv ℝ (fun y ↦ NormedSpace.exp (L y)) x w = expDeriv ℝ (L x) (fderiv ℝ L x w) := by
  have h := (hasFDerivAt_exp' (𝕂 := ℝ) (L x)).comp x hL.hasFDerivAt
  have h' : HasFDerivAt (fun y ↦ NormedSpace.exp (L y))
      ((expDeriv ℝ (L x)).comp (fderiv ℝ L x)) x := h
  rw [h'.fderiv]
  rfl

theorem fderiv_fderiv_exp_comp (hL : ContDiffAt ℝ 2 L x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ NormedSpace.exp (L y))) x v w =
      expDeriv2 ℝ (L x) (fderiv ℝ L x v) (fderiv ℝ L x w) +
        expDeriv ℝ (L x) (fderiv ℝ (fderiv ℝ L) x v w) := by
  have hL1 : DifferentiableAt ℝ L x := hL.differentiableAt (by simp)
  have hL2 : DifferentiableAt ℝ (fderiv ℝ L) x :=
    (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ L y :=
    (hL.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hf : fderiv ℝ (fun y ↦ NormedSpace.exp (L y)) =ᶠ[𝓝 x]
      fun y ↦ (expDeriv ℝ (L y)).comp (fderiv ℝ L y) := hev.mono fun y hy ↦ by
    ext w
    rw [fderiv_exp_comp hy]
    rfl
  have h1 : HasFDerivAt (fun y ↦ expDeriv ℝ (L y))
      ((expDeriv2 ℝ (L x)).comp (fderiv ℝ L x)) x :=
    (hasFDerivAt_expDeriv (𝕂 := ℝ) (L x)).comp x hL1.hasFDerivAt
  have h2 := h1.clm_comp hL2.hasFDerivAt
  rw [hf.fderiv_eq, h2.fderiv]
  simp [add_comm]

end Chain

/-! ### The metric -/

section Metric

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The constant pairing `((A, C), (A', C')) ↦ Re tr (A C' + A' C) / (2 β (1 - β))`. -/
noncomputable def wydPairing (β : ℝ) :
    (Matrix d d ℂ × Matrix d d ℂ) →L[ℝ] (Matrix d d ℂ × Matrix d d ℂ) →L[ℝ] ℝ :=
  (2 * (β * (1 - β)))⁻¹ • ((hsForm (d := d)).bilinearComp
    (ContinuousLinearMap.fst ℝ (Matrix d d ℂ) (Matrix d d ℂ))
    (ContinuousLinearMap.snd ℝ (Matrix d d ℂ) (Matrix d d ℂ)) + ((hsForm (d := d)).bilinearComp
    (ContinuousLinearMap.fst ℝ (Matrix d d ℂ) (Matrix d d ℂ))
    (ContinuousLinearMap.snd ℝ (Matrix d d ℂ) (Matrix d d ℂ))).flip)

theorem wydPairing_apply (β : ℝ) (P Q : Matrix d d ℂ × Matrix d d ℂ) : wydPairing β P Q =
    (2 * (β * (1 - β)))⁻¹ * (hsForm P.1 Q.2 + hsForm Q.1 P.2) := by
  simp [wydPairing, mul_add]

theorem wydPairing_comm (β : ℝ) (P Q : Matrix d d ℂ × Matrix d d ℂ) :
    wydPairing β P Q = wydPairing β Q P := by
  rw [wydPairing_apply, wydPairing_apply, add_comm]

/-- The embedding `ρ ↦ (ρ^β, ρ^{1-β})` in the affine chart `z ↦ ρ₀ + z`. -/
noncomputable def wydChart (β : ℝ) (V : Submodule ℝ (Matrix d d ℂ)) (ρ₀ : Matrix d d ℂ) (z : V) :
    Matrix d d ℂ × Matrix d d ℂ :=
  (matPow β (V.subtypeL z + ρ₀), matPow (1 - β) (V.subtypeL z + ρ₀))

/-- **The Wigner–Yanase–Dyson metric** in the affine chart `z ↦ ρ₀ + z` of `ρ₀ + V`. -/
noncomputable def wydMetric (β : ℝ) (V : Submodule ℝ (Matrix d d ℂ)) (ρ₀ : Matrix d d ℂ) :
    V → V →L[ℝ] V →L[ℝ] ℝ :=
  pullback (wydChart β V ρ₀) fun _ ↦ wydPairing β

variable {β : ℝ} {V : Submodule ℝ (Matrix d d ℂ)} {ρ₀ : Matrix d d ℂ}

/-- The logarithm in the chart. -/
noncomputable def logChart (V : Submodule ℝ (Matrix d d ℂ)) (ρ₀ : Matrix d d ℂ) (z : V) :
    Matrix d d ℂ := matLog (V.subtypeL z + ρ₀)

omit [Fintype d] [DecidableEq d] in
theorem chart_zero' : V.subtypeL (0 : V) + ρ₀ = ρ₀ := by simp

theorem contDiffAt_logChart (hρ : ρ₀.PosDef) (n : ℕ) : ContDiffAt ℝ n (logChart V ρ₀) 0 := by
  have hA := contDiffAt_matLog hρ n
  rw [← chart_zero' (V := V) (ρ₀ := ρ₀)] at hA
  exact hA.comp (f := fun z : V ↦ V.subtypeL z + ρ₀) (0 : V)
    ((V.subtypeL.contDiff.add (contDiff_const (c := ρ₀))).contDiffAt)

theorem contDiffAt_powChart (s : ℝ) (hρ : ρ₀.PosDef) (n : ℕ) :
    ContDiffAt ℝ n (fun z : V ↦ matPow s (V.subtypeL z + ρ₀)) 0 := by
  have hA := contDiffAt_matPow s hρ n
  rw [← chart_zero' (V := V) (ρ₀ := ρ₀)] at hA
  exact hA.comp (f := fun z : V ↦ V.subtypeL z + ρ₀) (0 : V)
    ((V.subtypeL.contDiff.add (contDiff_const (c := ρ₀))).contDiffAt)

theorem contDiffAt_wydChart (hρ : ρ₀.PosDef) (n : ℕ) : ContDiffAt ℝ n (wydChart β V ρ₀) 0 :=
  (contDiffAt_powChart β hρ n).prodMk (contDiffAt_powChart (1 - β) hρ n)

/-- First derivative of the power in the chart, in logarithmic coordinates. -/
theorem fderiv_powChart (s : ℝ) (hρ : ρ₀.PosDef) (w : V) :
    fderiv ℝ (fun z : V ↦ matPow s (V.subtypeL z + ρ₀)) 0 w =
      expDeriv ℝ (s • matLog ρ₀) (s • fderiv ℝ (logChart V ρ₀) 0 w) := by
  have hd := (contDiffAt_logChart (V := V) hρ 1).differentiableAt one_ne_zero
  have h := fderiv_exp_comp (L := fun z : V ↦ s • logChart V ρ₀ z) (hd.const_smul s) w
  rw [fderiv_fun_const_smul hd] at h
  simpa [logChart, matPow] using h

/-- Second derivative of the power in the chart, in logarithmic coordinates. -/
theorem fderiv_fderiv_powChart (s : ℝ) (hρ : ρ₀.PosDef) (v w : V) :
    fderiv ℝ (fderiv ℝ (fun z : V ↦ matPow s (V.subtypeL z + ρ₀))) 0 v w =
      expDeriv2 ℝ (s • matLog ρ₀) (s • fderiv ℝ (logChart V ρ₀) 0 v)
        (s • fderiv ℝ (logChart V ρ₀) 0 w) +
      expDeriv ℝ (s • matLog ρ₀) (s • fderiv ℝ (fderiv ℝ (logChart V ρ₀)) 0 v w) := by
  have h2 := contDiffAt_logChart (V := V) hρ 2
  have hd := h2.differentiableAt (by simp)
  have hev : ∀ᶠ y in 𝓝 (0 : V), DifferentiableAt ℝ (logChart V ρ₀) y :=
    (h2.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hL2 : DifferentiableAt ℝ (fderiv ℝ (logChart V ρ₀)) 0 :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h := fderiv_fderiv_exp_comp (L := fun z : V ↦ s • logChart V ρ₀ z) (h2.const_smul s) v w
  have hf : fderiv ℝ (fun z : V ↦ s • logChart V ρ₀ z) =ᶠ[𝓝 0]
      fun y ↦ s • fderiv ℝ (logChart V ρ₀) y := hev.mono fun y hy ↦ by
    rw [fderiv_fun_const_smul hy]
  rw [hf.fderiv_eq, fderiv_fun_const_smul hL2, fderiv_fun_const_smul hd] at h
  simpa [logChart, matPow] using h

end Metric

end WYD
