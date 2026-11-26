/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import WYDCurvature.Petz.Curvature.Hessian
import WYDCurvature.Petz.Curvature.Pullback
import WYDCurvature.Petz.ForMathlib.Basic
import WYDCurvature.Petz.KuboMori.Form

/-!
# Curvature of the BKM metric

The BKM metric of the density matrices in an affine chart, with the hypotheses of the curvature
theorems for fields with a totally symmetric derivative (`Curvature/Hessian.lean`) verified, and
its values and derivative at a diagonal state.  This is the first half of Dittmann's Theorem 2.

For a real subspace `V` of complex `d × d` matrices and a matrix `ρ₀`, `bkmChart V ρ₀` is the
pullback of the BKM form `bkmForm` (`KuboMori/Form.lean`) by the affine map
`z ↦ ρ₀ + z` (`Curvature/Pullback.lean`). For `V` the traceless Hermitian matrices and `ρ₀` a
positive definite density matrix, this is the state space of `d`-level density matrices near
`ρ₀`, with its BKM metric; for `V` all Hermitian matrices it is the cone of unnormalized states.

## Main definitions

* `PetzCurvature.tracelessHermitian d`, `PetzCurvature.hermitian d`: the real
  subspaces of traceless Hermitian and of Hermitian matrices.
* `PetzCurvature.bkmChart V ρ₀`: the BKM form in the chart `z ↦ ρ₀ + z` of `ρ₀ + V`.
* `PetzCurvature.bkmIntegral₂`, `PetzCurvature.bkmIntegral₃`: the scalar integrals
  `m(x, y) = ∫₀¹ ds / (a b)` and `m(x, y, z) = ∫₀¹ (1 - s) ds / (a b c)`, with
  `a = (1 - s) x + s` and so on.

## Main statements

For positive definite `ρ₀`:
* `PetzCurvature.contDiffAt_bkmChart`: the chart field is `Cⁿ` at `0` for every `n`.
* `PetzCurvature.eventually_bkmChart_comm`,
  `PetzCurvature.eventually_fderiv_bkmChart_comm`: near `0` it is symmetric and its
  derivative is totally symmetric; `PetzCurvature.fderiv_bkmChart_apply`: that derivative
  is the restriction of the derivative of `bkmForm`.
* `PetzCurvature.isInvertible_bkmChart`: on a subspace of Hermitian matrices it is positive
  definite, hence invertible, at `0` (`PetzCurvature.bkmForm_self_pos`).

At a diagonal matrix `ρ = diag(l)`, `l > 0`:
* `PetzCurvature.bkmForm_diagonal`: `G(A, B) = ∑ᵢⱼ m(lᵢ, lⱼ) Re(Aᵢⱼ Bⱼᵢ)`, and
  `m(x, y) = (log x - log y)/(x - y)`, `m(x, x) = 1/x` (`bkmIntegral₂_eq_bkm`).
* `PetzCurvature.fderiv_bkmForm_diagonal`:
  `DG(Z)(A, B) = -∑ᵢⱼₖ m(lᵢ, lⱼ, lₖ) (Re(Aᵢⱼ Zⱼₖ Bₖᵢ) + Re(Aᵢⱼ Bⱼₖ Zₖᵢ))`, with
  `m(x, y, z) = (m(x, z) - m(y, z))/(y - x)` for `x ≠ y` (`bkmIntegral₃_of_ne`),
  `m(x, x, x) = 1/(2x²)` (`bkmIntegral₃_self`) and `m` symmetric, which determine it.
* `PetzCurvature.bkmForm_diagonal_self_left`,
  `PetzCurvature.fderiv_bkmForm_diagonal_self`: `G(ρ, A) = Re tr A` and Euler's identity
  `DG_ρ(ρ) = -G_ρ`, from `x m(x, x, y) + y m(x, y, y) = m(x, y)` (`mul_bkmIntegral₃_add`).

The hyperplane correction:
* `PetzCurvature.scalarCurvature_bkmChart_eq_contr`: in a `G_ρ`-orthonormal basis of `V`,
  the scalar curvature is `¼ (|T|² - |τ|²)` (`bkmContrT`, `bkmContrTau`).
* `PetzCurvature.scalarCurvature_bkmChart_tracelessHermitian`: at a diagonal density matrix,
  `S(states) = S(Hermitian) + N (N - 1) / 4`, `N` the dimension of the state space, because `ρ` is
  the unit normal of the states and `DG_ρ(ρ, ·, ·) = -G_ρ` (`contr_option`).

The completeness kernel:
* `PetzCurvature.sum_mul_of_orthonormal`: for any `G_ρ`-orthonormal basis `e` of the
  Hermitian matrices at `ρ = diag(l)`, `∑ₐ (eₐ)ₚq (eₐ)ₛᵣ = δₚᵣ δqₛ / m(lᵣ, lₛ)`.
* `PetzCurvature.finrank_hermitian`, `PetzCurvature.finrank_tracelessHermitian`: the
  dimensions `n²` and `n² - 1`, and so `scalarCurvature_bkmChart_tracelessHermitian_eq`:
  `S(states) = S(Hermitian) + (n² - 1)(n² - 2)/4`.

## References

* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]

-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set
open PetzCurvature.Curvature

namespace PetzCurvature

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The real subspace of **traceless Hermitian matrices**: the tangent space of the density
matrices. -/
def tracelessHermitian (d : Type*) [Fintype d] : Submodule ℝ (Matrix d d ℂ) where
  carrier := {A | A.IsHermitian ∧ A.trace = 0}
  add_mem' ha hb := ⟨ha.1.add hb.1, by simp [trace_add, ha.2, hb.2]⟩
  zero_mem' := ⟨isHermitian_zero, trace_zero d ℂ⟩
  smul_mem' c A ha := ⟨by simp [IsHermitian, conjTranspose_smul, ha.1.eq], by
    simp [trace_smul, ha.2]⟩

omit [DecidableEq d] in
theorem mem_tracelessHermitian {A : Matrix d d ℂ} :
    A ∈ tracelessHermitian d ↔ A.IsHermitian ∧ A.trace = 0 :=
  Iff.rfl

/-- The real subspace of **Hermitian matrices**. -/
def hermitian (d : Type*) [Fintype d] : Submodule ℝ (Matrix d d ℂ) where
  carrier := {A | A.IsHermitian}
  add_mem' ha hb := IsHermitian.add ha hb
  zero_mem' := isHermitian_zero
  smul_mem' c A ha := by simp [IsHermitian, conjTranspose_smul, ha.eq]

omit [DecidableEq d] in
theorem mem_hermitian {A : Matrix d d ℂ} : A ∈ hermitian d ↔ A.IsHermitian :=
  Iff.rfl

omit [DecidableEq d] in
theorem isHermitian_of_mem_tracelessHermitian {A : Matrix d d ℂ}
    (hA : A ∈ tracelessHermitian d) : A.IsHermitian :=
  hA.1

variable (V : Submodule ℝ (Matrix d d ℂ))

/-- The BKM form in the affine chart `z ↦ ρ₀ + z` of `ρ₀ + V`: the pullback of `bkmForm` by that
chart (written `z ↦ ↑z + ρ₀`), a field of bilinear forms on `V`. For `V = tracelessHermitian d`
and a density matrix `ρ₀` it is the BKM metric of the state space in a chart centred at `ρ₀`. -/
noncomputable def bkmChart (ρ₀ : Matrix d d ℂ) : V → V →L[ℝ] V →L[ℝ] ℝ :=
  pullback (fun z : V ↦ V.subtypeL z + ρ₀) bkmForm

theorem bkmChart_eq (ρ₀ : Matrix d d ℂ) :
    bkmChart V ρ₀ = fun z ↦ (bkmForm (V.subtypeL z + ρ₀)).bilinearComp V.subtypeL V.subtypeL :=
  pullback_affine _ _ _

@[simp]
theorem bkmChart_apply (ρ₀ : Matrix d d ℂ) (z u w : V) :
    bkmChart V ρ₀ z u w =
      bkmForm ((z : Matrix d d ℂ) + ρ₀) (u : Matrix d d ℂ) (w : Matrix d d ℂ) := by
  rw [bkmChart_eq]
  rfl

variable {V} {ρ₀ : Matrix d d ℂ}

theorem contDiff_chartMap {n : WithTop ℕ∞} : ContDiff ℝ n fun z : V ↦ V.subtypeL z + ρ₀ :=
  V.subtypeL.contDiff.add contDiff_const

/-- **The BKM chart is smooth** at the centre `0`. -/
theorem contDiffAt_bkmChart (hρ : ρ₀.PosDef) (n : ℕ) : ContDiffAt ℝ n (bkmChart V ρ₀) 0 :=
  contDiffAt_pullback (by rw [map_zero, zero_add]; exact contDiffAt_bkmForm hρ n)
    contDiff_chartMap.contDiffAt

/-- Near the centre the path `(1 - s) (ρ₀ + z) + s` stays invertible. -/
theorem eventually_isUnit_bkmPath_chart (hρ : ρ₀.PosDef) :
    ∀ᶠ z in 𝓝 (0 : V), ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (V.subtypeL z + ρ₀, t)) := by
  have h := (contDiff_chartMap (V := V) (ρ₀ := ρ₀) (n := 0)).continuous.continuousAt (x := 0)
  rw [ContinuousAt, map_zero, zero_add] at h
  exact h.eventually (eventually_isUnit_bkmPath (isUnit_bkmPath_of_posDef hρ))

/-- The BKM chart is symmetric near the centre. -/
theorem eventually_bkmChart_comm (hρ : ρ₀.PosDef) :
    ∀ᶠ z in 𝓝 (0 : V), ∀ u w, bkmChart V ρ₀ z u w = bkmChart V ρ₀ z w u := by
  filter_upwards [eventually_isUnit_bkmPath_chart hρ] with z hz u w
  simp only [bkmChart_apply]
  exact bkmForm_comm hz _ _

/-- **The derivative of the BKM chart** is the restriction of the derivative of the BKM form:
the chart is affine, so no second-derivative term appears. -/
theorem fderiv_bkmChart_apply {z : V}
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (V.subtypeL z + ρ₀, t))) (X u w : V) :
    fderiv ℝ (bkmChart V ρ₀) z X u w =
      fderiv ℝ bkmForm ((z : Matrix d d ℂ) + ρ₀) (X : Matrix d d ℂ) (u : Matrix d d ℂ)
        (w : Matrix d d ℂ) := by
  have hφ : ∀ y : V, HasFDerivAt (fun z : V ↦ V.subtypeL z + ρ₀) V.subtypeL y :=
    fun _ ↦ V.subtypeL.hasFDerivAt.add_const ρ₀
  have hD : fderiv ℝ (fun z : V ↦ V.subtypeL z + ρ₀) = fun _ ↦ V.subtypeL :=
    funext fun y ↦ (hφ y).fderiv
  have hG : DifferentiableAt ℝ bkmForm (V.subtypeL z + ρ₀) :=
    (contDiffAt_bkmForm_of_isUnit hz 1).differentiableAt one_ne_zero
  rw [bkmChart, fderiv_pullback_apply (φ := fun z : V ↦ V.subtypeL z + ρ₀) hG
    (hφ z).differentiableAt
    (by rw [hD]; exact differentiableAt_const _), hD]
  simp

/-- The derivative of the BKM chart is totally symmetric near the centre. -/
theorem eventually_fderiv_bkmChart_comm (hρ : ρ₀.PosDef) :
    ∀ᶠ z in 𝓝 (0 : V), ∀ X u w,
      fderiv ℝ (bkmChart V ρ₀) z X u w = fderiv ℝ (bkmChart V ρ₀) z u X w := by
  filter_upwards [eventually_isUnit_bkmPath_chart hρ] with z hz X u w
  rw [fderiv_bkmChart_apply hz, fderiv_bkmChart_apply hz]
  exact fderiv_bkmForm_comm₁₂ hz _ _ _

/-- On a subspace of Hermitian matrices the BKM chart is positive definite at the centre. -/
theorem bkmChart_self_pos (hρ : ρ₀.PosDef) (hV : ∀ A ∈ V, A.IsHermitian) {u : V} (hu : u ≠ 0) :
    0 < bkmChart V ρ₀ 0 u u := by
  rw [bkmChart_apply, ZeroMemClass.coe_zero, zero_add]
  exact bkmForm_self_pos hρ (hV u u.2) (by simpa using hu)

/-- On a subspace of Hermitian matrices the BKM chart is invertible at the centre, being positive
definite in finite dimension. -/
theorem isInvertible_bkmChart (hρ : ρ₀.PosDef) (hV : ∀ A ∈ V, A.IsHermitian) :
    (bkmChart V ρ₀ 0).IsInvertible :=
  LinearMap.BilinForm.isInvertible_of_pos fun _ hu ↦ bkmChart_self_pos hρ hV hu

/-! ### The scalar integrals -/

section Scalar

variable {x y z : ℝ}

theorem pathScalar_pos (hx : 0 < x) {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) 1) : 0 < (1 - s) * x + s := by
  rw [uIcc_of_le zero_le_one] at hs
  rcases eq_or_lt_of_le hs.1 with rfl | h
  · simpa using hx
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [hs.2]) hx.le) h

theorem hasDerivAt_pathScalar (x s : ℝ) : HasDerivAt (fun s : ℝ ↦ (1 - s) * x + s) (1 - x) s := by
  exact ((((hasDerivAt_id' s).const_sub 1).mul_const x).add (hasDerivAt_id' s)).congr_deriv
    (by ring)

theorem continuousOn_pathScalar_inv (hx : 0 < x) :
    ContinuousOn (fun s : ℝ ↦ ((1 - s) * x + s)⁻¹) (uIcc 0 1) :=
  (((continuous_const.sub continuous_id).mul continuous_const).add
    continuous_id).continuousOn.inv₀ fun _ hs ↦ (pathScalar_pos hx hs).ne'

/-- The scalar BKM integral `m(x, y) = ∫₀¹ ds / (((1 - s) x + s) ((1 - s) y + s))`, equal to the
BKM kernel `(log x - log y) / (x - y)`, the first divided difference of `log`
(`bkmIntegral₂_eq_bkm`). -/
noncomputable def bkmIntegral₂ (x y : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ((1 - s) * x + s)⁻¹ * ((1 - s) * y + s)⁻¹

/-- The cubic scalar BKM integral
`m(x, y, z) = ∫₀¹ (1 - s) ds / (((1 - s) x + s) ((1 - s) y + s) ((1 - s) z + s))`, which is
`∫₀^∞ du / ((x + u) (y + u) (z + u))`, minus the second divided difference of the logarithm. -/
noncomputable def bkmIntegral₃ (x y z : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, (1 - s) * (((1 - s) * x + s)⁻¹ * ((1 - s) * y + s)⁻¹ * ((1 - s) * z + s)⁻¹)

/-- `m(x, y)` is symmetric. -/
theorem bkmIntegral₂_comm (x y : ℝ) : bkmIntegral₂ x y = bkmIntegral₂ y x := by
  unfold bkmIntegral₂
  congr 1
  funext s
  ring

/-- `m(x, y, z)` is symmetric in `x, y` (and, with `bkmIntegral₃_comm₂₃`, fully symmetric). -/
theorem bkmIntegral₃_comm₁₂ (x y z : ℝ) : bkmIntegral₃ x y z = bkmIntegral₃ y x z := by
  unfold bkmIntegral₃
  congr 1
  funext s
  ring

/-- `m(x, y, z)` is symmetric in `y, z`. -/
theorem bkmIntegral₃_comm₂₃ (x y z : ℝ) : bkmIntegral₃ x y z = bkmIntegral₃ x z y := by
  unfold bkmIntegral₃
  congr 1
  funext s
  ring

/-- On the diagonal, `m(x, x) = 1/x`. -/
theorem bkmIntegral₂_self (hx : 0 < x) : bkmIntegral₂ x x = x⁻¹ := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s ↦ s / (x * ((1 - s) * x + s)))
      (((1 - s) * x + s)⁻¹ * ((1 - s) * x + s)⁻¹) s := by
    intro s hs
    have ha := pathScalar_pos hx hs
    refine ((hasDerivAt_id' s).div ((hasDerivAt_pathScalar x s).const_mul x)
      (mul_pos hx ha).ne').congr_deriv ?_
    field_simp
    ring
  rw [bkmIntegral₂, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_pathScalar_inv hx).mul (continuousOn_pathScalar_inv hx)).intervalIntegrable]
  simp

/-- **The scalar BKM integral is the BKM kernel** off the diagonal:
`m(x, y) = (log x - log y) / (x - y)`. -/
theorem bkmIntegral₂_of_ne (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    bkmIntegral₂ x y = (Real.log x - Real.log y) / (x - y) := by
  have hyx : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have hxy' : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun s ↦ (Real.log ((1 - s) * x + s) - Real.log ((1 - s) * y + s)) / (y - x))
      (((1 - s) * x + s)⁻¹ * ((1 - s) * y + s)⁻¹) s := by
    intro s hs
    have ha := pathScalar_pos hx hs
    have hb := pathScalar_pos hy hs
    refine ((((hasDerivAt_pathScalar x s).log ha.ne').sub
      ((hasDerivAt_pathScalar y s).log hb.ne')).div_const (y - x)).congr_deriv ?_
    have ha' : x * (1 - s) + s ≠ 0 := by rw [mul_comm]; exact ha.ne'
    have hb' : y * (1 - s) + s ≠ 0 := by rw [mul_comm]; exact hb.ne'
    field_simp
    ring
  rw [bkmIntegral₂, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_pathScalar_inv hx).mul (continuousOn_pathScalar_inv hy)).intervalIntegrable]
  simp only [sub_self, zero_mul, zero_add, add_zero, one_mul, Real.log_one, zero_div,
    sub_zero]
  field_simp
  ring

/-- The scalar BKM integral is the BKM kernel `PetzKernel.bkm`. -/
theorem bkmIntegral₂_eq_bkm (hx : 0 < x) (hy : 0 < y) : bkmIntegral₂ x y = PetzKernel.bkm x y := by
  by_cases h : x = y
  · subst h
    rw [bkmIntegral₂_self hx, PetzKernel.bkm_self]
  · rw [bkmIntegral₂_of_ne hx hy h]
    simp [PetzKernel.bkm, h]

/-- The cubic integral as a difference quotient of the quadratic one:
`m(x, y, z) = (m(x, z) - m(y, z)) / (y - x)` for `x ≠ y`. -/
theorem bkmIntegral₃_of_ne (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x ≠ y) :
    bkmIntegral₃ x y z = (bkmIntegral₂ x z - bkmIntegral₂ y z) / (y - x) := by
  have hyx : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have hf : IntervalIntegrable (fun s ↦ ((1 - s) * x + s)⁻¹ * ((1 - s) * z + s)⁻¹)
      MeasureTheory.volume 0 1 :=
    ((continuousOn_pathScalar_inv hx).mul (continuousOn_pathScalar_inv hz)).intervalIntegrable
  have hg : IntervalIntegrable (fun s ↦ ((1 - s) * y + s)⁻¹ * ((1 - s) * z + s)⁻¹)
      MeasureTheory.volume 0 1 :=
    ((continuousOn_pathScalar_inv hy).mul (continuousOn_pathScalar_inv hz)).intervalIntegrable
  rw [bkmIntegral₂, bkmIntegral₂, ← intervalIntegral.integral_sub hf hg,
    ← intervalIntegral.integral_div, bkmIntegral₃]
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  have ha := pathScalar_pos hx hs
  have hb := pathScalar_pos hy hs
  have hc := pathScalar_pos hz hs
  field_simp
  ring

/-- On the diagonal, `m(x, x, x) = 1/(2x²)`, which is `-½ log''(x)`. -/
theorem bkmIntegral₃_self (hx : 0 < x) : bkmIntegral₃ x x x = (2 * x ^ 2)⁻¹ := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun s ↦ s / (x * ((1 - s) * x + s) ^ 2) +
        (1 - 2 * x) / (2 * x ^ 2) * (s ^ 2 / ((1 - s) * x + s) ^ 2))
      ((1 - s) * (((1 - s) * x + s)⁻¹ * ((1 - s) * x + s)⁻¹ * ((1 - s) * x + s)⁻¹)) s := by
    intro s hs
    have ha := pathScalar_pos hx hs
    have h1 := (hasDerivAt_id' s).div (((hasDerivAt_pathScalar x s).pow 2).const_mul x)
      (mul_pos hx (pow_pos ha 2)).ne'
    have h2 := (((hasDerivAt_id' s).pow 2).div ((hasDerivAt_pathScalar x s).pow 2)
      (pow_pos ha 2).ne').const_mul ((1 - 2 * x) / (2 * x ^ 2))
    refine (h1.add h2).congr_deriv ?_
    simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    field_simp
    ring
  have hc := continuousOn_pathScalar_inv hx
  rw [bkmIntegral₃, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_const.sub continuous_id).continuousOn.mul
      ((hc.mul hc).mul hc))).intervalIntegrable]
  field_simp
  ring

/-- **Euler's identity for the BKM integrals** (homogeneity of degree `-1`):
`x m(x, x, y) + y m(x, y, y) = m(x, y)`. -/
theorem mul_bkmIntegral₃_add (hx : 0 < x) (hy : 0 < y) :
    x * bkmIntegral₃ x x y + y * bkmIntegral₃ x y y = bkmIntegral₂ x y := by
  rcases eq_or_ne x y with rfl | h
  · rw [bkmIntegral₃_self hx, bkmIntegral₂_self hx]
    field_simp
    ring
  · have hyx : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    have hxy : x - y ≠ 0 := sub_ne_zero.2 h
    rw [bkmIntegral₃_comm₂₃, bkmIntegral₃_of_ne hx hy hx h, bkmIntegral₃_comm₁₂,
      bkmIntegral₃_of_ne hy hx hy (Ne.symm h), bkmIntegral₂_self hx, bkmIntegral₂_self hy,
      bkmIntegral₂_comm y x]
    field_simp
    ring

end Scalar

/-! ### Values at a diagonal matrix -/

section Diagonal

theorem re_trace_mul_diagonal_mul_diagonal (A B : Matrix d d ℂ) (r : d → ℝ) :
    (A * Matrix.diagonal (fun i ↦ (r i : ℂ)) * B *
      Matrix.diagonal (fun i ↦ (r i : ℂ))).trace.re =
      ∑ i, ∑ j, r i * r j * (A i j * B j i).re := by
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [diag_apply, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.mul_diagonal, show A i j * (r j : ℂ) * B j i * (r i : ℂ) =
    ((r i * r j : ℝ) : ℂ) * (A i j * B j i) by push_cast; ring, Complex.re_ofReal_mul]

theorem re_trace_mul_diagonal_cube (A Z B : Matrix d d ℂ) (r : d → ℝ) :
    (A * Matrix.diagonal (fun i ↦ (r i : ℂ)) * Z * Matrix.diagonal (fun i ↦ (r i : ℂ)) * B *
      Matrix.diagonal (fun i ↦ (r i : ℂ))).trace.re =
      ∑ i, ∑ j, ∑ k, r i * r j * r k * (A i j * Z j k * B k i).re := by
  rw [re_trace_mul_diagonal_mul_diagonal (A * Matrix.diagonal _ * Z)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.mul_diagonal, show A i j * (r j : ℂ) * Z j k * B k i =
    (r j : ℂ) * (A i j * Z j k * B k i) by ring, Complex.re_ofReal_mul]
  ring

variable {l : d → ℝ}

omit [Fintype d] in
theorem bkmPath_diagonal (l : d → ℝ) (t : ℝ) :
    bkmPath (Matrix.diagonal (fun i ↦ (l i : ℂ)), t) =
      Matrix.diagonal fun i ↦ (((1 - t) * l i + t : ℝ) : ℂ) := by
  ext i j
  rcases eq_or_ne i j with rfl | h
  · simp [bkmPath]
  · simp [bkmPath, h]

omit [Fintype d] in
theorem posDef_diagonal_ofReal (hl : ∀ i, 0 < l i) :
    (Matrix.diagonal fun i ↦ (l i : ℂ)).PosDef :=
  posDef_diagonal_iff.2 fun i ↦ by exact_mod_cast hl i

theorem inv_bkmPath_diagonal (hl : ∀ i, 0 < l i) {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) :
    (bkmPath (Matrix.diagonal (fun i ↦ (l i : ℂ)), t))⁻¹ =
      Matrix.diagonal fun i ↦ ((((1 - t) * l i + t)⁻¹ : ℝ) : ℂ) := by
  rw [bkmPath_diagonal, inv_diagonal_ofReal fun i ↦ (pathScalar_pos (hl i) ht).ne']

/-- **The BKM form at a diagonal matrix**:
`G(A, B) = ∑ᵢⱼ m(lᵢ, lⱼ) Re(Aᵢⱼ Bⱼᵢ)` at `ρ = diag(l)`, `m = bkmIntegral₂`. -/
theorem bkmForm_diagonal (hl : ∀ i, 0 < l i) (A B : Matrix d d ℂ) :
    bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) A B =
      ∑ i, ∑ j, bkmIntegral₂ (l i) (l j) * (A i j * B j i).re := by
  have hc : ∀ i j, ContinuousOn (fun t : ℝ ↦ ((1 - t) * l i + t)⁻¹ * ((1 - t) * l j + t)⁻¹ *
      (A i j * B j i).re) (uIcc 0 1) := fun i j ↦
    ((continuousOn_pathScalar_inv (hl i)).mul (continuousOn_pathScalar_inv (hl j))).mul
      continuousOn_const
  rw [bkmForm_apply (isUnit_bkmPath_of_posDef (posDef_diagonal_ofReal hl)),
    intervalIntegral.integral_congr (g := fun t ↦ ∑ i, ∑ j, ((1 - t) * l i + t)⁻¹ *
      ((1 - t) * l j + t)⁻¹ * (A i j * B j i).re) fun t ht ↦ ?_]
  · rw [intervalIntegral.integral_finsetSum fun i _ ↦
      (continuousOn_finsetSum _ fun j _ ↦ hc i j).intervalIntegrable]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [intervalIntegral.integral_finsetSum fun j _ ↦ (hc i j).intervalIntegrable]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [intervalIntegral.integral_mul_const, bkmIntegral₂]
  · simp only [sandwichForm_apply, inv_bkmPath_diagonal hl ht,
      re_trace_mul_diagonal_mul_diagonal]

/-- The BKM form at a diagonal matrix through the BKM kernel:
`G(A, B) = ∑ᵢⱼ (log lᵢ - log lⱼ)/(lᵢ - lⱼ) Re(Aᵢⱼ Bⱼᵢ)`. -/
theorem bkmForm_diagonal_eq_bkm (hl : ∀ i, 0 < l i) (A B : Matrix d d ℂ) :
    bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) A B =
      ∑ i, ∑ j, PetzKernel.bkm (l i) (l j) * (A i j * B j i).re := by
  rw [bkmForm_diagonal hl]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    rw [bkmIntegral₂_eq_bkm (hl i) (hl j)]

/-- **The derivative of the BKM form at a diagonal matrix**: at `ρ = diag(l)`,
`DG(Z)(A, B) = -∑ᵢⱼₖ m(lᵢ, lⱼ, lₖ) (Re(Aᵢⱼ Zⱼₖ Bₖᵢ) + Re(Aᵢⱼ Bⱼₖ Zₖᵢ))`,
`m = bkmIntegral₃`. -/
theorem fderiv_bkmForm_diagonal (hl : ∀ i, 0 < l i) (Z A B : Matrix d d ℂ) :
    fderiv ℝ bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) Z A B =
      -∑ i, ∑ j, ∑ k, bkmIntegral₃ (l i) (l j) (l k) *
        ((A i j * Z j k * B k i).re + (A i j * B j k * Z k i).re) := by
  have hc : ∀ i j k, ContinuousOn (fun t : ℝ ↦ (1 - t) * (((1 - t) * l i + t)⁻¹ *
      ((1 - t) * l j + t)⁻¹ * ((1 - t) * l k + t)⁻¹) *
        ((A i j * Z j k * B k i).re + (A i j * B j k * Z k i).re)) (uIcc 0 1) := fun i j k ↦
    ((continuous_const.sub continuous_id).continuousOn.mul
      (((continuousOn_pathScalar_inv (hl i)).mul (continuousOn_pathScalar_inv (hl j))).mul
        (continuousOn_pathScalar_inv (hl k)))).mul continuousOn_const
  rw [fderiv_bkmForm_apply (isUnit_bkmPath_of_posDef (posDef_diagonal_ofReal hl)),
    intervalIntegral.integral_congr (g := fun t ↦ ∑ i, ∑ j, ∑ k, (1 - t) *
      (((1 - t) * l i + t)⁻¹ * ((1 - t) * l j + t)⁻¹ * ((1 - t) * l k + t)⁻¹) *
        ((A i j * Z j k * B k i).re + (A i j * B j k * Z k i).re)) fun t ht ↦ ?_]
  · rw [intervalIntegral.integral_finsetSum fun i _ ↦ (continuousOn_finsetSum _ fun j _ ↦
      continuousOn_finsetSum _ fun k _ ↦ hc i j k).intervalIntegrable]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [intervalIntegral.integral_finsetSum fun j _ ↦
      (continuousOn_finsetSum _ fun k _ ↦ hc i j k).intervalIntegrable]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [intervalIntegral.integral_finsetSum fun k _ ↦ (hc i j k).intervalIntegrable]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [intervalIntegral.integral_mul_const, bkmIntegral₃]
  · simp only [tripleSandwich, inv_bkmPath_diagonal hl ht, re_trace_mul_diagonal_cube,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ ?_
    ring

/-- At `ρ = diag(l)`, `G(ρ, A) = Re tr A`: `ρ` is `G`-orthogonal to the traceless matrices. -/
theorem bkmForm_diagonal_self_left (hl : ∀ i, 0 < l i) (A : Matrix d d ℂ) :
    bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (Matrix.diagonal fun i ↦ (l i : ℂ)) A =
      A.trace.re := by
  rw [bkmForm_diagonal hl, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Ne.symm hj])
    (by simp), bkmIntegral₂_self (hl i), Matrix.diagonal_apply_eq, diag_apply,
    Complex.re_ofReal_mul]
  field_simp [(hl i).ne']

/-- **Euler's identity** at `ρ = diag(l)`: `DG_ρ(ρ) = -G_ρ`, from homogeneity of degree `-1`. -/
theorem fderiv_bkmForm_diagonal_self (hl : ∀ i, 0 < l i) (A B : Matrix d d ℂ) :
    fderiv ℝ bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (Matrix.diagonal fun i ↦ (l i : ℂ))
      A B = -bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) A B := by
  rw [fderiv_bkmForm_diagonal hl, bkmForm_diagonal hl, neg_inj]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single j (fun k _ hk ↦ by simp [Ne.symm hk])
    (by simp), Finset.sum_eq_single i (fun k _ hk ↦ by simp [hk])
    (by simp), Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
    show A i j * (l j : ℂ) * B j i = (l j : ℂ) * (A i j * B j i) by ring,
    show A i j * B j i * (l i : ℂ) = (l i : ℂ) * (A i j * B j i) by ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, bkmIntegral₃_comm₂₃ (l i) (l j) (l i),
    ← mul_bkmIntegral₃_add (hl i) (hl j)]
  ring

end Diagonal

/-! ### The hyperplane correction -/

section Hyperplane

/-- `|T|²` of a family: `∑ DG_ρ(eₐ, e_b, e_c)²`. -/
noncomputable def bkmContrT (ρ : Matrix d d ℂ) {ι : Type*} [Fintype ι] (e : ι → Matrix d d ℂ) :
    ℝ :=
  ∑ a, ∑ b, ∑ c, fderiv ℝ bkmForm ρ (e a) (e b) (e c) ^ 2

/-- `|τ|²` of a family: `∑ₐ (∑_b DG_ρ(eₐ, e_b, e_b))²`. -/
noncomputable def bkmContrTau (ρ : Matrix d d ℂ) {ι : Type*} [Fintype ι]
    (e : ι → Matrix d d ℂ) : ℝ :=
  ∑ a, (∑ b, fderiv ℝ bkmForm ρ (e a) (e b) (e b)) ^ 2

variable {V : Submodule ℝ (Matrix d d ℂ)} {ρ : Matrix d d ℂ}

/-- The scalar curvature of the BKM metric on `ρ + V` at `ρ`, in a `G_ρ`-orthonormal basis of `V`:
`S = ¼ (|T|² - |τ|²)`. -/
theorem scalarCurvature_bkmChart_eq_contr (hρ : ρ.PosDef) (hV : ∀ A ∈ V, A.IsHermitian)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V)
    (hb : ∀ i j, bkmForm ρ (b i) (b j) = if i = j then 1 else 0) :
    scalarCurvature (bkmChart V ρ) 0 =
      4⁻¹ * (bkmContrT ρ (fun i ↦ (b i : Matrix d d ℂ)) -
        bkmContrTau ρ (fun i ↦ (b i : Matrix d d ℂ))) := by
  have hb' : ∀ i j, bkmChart V ρ 0 (b i) (b j) = if i = j then 1 else 0 := fun i j ↦ by
    rw [bkmChart_apply, ZeroMemClass.coe_zero, zero_add, hb]
  have hx0 : ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (bkmPath (V.subtypeL (0 : V) + ρ, t)) := by
    simpa using isUnit_bkmPath_of_posDef hρ
  rw [scalarCurvature_of_fderiv_comm_of_orthonormal (G := bkmChart V ρ)
    (eventually_bkmChart_comm hρ)
    (eventually_fderiv_bkmChart_comm hρ) (contDiffAt_bkmChart hρ 2)
    (isInvertible_bkmChart hρ hV) b hb']
  simp only [fderiv_bkmChart_apply hx0, ZeroMemClass.coe_zero, zero_add, bkmContrT, bkmContrTau]

/-- **Adjoining a unit normal** `r` to an orthonormal family `e`, for a totally symmetric `D`
with `D(r, ·, ·) = -g`: `|T|²` grows by `3 |ι| + 1` and `|τ|²` by `(|ι| + 1)²`. -/
theorem contr_option {M ι : Type*} [Fintype ι] [DecidableEq ι] (D : M → M → M → ℝ)
    (g : M → M → ℝ) (r : M) (e : ι → M) (hD₁₂ : ∀ a b c, D a b c = D b a c)
    (hD₂₃ : ∀ a b c, D a b c = D a c b) (hE : ∀ A B, D r A B = -g A B)
    (hgs : ∀ A B, g A B = g B A) (he : ∀ a b, g (e a) (e b) = if a = b then 1 else 0)
    (hr : ∀ a, g r (e a) = 0) (hrr : g r r = 1) :
    (∑ o₁ : Option ι, ∑ o₂ : Option ι, ∑ o₃ : Option ι,
      D (o₁.elim r e) (o₂.elim r e) (o₃.elim r e) ^ 2 =
        ∑ a, ∑ b, ∑ c, D (e a) (e b) (e c) ^ 2 + 3 * Fintype.card ι + 1) ∧
    (∑ o₁ : Option ι, (∑ o₂ : Option ι, D (o₁.elim r e) (o₂.elim r e) (o₂.elim r e)) ^ 2 =
        ∑ a, (∑ b, D (e a) (e b) (e b)) ^ 2 + (Fintype.card ι + 1) ^ 2) := by
  have h₂ : ∀ A B, D A r B = -g A B := fun A B ↦ by rw [hD₁₂, hE]
  have h₃ : ∀ A B, D A B r = -g A B := fun A B ↦ by rw [hD₂₃, h₂]
  have hr' : ∀ a, g (e a) r = 0 := fun a ↦ by rw [hgs, hr]
  constructor
  · simp only [Fintype.sum_option, Option.elim, hE, h₂, h₃, he, hr, hr', hrr]
    simp [Finset.sum_add_distrib, apply_ite (fun x : ℝ ↦ x ^ 2)]
    ring
  · simp only [Fintype.sum_option, Option.elim, hE, h₂, he, hr', hrr]
    simp
    ring

variable {l : d → ℝ}

/-- An orthonormal basis of the traceless Hermitian matrices for the BKM metric at a diagonal
positive matrix. -/
theorem exists_orthonormal_basis_tracelessHermitian (hl : ∀ i, 0 < l i) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ (tracelessHermitian d))) ℝ (tracelessHermitian d),
      ∀ i j, bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (b i) (b j) = if i = j then 1 else 0 := by
  have hρ := posDef_diagonal_ofReal hl
  have hH₀ : ∀ A ∈ tracelessHermitian d, A.IsHermitian := fun A hA ↦ hA.1
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (bkmChart (tracelessHermitian d) _ 0)
    (fun v w ↦ (eventually_bkmChart_comm hρ).self_of_nhds v w)
    (fun v hv ↦ bkmChart_self_pos hρ hH₀ hv)
  exact ⟨b, fun i j ↦ by rw [← hb, bkmChart_apply, ZeroMemClass.coe_zero, zero_add]⟩

/-- **The state `ρ` as unit normal**: at a diagonal density matrix `ρ`, an orthonormal basis of the
traceless Hermitian matrices extends by `ρ` to an orthonormal basis of all Hermitian matrices. -/
theorem exists_basis_hermitian_option (hl : ∀ i, 0 < l i) (htr : ∑ i, l i = 1) {ι : Type*}
    [Finite ι] [DecidableEq ι] (b₀ : Module.Basis ι ℝ (tracelessHermitian d))
    (hb₀ : ∀ i j, bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (b₀ i) (b₀ j) =
      if i = j then 1 else 0) :
    ∃ b : Module.Basis (Option ι) ℝ (hermitian d),
      (∀ o, (b o : Matrix d d ℂ) = o.elim (Matrix.diagonal fun i ↦ (l i : ℂ))
        (fun a ↦ (b₀ a : Matrix d d ℂ))) ∧
      ∀ o o', bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (b o) (b o') =
        if o = o' then 1 else 0 := by
  have := Fintype.ofFinite ι
  set ρ := Matrix.diagonal fun i ↦ (l i : ℂ) with hρdef
  have hρ : ρ.PosDef := posDef_diagonal_ofReal hl
  have hx := isUnit_bkmPath_of_posDef hρ
  have htrρ : ρ.trace = 1 := by
    rw [hρdef, Matrix.trace_diagonal]
    exact_mod_cast htr
  have hρr : ∀ a, bkmForm ρ ρ (b₀ a) = 0 := fun a ↦ by
    rw [bkmForm_diagonal_self_left hl, (b₀ a).2.2, Complex.zero_re]
  have hρρ : bkmForm ρ ρ ρ = 1 := by
    rw [bkmForm_diagonal_self_left hl, htrρ, Complex.one_re]
  let e : Option ι → hermitian d :=
    fun o ↦ o.elim ⟨ρ, hρ.isHermitian⟩ (fun a ↦ ⟨b₀ a, (b₀ a).2.1⟩)
  have he : ∀ o o', bkmForm ρ (e o) (e o') = if o = o' then 1 else 0 := by
    rintro (_ | a) (_ | b)
    · exact hρρ
    · exact hρr b
    · change bkmForm ρ (b₀ a) ρ = 0
      rw [bkmForm_comm hx, hρr]
    · change bkmForm ρ (b₀ a) (b₀ b) = _
      rw [hb₀]
      simp
  have hli : LinearIndependent ℝ e :=
    linearIndependent_of_orthonormal (bkmChart (hermitian d) ρ 0) fun o o' ↦ by
      rw [bkmChart_apply, ZeroMemClass.coe_zero, zero_add, he]
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range e) := by
    rintro v -
    set c := (v : Matrix d d ℂ).trace.re
    have him : (v : Matrix d d ℂ).trace.im = 0 := by
      rw [Complex.im_eq_zero_iff_isSelfAdjoint, IsSelfAdjoint, ← trace_conjTranspose,
        (mem_hermitian.1 v.2).eq]
    have hw : (v : Matrix d d ℂ) - c • ρ ∈ tracelessHermitian d := by
      refine ⟨(hermitian d).sub_mem v.2 ((hermitian d).smul_mem c hρ.isHermitian), ?_⟩
      rw [trace_sub, trace_smul, htrρ]
      apply Complex.ext <;> simp [c, him]
    have hv : v = c • e none + ∑ a, b₀.repr ⟨_, hw⟩ a • e (some a) := by
      apply Subtype.ext
      have := congrArg (fun x : tracelessHermitian d ↦ (x : Matrix d d ℂ))
        (b₀.sum_repr ⟨_, hw⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, e, Option.elim,
        this]
      abel
    rw [hv]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩))
      (Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨some a, rfl⟩))
  refine ⟨Module.Basis.mk hli hsp, fun o ↦ ?_, fun o o' ↦ ?_⟩
  · rw [Module.Basis.mk_apply]
    cases o <;> rfl
  · rw [Module.Basis.mk_apply, Module.Basis.mk_apply, he]

omit [DecidableEq d] in
/-- The Hermitian matrices have one dimension more than the traceless ones. -/
theorem finrank_hermitian_eq (hl : ∀ i, 0 < l i) (htr : ∑ i, l i = 1) :
    Module.finrank ℝ (hermitian d) = Module.finrank ℝ (tracelessHermitian d) + 1 := by
  classical
  obtain ⟨b₀, hb₀⟩ := exists_orthonormal_basis_tracelessHermitian hl
  obtain ⟨b, -, -⟩ := exists_basis_hermitian_option hl htr b₀ hb₀
  rw [Module.finrank_eq_card_basis b, Fintype.card_option, Fintype.card_fin]

/-- **The hyperplane correction**: at a diagonal density matrix `ρ = diag(l)` the scalar curvature
of the BKM metric on the states (`ρ` + traceless Hermitian matrices) exceeds that on all positive
matrices (`ρ` + Hermitian matrices) by `N (N - 1) / 4`, `N` the dimension of the state space. The
state `ρ` is the unit normal of the states, with `DG_ρ(ρ, ·, ·) = -G_ρ`. -/
theorem scalarCurvature_bkmChart_tracelessHermitian (hl : ∀ i, 0 < l i) (htr : ∑ i, l i = 1) :
    scalarCurvature (bkmChart (tracelessHermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ))) 0 =
      scalarCurvature (bkmChart (hermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ))) 0 +
        (Module.finrank ℝ (tracelessHermitian d) : ℝ) *
          ((Module.finrank ℝ (tracelessHermitian d) : ℝ) - 1) / 4 := by
  set ρ := Matrix.diagonal fun i ↦ (l i : ℂ) with hρdef
  have hρ : ρ.PosDef := posDef_diagonal_ofReal hl
  have hx := isUnit_bkmPath_of_posDef hρ
  obtain ⟨b₀, hb₀⟩ := exists_orthonormal_basis_tracelessHermitian hl
  obtain ⟨b, hbF, hb⟩ := exists_basis_hermitian_option hl htr b₀ hb₀
  have htrρ : ρ.trace = 1 := by
    rw [hρdef, Matrix.trace_diagonal]
    exact_mod_cast htr
  obtain ⟨hT, hτ⟩ := contr_option (fun a b c ↦ fderiv ℝ bkmForm ρ a b c) (fun a b ↦ bkmForm ρ a b)
    ρ (fun a ↦ (b₀ a : Matrix d d ℂ)) (fun a b c ↦ fderiv_bkmForm_comm₁₂ hx a b c)
    (fun a b c ↦ fderiv_bkmForm_comm₂₃ hx a b c) (fun A B ↦ fderiv_bkmForm_diagonal_self hl A B)
    (fun A B ↦ bkmForm_comm hx A B) hb₀
    (fun a ↦ by rw [bkmForm_diagonal_self_left hl, (b₀ a).2.2, Complex.zero_re])
    (by rw [bkmForm_diagonal_self_left hl, htrρ, Complex.one_re])
  rw [scalarCurvature_bkmChart_eq_contr hρ (fun _ ↦ isHermitian_of_mem_tracelessHermitian) b₀ hb₀,
    scalarCurvature_bkmChart_eq_contr hρ (fun A hA ↦ hA) b hb]
  simp only [bkmContrT, bkmContrTau, hbF]
  rw [hT, hτ, Fintype.card_fin]
  ring

end Hyperplane

/-! ### The completeness kernel -/

section Completeness

variable {l : d → ℝ}

/-- `m(x, y) > 0` at positive arguments. -/
theorem bkmIntegral₂_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < bkmIntegral₂ x y := by
  rw [bkmIntegral₂_eq_bkm hx hy]
  exact PetzKernel.bkm_pos hx hy

/-- `G_ρ(E, Eᵣₛ + Eₛᵣ) = 2 m(lᵣ, lₛ) Re Eᵣₛ` at `ρ = diag(l)`, for Hermitian `E`. -/
theorem bkmForm_diagonal_single_add (hl : ∀ i, 0 < l i) {E : Matrix d d ℂ} (hE : E.IsHermitian)
    (r s : d) :
    bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) E (single r s 1 + single s r 1) =
      2 * bkmIntegral₂ (l r) (l s) * (E r s).re := by
  rw [bkmForm_diagonal hl]
  simp only [Matrix.add_apply, Matrix.single_apply, mul_add, Complex.add_re, mul_ite, mul_one,
    mul_zero, ite_and, apply_ite Complex.re, Complex.zero_re, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← hE.apply s r, Complex.star_def, Complex.conj_re, bkmIntegral₂_comm (l s)]
  ring

/-- `G_ρ(E, i Eᵣₛ - i Eₛᵣ) = 2 m(lᵣ, lₛ) Im Eᵣₛ` at `ρ = diag(l)`, for Hermitian `E`. -/
theorem bkmForm_diagonal_single_sub (hl : ∀ i, 0 < l i) {E : Matrix d d ℂ} (hE : E.IsHermitian)
    (r s : d) :
    bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) E (single r s Complex.I - single s r Complex.I) =
      2 * bkmIntegral₂ (l r) (l s) * (E r s).im := by
  rw [bkmForm_diagonal hl]
  simp only [Matrix.sub_apply, Matrix.single_apply, mul_sub, Complex.sub_re, mul_ite,
    mul_zero, ite_and, apply_ite Complex.re, Complex.zero_re, Complex.mul_I_re,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← hE.apply s r, Complex.star_def, Complex.conj_im, bkmIntegral₂_comm (l s)]
  ring

/-- Expansion of a Hermitian matrix in a `G_ρ`-orthonormal basis, entrywise:
`Xₚq = ∑ₐ G_ρ(eₐ, X) (eₐ)ₚq`. -/
theorem apply_eq_sum_of_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι ℝ (hermitian d))
    (he : ∀ a b, bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (e a) (e b) =
      if a = b then 1 else 0) {X : Matrix d d ℂ} (hX : X.IsHermitian) (p q : d) :
    X p q = ∑ a, (bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (e a) X : ℂ) *
      (e a : Matrix d d ℂ) p q := by
  have he' : ∀ a b, bkmChart (hermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ)) 0 (e a) (e b) =
      if a = b then 1 else 0 := fun a b ↦ by
    rw [bkmChart_apply, ZeroMemClass.coe_zero, zero_add, he]
  have hrepr : ∀ a, e.repr ⟨X, hX⟩ a = bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (e a) X :=
    fun a ↦ by
      rw [repr_eq_of_orthonormal (G := bkmChart (hermitian d) _) (x := 0) e he', bkmChart_apply,
        ZeroMemClass.coe_zero, zero_add]
  have := congrArg (fun Y : hermitian d ↦ (Y : Matrix d d ℂ) p q) (e.sum_repr ⟨X, hX⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Matrix.sum_apply, Matrix.smul_apply, hrepr,
    Complex.real_smul] at this
  exact this.symm

/-- **The completeness kernel**: for a `G_ρ`-orthonormal basis `e` of the Hermitian matrices at
`ρ = diag(l)`, `∑ₐ (eₐ)ₚq (eₐ)ₛᵣ = δₚᵣ δqₛ / m(lᵣ, lₛ)`. -/
theorem sum_mul_of_orthonormal (hl : ∀ i, 0 < l i) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι ℝ (hermitian d))
    (he : ∀ a b, bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (e a) (e b) =
      if a = b then 1 else 0) (p q r s : d) :
    ∑ a, (e a : Matrix d d ℂ) p q * (e a : Matrix d d ℂ) s r =
      if p = r ∧ q = s then (((bkmIntegral₂ (l r) (l s))⁻¹ : ℝ) : ℂ) else 0 := by
  set m := bkmIntegral₂ (l r) (l s)
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (bkmIntegral₂_pos (hl r) (hl s)).ne'
  have hE : ∀ a, (e a : Matrix d d ℂ).IsHermitian := fun a ↦ (e a).2
  have hX1 : (single r s 1 + single s r 1 : Matrix d d ℂ).IsHermitian := by
    simp [IsHermitian, conjTranspose_single, add_comm]
  have hX2 : (single r s Complex.I - single s r Complex.I : Matrix d d ℂ).IsHermitian := by
    rw [IsHermitian, conjTranspose_sub, conjTranspose_single, conjTranspose_single,
      Complex.star_def, Complex.conj_I, ← Matrix.single_neg, ← Matrix.single_neg]
    abel
  have h1 : (single r s 1 + single s r 1 : Matrix d d ℂ) p q =
      ∑ a, ((2 * m * ((e a : Matrix d d ℂ) r s).re : ℝ) : ℂ) * (e a : Matrix d d ℂ) p q := by
    rw [apply_eq_sum_of_orthonormal e he hX1]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [bkmForm_diagonal_single_add hl (hE a)]
  have h2 : (single r s Complex.I - single s r Complex.I : Matrix d d ℂ) p q =
      ∑ a, ((2 * m * ((e a : Matrix d d ℂ) r s).im : ℝ) : ℂ) * (e a : Matrix d d ℂ) p q := by
    rw [apply_eq_sum_of_orthonormal e he hX2]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [bkmForm_diagonal_single_sub hl (hE a)]
  have hconj : ∀ a, (e a : Matrix d d ℂ) s r =
      (((e a : Matrix d d ℂ) r s).re : ℂ) - (((e a : Matrix d d ℂ) r s).im : ℂ) * Complex.I :=
    fun a ↦ by
      rw [← (hE a).apply s r]
      apply Complex.ext <;> simp
  have key : ∑ a, (e a : Matrix d d ℂ) p q * (e a : Matrix d d ℂ) s r =
      ((single r s 1 + single s r 1 : Matrix d d ℂ) p q -
        Complex.I * (single r s Complex.I - single s r Complex.I : Matrix d d ℂ) p q) /
          (2 * m) := by
    rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hconj a]
    field_simp
    push_cast
    ring_nf
  rw [key]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply]
  by_cases h1 : r = p ∧ s = q
  · obtain ⟨rfl, rfl⟩ := h1
    by_cases h2 : s = r
    · subst h2
      simp only [and_self, ite_true]
      push_cast
      field_simp
      ring
    · simp only [and_self, ite_true, h2, Ne.symm h2, ite_false]
      push_cast
      field_simp
      linear_combination (-1 : ℂ) * Complex.I_sq
  · have h1' : ¬(p = r ∧ q = s) := fun h ↦ h1 ⟨h.1.symm, h.2.symm⟩
    simp only [h1, h1', ite_false, zero_add, zero_sub]
    by_cases h2 : s = p ∧ r = q
    · simp only [h2, and_self, ite_true]
      rw [div_eq_zero_iff]
      left
      linear_combination Complex.I_sq
    · simp [h2]

omit [DecidableEq d] in
/-- **The Hermitian `d × d` matrices have real dimension `d²`**, read off the completeness kernel
at `ρ = 1`: `dim = ∑ₐ G(eₐ, eₐ) = ∑ᵢⱼ m(1, 1) · m(1, 1)⁻¹`. -/
theorem finrank_hermitian : Module.finrank ℝ (hermitian d) = Fintype.card d ^ 2 := by
  classical
  have hl : ∀ _ : d, (0 : ℝ) < 1 := fun _ ↦ one_pos
  have hρ := posDef_diagonal_ofReal hl
  obtain ⟨e, he⟩ := exists_orthonormal_basis (bkmChart (hermitian d) _ 0)
    (fun v w ↦ (eventually_bkmChart_comm hρ).self_of_nhds v w)
    (fun v hv ↦ bkmChart_self_pos hρ (fun _ h ↦ h) hv)
  have he' : ∀ a b, bkmForm (Matrix.diagonal fun _ : d ↦ ((1 : ℝ) : ℂ)) (e a) (e b) =
      if a = b then 1 else 0 := fun a b ↦ by
    rw [← he, bkmChart_apply, ZeroMemClass.coe_zero, zero_add]
  have key : ((Module.finrank ℝ (hermitian d) : ℕ) : ℝ) = ((Fintype.card d ^ 2 : ℕ) : ℝ) := by
    calc ((Module.finrank ℝ (hermitian d) : ℕ) : ℝ)
        = ∑ a, bkmForm (Matrix.diagonal fun _ : d ↦ ((1 : ℝ) : ℂ)) (e a) (e a) := by
          simp only [he', ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one]
      _ = ∑ i, ∑ j, bkmIntegral₂ 1 1 *
            (∑ a, (e a : Matrix d d ℂ) i j * (e a : Matrix d d ℂ) j i).re := by
          simp only [bkmForm_diagonal hl, Complex.re_sum, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_comm]
      _ = ∑ _i : d, ∑ _j : d, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          rw [sum_mul_of_orthonormal hl e he' i j i j]
          simp only [and_self, ite_true, Complex.ofReal_re]
          exact mul_inv_cancel₀ (bkmIntegral₂_pos one_pos one_pos).ne'
      _ = ((Fintype.card d ^ 2 : ℕ) : ℝ) := by simp [sq]
  exact_mod_cast key

omit [DecidableEq d] in
/-- The density matrices of `d` levels form a manifold of dimension `d² - 1`. The faithful state
`diag(l)` only serves to make `d` nonempty; for empty `d` the dimension is `0`, not `-1`. -/
theorem finrank_tracelessHermitian {l : d → ℝ} (hl : ∀ i, 0 < l i) (htr : ∑ i, l i = 1) :
    (Module.finrank ℝ (tracelessHermitian d) : ℝ) = (Fintype.card d : ℝ) ^ 2 - 1 := by
  have h := finrank_hermitian_eq hl htr
  rw [finrank_hermitian] at h
  have : ((Fintype.card d ^ 2 : ℕ) : ℝ) = (Module.finrank ℝ (tracelessHermitian d) : ℝ) + 1 := by
    exact_mod_cast h
  push_cast at this
  linarith

/-- **The hyperplane correction with Dittmann's constant**: at a diagonal density matrix of `n`
levels, `S(states) = S(Hermitian) + (n² - 1)(n² - 2)/4`. -/
theorem scalarCurvature_bkmChart_tracelessHermitian_eq (hl : ∀ i, 0 < l i)
    (htr : ∑ i, l i = 1) :
    scalarCurvature (bkmChart (tracelessHermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ))) 0 =
      scalarCurvature (bkmChart (hermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ))) 0 +
        ((Fintype.card d : ℝ) ^ 2 - 1) * ((Fintype.card d : ℝ) ^ 2 - 2) / 4 := by
  rw [scalarCurvature_bkmChart_tracelessHermitian hl htr, finrank_tracelessHermitian hl htr]
  ring

end Completeness

end PetzCurvature
