/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Algebra.Order.Chebyshev
import WYDCurvature.Final

/-!
# Conjecture 8.1 of Gibilisco–Isola, with the definitions of the paper

The definitions of *On the monotonicity of scalar curvature in classical and quantum information
geometry* (math-ph/0407007), with their numbers there:

* `density n`: the density matrices `D¹ₙ = {ρ | Tr ρ = 1, ρ > 0}`, Definition 2.5;
* `MoreMixed x y`: `x ≻ y`, Definition 2.3 (partial sums of the decreasing rearrangements), and
  `MoreMixedMatrix A B`: `A ≻ B`, Definition 2.6;
* `SchurIncreasingOn S f`: Definition 2.8, and its strict form `StrictSchurIncreasingOn S f`;
* `fGI p`: the function `f_p` of Definition 6.1; `cMC f x y = 1/(y f(x/y))`, Section 5;
* `cLR f ρ B`: `c_f(L_ρ, R_ρ)(B)`, Theorem 5.2: the linear map (`cLR_add`, `cLR_smul`) that multiplies
  `u v*` by `c_f(a, b)` when `ρu = au` and `ρv = bv` (`cLR_vecMulVec`);
* `IsWYDMetric p g`: `g` is the `WYD(p)` metric `Tr (A c_f(L_ρ, R_ρ)(B))` on `D¹ₙ`, Definition 6.2; the
  tangent space is the Hermitian matrices of trace zero;
* `scal g ρ`: the scalar curvature of `g` at `ρ`, computed in the chart `z ↦ ρ + z`. The base point of
  the chart does not matter (`scal_eq_chart`).

`conjecture81` is Conjecture 8.1. It is a special case of `wyd_schurIncreasing`, which holds for
`p ≤ -1` and for `p ≥ 1/2`, `p ≠ 1`: these are the finite `p ≠ 1` for which the metric is monotone
(Theorem 6.1, formalized in `WYD/Theorem61.lean`, `theorem61`). `wyd_strictly` is the strict form, for `p ≠ 1, 2`. The cases `p = 1` and
`p = ∞` are the Kubo–Mori metric, `f₁ = f_∞`: Petz's conjecture, proved in PetzCurvature and brought in by
`WYD/KuboMori.lean` (`wyd_schurIncreasing_all`, every `p ≤ -1` and `p ≥ 1/2`).
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set
open AlphaCurvature AlphaCurvature.Curvature AlphaCurvature.Quantum

namespace WYD.Literal

/-! ### The definitions -/

/-- The conjugate exponent, `1/p + 1/p̃ = 1` (for `p ≠ 0, 1`). -/
noncomputable def conj (p : ℝ) : ℝ := p / (p - 1)

theorem one_div_add_one_div_conj {p : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) : 1 / p + 1 / conj p = 1 := by
  have : p - 1 ≠ 0 := sub_ne_zero.2 h1
  rw [conj]
  field_simp
  ring

/-- Definition 6.1: `f_p(x) = (1/(p p̃)) (x - 1)² / ((x^{1/p} - 1)(x^{1/p̃} - 1))` for `p ≠ 0, 1`, and
`f₁(x) = (x - 1)/log x`; both are `1` at `x = 1`, by continuity. For `p = 0` there is no metric and the
value has no meaning. -/
noncomputable def fGI (p x : ℝ) : ℝ :=
  if x = 1 then 1
  else if p = 1 then (x - 1) / Real.log x
  else 1 / (p * conj p) * ((x - 1) ^ 2 / ((x ^ (1 / p) - 1) * (x ^ (1 / conj p) - 1)))

/-- The Morozova–Chentsov function of `f`. -/
noncomputable def cMC (f : ℝ → ℝ) (x y : ℝ) : ℝ := 1 / (y * f (x / y))

section Defs

variable {d : Type*} [Fintype d] [DecidableEq d]

open Classical in
/-- `c_f(L_ρ, R_ρ)(B)`: in an eigenbasis of `ρ` the entry `(i, j)` is multiplied by `c_f(λᵢ, λⱼ)`. -/
noncomputable def cLR (f : ℝ → ℝ) (ρ B : Matrix d d ℂ) : Matrix d d ℂ :=
  if h : ρ.IsHermitian then
    (h.eigenvectorUnitary : Matrix d d ℂ) *
      Matrix.of (fun i j ↦ (cMC f (h.eigenvalues i) (h.eigenvalues j) : ℂ) *
        (star (h.eigenvectorUnitary : Matrix d d ℂ) * B * (h.eigenvectorUnitary : Matrix d d ℂ)) i j) *
      star (h.eigenvectorUnitary : Matrix d d ℂ)
  else 0

/-- `G` is the `WYD(p)` metric in the chart `z ↦ ρ₀ + z` of the density matrices. -/
def IsWYD (p : ℝ) (ρ₀ : Matrix d d ℂ)
    (G : tracelessHermitian d → tracelessHermitian d →L[ℝ] tracelessHermitian d →L[ℝ] ℝ) : Prop :=
  ∀ z : tracelessHermitian d, ((z : Matrix d d ℂ) + ρ₀).PosDef → ∀ A B : tracelessHermitian d,
    G z A B = (Matrix.trace ((A : Matrix d d ℂ) * cLR (fGI p) ((z : Matrix d d ℂ) + ρ₀) B)).re

end Defs

/-- The decreasing rearrangement `x↓`. -/
noncomputable def decr {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i ↦ (x ∘ Tuple.sort x) i.rev

theorem antitone_decr {n : ℕ} (x : Fin n → ℝ) : Antitone (decr x) := fun _ _ h ↦
  Tuple.monotone_sort x (Fin.rev_le_rev.2 h)

/-- Definition 2.3: `x` is more mixed than `y`, `x ≻ y`. -/
def MoreMixed {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  (∀ k < n, ∑ i with (i : Fin n).val < k, decr x i ≤ ∑ i with (i : Fin n).val < k, decr y i) ∧
    ∑ i, decr x i = ∑ i, decr y i

/-- Definition 2.6: `A ≻ B` for Hermitian matrices. -/
def MoreMixedMatrix {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (hA : A.IsHermitian) (hB : B.IsHermitian), MoreMixed hA.eigenvalues hB.eigenvalues

/-- The spectra of two Hermitian matrices are equal up to order. -/
def SameSpectrum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (hA : A.IsHermitian) (hB : B.IsHermitian) (τ : Equiv.Perm (Fin n)),
    hA.eigenvalues ∘ τ = hB.eigenvalues

/-- Definition 2.8: `f` is Schur-increasing on `S`. -/
def SchurIncreasingOn {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (f : Matrix (Fin n) (Fin n) ℂ → ℝ) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, MoreMixedMatrix A B → f A ≥ f B

/-- The strict form: `f A > f B` if `A ≻ B` and the spectra differ. -/
def StrictSchurIncreasingOn {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (f : Matrix (Fin n) (Fin n) ℂ → ℝ) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, MoreMixedMatrix A B → ¬ SameSpectrum A B → f A > f B

/-- Definition 2.5: the density matrices `D¹ₙ`. -/
def density (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := {ρ | ρ.PosDef ∧ ρ.trace = 1}

/-- A field of bilinear forms on the tangent spaces of `D¹ₙ`, which are the Hermitian matrices of trace
zero; only its values on `D¹ₙ` matter. -/
abbrev FormField (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) ℂ → tracelessHermitian (Fin n) →L[ℝ] tracelessHermitian (Fin n) →L[ℝ] ℝ

/-- Definition 6.2: `g` is the `WYD(p)` metric on `D¹ₙ`, `g_ρ(A, B) = Tr (A c_f(L_ρ, R_ρ)(B))` with
`f = f_p`. -/
def IsWYDMetric {n : ℕ} (p : ℝ) (g : FormField n) : Prop :=
  ∀ ρ ∈ density n, ∀ A B : tracelessHermitian (Fin n),
    g ρ A B = (Matrix.trace ((A : Matrix (Fin n) (Fin n) ℂ) * cLR (fGI p) ρ B)).re

/-- The scalar curvature of `g` at `ρ`, in the chart `z ↦ ρ + z`. -/
noncomputable def scal {n : ℕ} (g : FormField n) (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  scalarCurvature (fun z : tracelessHermitian (Fin n) ↦ g ((z : Matrix (Fin n) (Fin n) ℂ) + ρ)) 0

/-! ### `c_f(L_ρ, R_ρ)` -/

section CLR

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem cLR_add (f : ℝ → ℝ) (ρ A B : Matrix d d ℂ) : cLR f ρ (A + B) = cLR f ρ A + cLR f ρ B := by
  unfold cLR
  split_ifs with h
  · rw [← Matrix.add_mul, ← Matrix.mul_add]
    congr 2
    ext i j
    simp [Matrix.mul_add, Matrix.add_mul]
    ring
  · simp

theorem cLR_smul (f : ℝ → ℝ) (ρ B : Matrix d d ℂ) (c : ℂ) : cLR f ρ (c • B) = c • cLR f ρ B := by
  unfold cLR
  split_ifs with h
  · rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j
    simp
    ring
  · simp

/-- **The functional calculus**: `L_ρ` and `R_ρ` multiply `u v*` by `a` and `b` when `ρu = au` and
`ρv = bv`, and `c_f(L_ρ, R_ρ)` multiplies it by `c_f(a, b)`. -/
theorem cLR_vecMulVec (f : ℝ → ℝ) {ρ : Matrix d d ℂ} (h : ρ.IsHermitian) {u v : d → ℂ} {a b : ℝ}
    (hu : ρ *ᵥ u = (a : ℂ) • u) (hv : ρ *ᵥ v = (b : ℂ) • v) :
    cLR f ρ (vecMulVec u (star v)) = (cMC f a b : ℂ) • vecMulVec u (star v) := by
  set U := (h.eigenvectorUnitary : Matrix d d ℂ) with hU
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 h.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 h.eigenvectorUnitary.2
  have hspec : ρ = U * Matrix.diagonal (fun i ↦ (h.eigenvalues i : ℂ)) * star U := by
    conv_lhs => rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  -- coordinates of an eigenvector
  have key : ∀ {w : d → ℂ} {c : ℝ}, ρ *ᵥ w = (c : ℂ) • w → ∀ i, (star U *ᵥ w) i ≠ 0 →
      h.eigenvalues i = c := by
    intro w c hw i hi
    have e : Matrix.diagonal (fun i ↦ (h.eigenvalues i : ℂ)) *ᵥ (star U *ᵥ w) =
        (c : ℂ) • (star U *ᵥ w) := by
      rw [← Matrix.mulVec_smul, ← hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      refine congrArg (· *ᵥ w) ?_
      calc _ = star U * (U * Matrix.diagonal (fun i ↦ (h.eigenvalues i : ℂ)) * star U) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
        _ = star U * ρ := by rw [← hspec]
    have := congrFun e i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    exact Complex.ofReal_injective (mul_right_cancel₀ hi this)
  have hM : star U * vecMulVec u (star v) * U = vecMulVec (star U *ᵥ u) (star (star U *ᵥ v)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
    congr 1
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hinner : Matrix.of (fun i j ↦ (cMC f (h.eigenvalues i) (h.eigenvalues j) : ℂ) *
      (star U * vecMulVec u (star v) * U) i j) =
      (cMC f a b : ℂ) • (star U * vecMulVec u (star v) * U) := by
    ext i j
    rw [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hM, Matrix.vecMulVec_apply]
    by_cases hi : (star U *ᵥ u) i = 0
    · rw [hi]; simp
    by_cases hj : (star U *ᵥ v) j = 0
    · simp [hj]
    rw [key hu i hi, key hv j hj]
  rw [cLR, dite_eq_left h, ← hU, hinner, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_assoc, hUU', Matrix.mul_one, ← Matrix.mul_assoc, hUU',
    Matrix.one_mul]

theorem cMC_fGI {p x y : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) (hx : 0 < x) (hy : 0 < y) :
    cMC (fGI p) x y = (1 / p * (1 - 1 / p))⁻¹ *
      (powKernel (1 / p) x y * powKernel (1 - 1 / p) x y) := by
  have hc : 1 / conj p = 1 - 1 / p := by have := one_div_add_one_div_conj h0 h1; linarith
  have hb : 1 / p ≠ 0 := one_div_ne_zero h0
  have hb1 : 1 - 1 / p ≠ 0 := by
    rw [sub_ne_zero]; intro h; rw [eq_div_iff h0, one_mul] at h; exact h1 h
  have hpc : 1 / (p * conj p) = 1 / p * (1 - 1 / p) := by rw [← hc]; ring
  rcases eq_or_ne x y with rfl | hxy
  · rw [cMC, div_self hx.ne', fGI, ite_eq_left rfl, powKernel_self, powKernel_self, mul_one]
    have e : x ^ (1 / p - 1) * x ^ (1 - 1 / p - 1) = x⁻¹ := by
      rw [← Real.rpow_add hx, show 1 / p - 1 + (1 - 1 / p - 1) = -1 by ring, Real.rpow_neg_one]
    calc 1 / x = x⁻¹ := one_div x
      _ = (1 / p * (1 - 1 / p))⁻¹ * ((1 / p * (1 - 1 / p)) * (x ^ (1 / p - 1) *
          x ^ (1 - 1 / p - 1))) := by rw [e, inv_mul_cancel_left₀ (mul_ne_zero hb hb1)]
      _ = _ := by ring
  · have hne : x / y ≠ 1 := fun h ↦ hxy ((div_eq_one_iff_eq hy.ne').1 h)
    have hxy' : x - y ≠ 0 := sub_ne_zero.2 hxy
    rw [cMC, fGI, ite_eq_right hne, ite_eq_right h1, hpc, hc, powKernel_of_ne hxy, powKernel_of_ne hxy,
      Real.div_rpow hx.le hy.le, Real.div_rpow hx.le hy.le]
    set s := 1 / p
    have hys : 0 < y ^ s := Real.rpow_pos_of_pos hy _
    have hys1 : 0 < y ^ (1 - s) := Real.rpow_pos_of_pos hy _
    have hyy : y ^ s * y ^ (1 - s) = y := by
      rw [← Real.rpow_add hy, show s + (1 - s) = 1 by ring, Real.rpow_one]
    have n1 : x ^ s - y ^ s ≠ 0 := fun h ↦ hxy (by
      have := sub_eq_zero.1 h
      exact (Real.rpow_left_inj hx.le hy.le hb).1 this)
    have n2 : x ^ (1 - s) - y ^ (1 - s) ≠ 0 := fun h ↦ hxy (by
      have := sub_eq_zero.1 h
      exact (Real.rpow_left_inj hx.le hy.le hb1).1 this)
    have e1 : x ^ s / y ^ s - 1 = (x ^ s - y ^ s) / y ^ s := by field_simp
    have e2 : x ^ (1 - s) / y ^ (1 - s) - 1 = (x ^ (1 - s) - y ^ (1 - s)) / y ^ (1 - s) := by
      field_simp
    have e3 : x / y - 1 = (x - y) / y := by field_simp
    rw [e1, e2, e3, div_mul_div_comm, hyy]
    generalize x ^ s - y ^ s = X at *
    generalize x ^ (1 - s) - y ^ (1 - s) = Y at *
    field_simp

/-- The metric of the main theorem is the paper's. -/
theorem wydMetric_eq {p : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) (ρ₀ : Matrix d d ℂ) :
    IsWYD p ρ₀ (wydMetric (1 / p) (tracelessHermitian d) ρ₀) := by
  intro z hz A B
  set x : Matrix d d ℂ := (z : Matrix d d ℂ) + ρ₀ with hx
  -- move the base point of the chart
  have hshift : wydMetric (1 / p) (tracelessHermitian d) ρ₀ z =
      wydMetric (1 / p) (tracelessHermitian d) x 0 := by
    have hf : fderiv ℝ (wydChart (1 / p) (tracelessHermitian d) ρ₀) z =
        fderiv ℝ (wydChart (1 / p) (tracelessHermitian d) x) 0 := by
      have e : wydChart (1 / p) (tracelessHermitian d) x =
          fun y ↦ wydChart (1 / p) (tracelessHermitian d) ρ₀ (z + y) := by
        funext y
        simp only [wydChart, hx, map_add, Submodule.subtypeL_apply]
        rw [add_assoc, add_comm (y : Matrix d d ℂ), add_assoc, add_comm ρ₀]
      rw [e, fderiv_comp_add_left, add_zero]
    ext u w
    rw [wydMetric, wydMetric, pullback_apply, pullback_apply, hf]
  have hxD : x = (hz.1.eigenvectorUnitary : Matrix d d ℂ) * diagS hz.1.eigenvalues *
      star (hz.1.eigenvectorUnitary : Matrix d d ℂ) := by
    conv_lhs => rw [hz.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  set l := hz.1.eigenvalues with hl
  set U := (hz.1.eigenvectorUnitary : Matrix d d ℂ) with hU
  have hUm : U ∈ Matrix.unitaryGroup d ℂ := hz.1.eigenvectorUnitary.2
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hUm
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hUm
  have hpos : ∀ i, 0 < l i := hz.eigenvalues_pos
  have hconj : ∀ M : Matrix d d ℂ, M = U * (star U * M * U) * star U := fun M ↦ by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, hUU', Matrix.mul_one,
      ← Matrix.mul_assoc, hUU', Matrix.one_mul]
  have hder : ∀ (s : ℝ) (M : Matrix d d ℂ), fderiv ℝ (matPow s) x M =
      U * fderiv ℝ (matPow s) (diagS l) (star U * M * U) * star U := fun s M ↦ by
    conv_lhs => rw [hxD, hconj M]
    exact fderiv_matPow_conj s hUm hpos _
  rw [hshift, wydMetric_apply _ hz, hder, hder, cLR, dite_eq_left hz.1, ← hU, ← hl]
  have t1 : ∀ M N : Matrix d d ℂ, trace (U * M * star U * (U * N * star U)) = trace (M * N) :=
    fun M N ↦ by
      rw [show U * M * star U * (U * N * star U) = U * (M * N) * star U by
        rw [Matrix.mul_assoc (U * M), ← Matrix.mul_assoc (star U), ← Matrix.mul_assoc (star U), hUU,
          Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc], trace_conj hUm]
  have t2 : ∀ M : Matrix d d ℂ, trace ((A : Matrix d d ℂ) * (U * M * star U)) =
      trace (star U * (A : Matrix d d ℂ) * U * M) := fun M ↦ by
    conv_lhs => rw [hconj (A : Matrix d d ℂ)]
    exact t1 _ _
  rw [t1, t2, Matrix.trace, Matrix.trace, Complex.re_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Matrix.mul_apply, Matrix.mul_apply, Complex.re_sum,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [diagS, fderiv_matPow_diagonal_apply _ hpos, fderiv_matPow_diagonal_apply _ hpos,
    Matrix.of_apply, cMC_fGI h0 h1 (hpos j) (hpos i), powKernel_comm (1 / p) (l j)]
  generalize (star U * (A : Matrix d d ℂ) * U) i j = a
  generalize (star U * (B : Matrix d d ℂ) * U) j i = b
  generalize powKernel (1 / p) (l i) (l j) = c
  generalize powKernel (1 - 1 / p) (l j) (l i) = e
  generalize (1 / p * (1 - 1 / p))⁻¹ = k
  rw [show (c : ℂ) * a * ((e : ℂ) * b) = ((c * e : ℝ) : ℂ) * (a * b) by push_cast; ring,
    show a * (((k * (c * e) : ℝ) : ℂ) * b) = ((k * (c * e) : ℝ) : ℂ) * (a * b) by ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

/-- The scalar curvature at `0` depends only on the metric near `0`. -/
theorem scalarCurvature_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {G G' : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} (h : G =ᶠ[𝓝 x] G') :
    scalarCurvature G x = scalarCurvature G' x := by
  have hc : christoffel G =ᶠ[𝓝 x] christoffel G' := by
    filter_upwards [h.eventually_nhds] with y hy
    have hy' : G =ᶠ[𝓝 y] G' := hy
    simp only [christoffel, hy'.fderiv_eq, hy'.self_of_nhds]
  have hR : riemann G x = riemann G' x := by
    simp only [riemann, hc.fderiv_eq, hc.self_of_nhds]
  rw [scalarCurvature, scalarCurvature, ricci, ricci, hR, h.self_of_nhds]

/-- Two fields that are both the `WYD(p)` metric have the same scalar curvature. -/
theorem IsWYD.scalarCurvature_eq {p : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) {ρ : Matrix d d ℂ}
    (hρ : ρ.PosDef)
    {G : tracelessHermitian d → tracelessHermitian d →L[ℝ] tracelessHermitian d →L[ℝ] ℝ}
    (hG : IsWYD p ρ G) :
    scalarCurvature G 0 = scalarCurvature (wydMetric (1 / p) (tracelessHermitian d) ρ) 0 := by
  refine scalarCurvature_congr ?_
  filter_upwards [eventually_posDef_chart (V := tracelessHermitian d) hρ fun v hv ↦
    (mem_tracelessHermitian.1 hv).1] with z hz
  ext A B
  rw [hG z hz, wydMetric_eq h0 h1 ρ z hz]

end CLR

/-! ### The order -/

theorem sortInc_comp_perm {n : ℕ} (x : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    Majorization.sortInc (x ∘ e) = Majorization.sortInc x := by
  rw [Majorization.sortInc, Majorization.sortInc]
  exact Tuple.comp_perm_comp_sort_eq_comp_sort

theorem sum_decr_lt {n : ℕ} (x : Fin n → ℝ) {k : ℕ} (hk : k ≤ n) :
    ∑ i with (i : Fin n).val < n - k, decr x i =
      ∑ i, x i - ∑ i ∈ Finset.range k, Majorization.toSeq (Majorization.sortInc x) i := by
  have e1 : ∑ i with (i : Fin n).val < n - k, decr x i =
      ∑ i with ¬ (i : Fin n).val < k, Majorization.sortInc x i := by
    refine Finset.sum_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hi ⊢; omega
    · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at hi ⊢; omega
    · intro i _; exact Fin.rev_rev i
    · intro i _; exact Fin.rev_rev i
    · intro i _; rfl
  have e2 : ∑ i ∈ Finset.range k, Majorization.toSeq (Majorization.sortInc x) i =
      ∑ i with (i : Fin n).val < k, Majorization.sortInc x i := by
    rw [Finset.sum_filter]
    have e3 : ∑ i ∈ Finset.range k, Majorization.toSeq (Majorization.sortInc x) i =
        ∑ i ∈ Finset.range n, if i < k then Majorization.toSeq (Majorization.sortInc x) i else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext i; simp only [Finset.mem_range, Finset.mem_filter]; omega
    rw [e3, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Majorization.toSeq_val]
  rw [e1, e2, ← Majorization.sum_sortInc x,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n ↦ i.val < k)]
  ring

theorem sum_decr {n : ℕ} (x : Fin n → ℝ) : ∑ i, decr x i = ∑ i, x i := by
  rw [← Majorization.sum_sortInc x]
  exact Equiv.sum_comp Fin.revPerm (Majorization.sortInc x)

/-- Definition 2.3 is the majorization of the main theorem. -/
theorem moreMixed_iff {n : ℕ} (x y : Fin n → ℝ) : MoreMixed x y ↔ IsMajorizedBy x y := by
  rw [MoreMixed, IsMajorizedBy, sum_decr, sum_decr]
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨h', fun k hk ↦ ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · have := h (n - k) (by omega)
      rw [sum_decr_lt x hk, sum_decr_lt y hk] at this
      linarith
  · rintro ⟨h', h⟩
    refine ⟨fun k hk ↦ ?_, h'⟩
    have := h (n - k) (by omega)
    have e : k = n - (n - k) := by omega
    rw [e, sum_decr_lt x (by omega), sum_decr_lt y (by omega)]
    linarith

theorem IsMajorizedBy.comp_equiv {m n : ℕ} {x y : Fin n → ℝ} (h : IsMajorizedBy x y)
    (e : Fin m ≃ Fin n) : IsMajorizedBy (x ∘ e) (y ∘ e) := by
  obtain rfl : m = n := by simpa using Fintype.card_congr e
  refine ⟨?_, ?_⟩
  · rw [← Majorization.sum_sortInc, ← Majorization.sum_sortInc (y ∘ e), sortInc_comp_perm,
      sortInc_comp_perm, Majorization.sum_sortInc, Majorization.sum_sortInc, h.1]
  · rw [sortInc_comp_perm, sortInc_comp_perm]; exact h.2

/-! ### The conjecture -/

theorem range_of_p {p : ℝ} (hp : p ≤ -1 ∨ 1 / 2 ≤ p) : -1 ≤ 1 / p ∧ 1 / p ≤ 2 := by
  rcases hp with hp | hp
  · have : p < 0 := by linarith
    constructor
    · rw [le_div_iff_of_neg this]; linarith
    · rw [div_le_iff_of_neg this]; linarith
  · have : 0 < p := by linarith
    constructor
    · rw [le_div_iff₀ this]; linarith
    · rw [div_le_iff₀ this]; linarith

section Main

variable {n : ℕ} {ρ σ : Matrix (Fin n) (Fin n) ℂ}

/-- The strict form, in charts. -/
theorem wyd_strictly_chart {p : ℝ} (hp : p ≤ -1 ∨ 1 / 2 ≤ p) (h1 : p ≠ 1) (h2 : p ≠ 2) (hρ : ρ.PosDef)
    (hσ : σ.PosDef) (hρt : ρ.trace = 1) (hσt : σ.trace = 1)
    (hmix : MoreMixed hρ.1.eigenvalues hσ.1.eigenvalues)
    (hne : ∀ τ : Equiv.Perm (Fin n), hρ.1.eigenvalues ∘ τ ≠ hσ.1.eigenvalues)
    {G G' : tracelessHermitian (Fin n) →
      tracelessHermitian (Fin n) →L[ℝ] tracelessHermitian (Fin n) →L[ℝ] ℝ}
    (hG : IsWYD p ρ G) (hG' : IsWYD p σ G') : scalarCurvature G' 0 < scalarCurvature G 0 := by
  have h0 : p ≠ 0 := by rcases hp with hp | hp <;> intro h <;> linarith
  obtain ⟨hm, hM⟩ := range_of_p hp
  rw [hG.scalarCurvature_eq h0 h1 hρ, hG'.scalarCurvature_eq h0 h1 hσ]
  refine wyd_curvature_lt_of_isMajorizedBy hm hM (one_div_ne_zero h0) ?_ ?_ hρ hσ hρt hσt
    (IsMajorizedBy.comp_equiv ((moreMixed_iff _ _).1 hmix) _) hne
  · intro h; rw [div_eq_iff h0, one_mul] at h; exact h1 h.symm
  · intro h
    have : 1 / p = 1 / 2 := by linarith
    rw [div_eq_div_iff h0 two_ne_zero] at this
    exact h2 (by linarith)

/-- At `p = 2` (Wigner–Yanase) the scalar curvature is constant, `¼(n² - 1)(n² - 2)`: the value for the
sphere of radius `2` and dimension `n² - 1`. -/
theorem scalarCurvature_wigner_yanase (hρ : ρ.PosDef) (hρt : ρ.trace = 1)
    {G : tracelessHermitian (Fin n) →
      tracelessHermitian (Fin n) →L[ℝ] tracelessHermitian (Fin n) →L[ℝ] ℝ}
    (hG : IsWYD 2 ρ G) : scalarCurvature G 0 = ((n : ℝ) ^ 2 - 1) * ((n : ℝ) ^ 2 - 2) / 4 := by
  rw [hG.scalarCurvature_eq two_ne_zero (by norm_num) hρ,
    scalarCurvature_wydMetric (by norm_num) (by norm_num) hρ hρt, Fintype.card_fin]
  have hcub : ∀ x k y : ℝ, cubK (1 / 2) x k y = 0 := fun x k y ↦ by
    rw [cubK, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]; ring
  have hcurv : ∀ x y z : ℝ, curvK (1 / 2) x y z = 0 := fun x y z ↦ by
    rw [curvK, hcub, hcub, hcub]; simp
  have hhs : ∀ x y z : ℝ, wydHs (1 / 2) x y z = 0 := fun x y z ↦ by
    rw [wydHs, hsL, hcurv, hcurv, hcurv]; simp
  simp only [curvSum, hhs, Finset.sum_const_zero]
  ring

/-- The non-strict form, in charts; equal spectra are included. -/
theorem wyd_schurIncreasing_chart {p : ℝ} (hp : p ≤ -1 ∨ 1 / 2 ≤ p) (h1 : p ≠ 1) (hρ : ρ.PosDef)
    (hσ : σ.PosDef) (hρt : ρ.trace = 1) (hσt : σ.trace = 1)
    (hmix : MoreMixed hρ.1.eigenvalues hσ.1.eigenvalues)
    {G G' : tracelessHermitian (Fin n) →
      tracelessHermitian (Fin n) →L[ℝ] tracelessHermitian (Fin n) →L[ℝ] ℝ}
    (hG : IsWYD p ρ G) (hG' : IsWYD p σ G') : scalarCurvature G' 0 ≤ scalarCurvature G 0 := by
  have h0 : p ≠ 0 := by rcases hp with hp | hp <;> intro h <;> linarith
  by_cases h2 : p = 2
  · subst h2
    rw [scalarCurvature_wigner_yanase hρ hρt hG, scalarCurvature_wigner_yanase hσ hσt hG']
  by_cases hne : ∀ τ : Equiv.Perm (Fin n), hρ.1.eigenvalues ∘ τ ≠ hσ.1.eigenvalues
  · exact (wyd_strictly_chart hp h1 h2 hρ hσ hρt hσt hmix hne hG hG').le
  · push Not at hne
    obtain ⟨τ, hτ⟩ := hne
    have hb1 : 1 / p ≠ 1 := by intro h; rw [div_eq_iff h0, one_mul] at h; exact h1 h.symm
    rw [hG.scalarCurvature_eq h0 h1 hρ, hG'.scalarCurvature_eq h0 h1 hσ,
      scalarCurvature_wydMetric (one_div_ne_zero h0) hb1 hρ hρt,
      scalarCurvature_wydMetric (one_div_ne_zero h0) hb1 hσ hσt, ← hτ, curvSum_comp_equiv]

end Main

section Global

variable {n : ℕ} {p : ℝ} {g : FormField n}

theorem coe_add_mem {ρ : Matrix (Fin n) (Fin n) ℂ} (hρt : ρ.trace = 1) {z : tracelessHermitian (Fin n)}
    (hz : ((z : Matrix (Fin n) (Fin n) ℂ) + ρ).PosDef) : (z : Matrix (Fin n) (Fin n) ℂ) + ρ ∈ density n :=
  ⟨hz, by rw [Matrix.trace_add, (mem_tracelessHermitian.1 z.2).2, hρt, zero_add]⟩

theorem IsWYDMetric.chart (hg : IsWYDMetric p g) {ρ : Matrix (Fin n) (Fin n) ℂ} (hρt : ρ.trace = 1) :
    IsWYD p ρ fun z ↦ g ((z : Matrix (Fin n) (Fin n) ℂ) + ρ) :=
  fun _ hz ↦ hg _ (coe_add_mem hρt hz)

/-- The scalar curvature is that of one fixed chart `z ↦ ρ₀ + z`, whatever `ρ₀`. -/
theorem scal_eq_chart (g : FormField n) (ρ₀ : Matrix (Fin n) (Fin n) ℂ) (z : tracelessHermitian (Fin n)) :
    scal g ((z : Matrix (Fin n) (Fin n) ℂ) + ρ₀) =
      scalarCurvature (fun y : tracelessHermitian (Fin n) ↦ g ((y : Matrix (Fin n) (Fin n) ℂ) + ρ₀)) z := by
  have key : ∀ (G : tracelessHermitian (Fin n) →
      tracelessHermitian (Fin n) →L[ℝ] tracelessHermitian (Fin n) →L[ℝ] ℝ),
      scalarCurvature (fun y ↦ G (z + y)) 0 = scalarCurvature G z := fun G ↦ by
    have h : christoffel (fun y ↦ G (z + y)) = fun x ↦ christoffel G (z + x) := by
      funext x
      simp only [christoffel, fderiv_comp_add_left]
    simp only [scalarCurvature, ricci, riemann, h, fderiv_comp_add_left, add_zero]
  rw [← key, scal]
  congr 1
  funext y
  congr 1
  push_cast
  abel

/-- **The scalar curvature of the `WYD(p)` metric is Schur-increasing on `D¹ₙ`**, for every `n`, `p ≤ -1`
and `p ≥ 1/2`, `p ≠ 1`. -/
theorem wyd_schurIncreasing (hp : p ≤ -1 ∨ 1 / 2 ≤ p) (h1 : p ≠ 1) (hg : IsWYDMetric p g) :
    SchurIncreasingOn (density n) (scal g) := by
  rintro A ⟨hA, hAt⟩ B ⟨hB, hBt⟩ ⟨_, _, hmix⟩
  exact wyd_schurIncreasing_chart hp h1 hA hB hAt hBt hmix (hg.chart hAt) (hg.chart hBt)

/-- **It is strictly Schur-increasing**, for the same `p` except `p = 2`, where it is constant. -/
theorem wyd_strictly (hp : p ≤ -1 ∨ 1 / 2 ≤ p) (h1 : p ≠ 1) (h2 : p ≠ 2) (hg : IsWYDMetric p g) :
    StrictSchurIncreasingOn (density n) (scal g) := by
  rintro A ⟨hA, hAt⟩ B ⟨hB, hBt⟩ ⟨_, _, hmix⟩ hne
  exact wyd_strictly_chart hp h1 h2 hA hB hAt hBt hmix (fun τ h ↦ hne ⟨_, _, τ, h⟩)
    (hg.chart hAt) (hg.chart hBt)

/-- Theorem 7.2: at `p = 2` the scalar curvature is the constant `¼(n² - 1)(n² - 2)`. -/
theorem scal_wigner_yanase (hg : IsWYDMetric 2 g) {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ ∈ density n) :
    scal g ρ = ((n : ℝ) ^ 2 - 1) * ((n : ℝ) ^ 2 - 2) / 4 :=
  scalarCurvature_wigner_yanase hρ.1 hρ.2 (hg.chart hρ.2)

end Global

/-- **Conjecture 8.1 of Gibilisco–Isola**: there is `ε > 0` such that for `p ∈ (1, 1 + ε)` the scalar
curvature of the `WYD(p)` metric is Schur-increasing. Here `ε = 1`, the same for every `n`; by
`wyd_schurIncreasing` any `ε` would do. -/
theorem conjecture81 : ∃ ε > 0, ∀ p ∈ Ioo (1 : ℝ) (1 + ε), ∀ (n : ℕ) (g : FormField n),
    IsWYDMetric p g → SchurIncreasingOn (density n) (scal g) :=
  ⟨1, one_pos, fun _ hp _ _ hg ↦ wyd_schurIncreasing (Or.inr (by linarith [hp.1])) hp.1.ne' hg⟩

/-! ### Sanity checks -/

theorem exists_isWYD {n : ℕ} {p : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ G, IsWYD p ρ G := ⟨_, wydMetric_eq h0 h1 ρ⟩

/-- The metric exists, as a field of bilinear forms, for `p ≠ 0, 1`. -/
theorem exists_isWYDMetric {n : ℕ} {p : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) :
    ∃ g : FormField n, IsWYDMetric p g :=
  ⟨fun ρ ↦ wydMetric (1 / p) (tracelessHermitian (Fin n)) ρ 0, fun ρ hρ A B ↦ by
    simpa using wydMetric_eq h0 h1 ρ 0 (by simpa using hρ.1) A B⟩

theorem mul_powKernel_pos {s x y : ℝ} (hs : s ≠ 0) (hx : 0 < x) (hy : 0 < y) :
    0 < s * powKernel s x y := by
  rcases lt_trichotomy x y with h | rfl | h
  · rw [powKernel_of_ne h.ne, ← mul_div_assoc]
    rcases lt_or_gt_of_ne hs with h' | h'
    · exact div_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos h' (sub_pos.2 (Real.rpow_lt_rpow_of_neg hx h h'))) (sub_neg.2 h)
    · exact div_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg h' (sub_neg.2 (Real.rpow_lt_rpow hx.le h h'))) (sub_neg.2 h)
  · rw [powKernel_self, ← mul_assoc]
    exact mul_pos (mul_self_pos.2 hs) (Real.rpow_pos_of_pos hx _)
  · rw [powKernel_of_ne h.ne', ← mul_div_assoc]
    rcases lt_or_gt_of_ne hs with h' | h'
    · exact div_pos (mul_pos_of_neg_of_neg h' (sub_neg.2 (Real.rpow_lt_rpow_of_neg hy h h')))
        (sub_pos.2 h)
    · exact div_pos (mul_pos h' (sub_pos.2 (Real.rpow_lt_rpow hy.le h h'))) (sub_pos.2 h)

theorem cMC_fGI_pos {p x y : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) (hx : 0 < x) (hy : 0 < y) :
    0 < cMC (fGI p) x y := by
  have hb : 1 / p ≠ 0 := one_div_ne_zero h0
  have hb1 : 1 - 1 / p ≠ 0 := by
    rw [sub_ne_zero]; intro h; rw [eq_div_iff h0, one_mul] at h; exact h1 h
  have a := mul_powKernel_pos hb hx hy
  have b := mul_powKernel_pos hb1 hx hy
  rw [cMC_fGI h0 h1 hx hy]
  set s := 1 / p
  have e : (s * (1 - s))⁻¹ * (powKernel s x y * powKernel (1 - s) x y) =
      (s * powKernel s x y) * ((1 - s) * powKernel (1 - s) x y) * ((s * (1 - s))⁻¹) ^ 2 := by
    field_simp
  rw [e]
  exact mul_pos (mul_pos a b) (sq_pos_iff.2 (inv_ne_zero (mul_ne_zero hb hb1)))

theorem cMC_fGI_comm {p x y : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) (hx : 0 < x) (hy : 0 < y) :
    cMC (fGI p) x y = cMC (fGI p) y x := by
  rw [cMC_fGI h0 h1 hx hy, cMC_fGI h0 h1 hy hx, powKernel_comm _ x, powKernel_comm _ x]

/-- The metric in an eigenbasis: `Tr (A c(L, R)(B)) = Σ c(λⱼ, λᵢ) aᵢⱼ bⱼᵢ`. -/
theorem trace_cLR {n : ℕ} (f : ℝ → ℝ) {ρ : Matrix (Fin n) (Fin n) ℂ} (h : ρ.IsHermitian)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace (A * cLR f ρ B)).re = ∑ i, ∑ j, cMC f (h.eigenvalues j) (h.eigenvalues i) *
      ((star (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * A * (h.eigenvectorUnitary :
          Matrix (Fin n) (Fin n) ℂ)) i j *
        (star (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * B * (h.eigenvectorUnitary :
          Matrix (Fin n) (Fin n) ℂ)) j i).re := by
  set U := (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  rw [cLR, dite_eq_left h, ← hU, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.of_apply, ← Complex.re_ofReal_mul]
  congr 1
  ring

/-- The `WYD(p)` metric is symmetric. -/
theorem IsWYDMetric.symm {n : ℕ} {p : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) {g : FormField n}
    (hg : IsWYDMetric p g) {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ ∈ density n)
    (A B : tracelessHermitian (Fin n)) : g ρ A B = g ρ B A := by
  rw [hg ρ hρ, hg ρ hρ, trace_cLR _ hρ.1.1, trace_cLR _ hρ.1.1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [cMC_fGI_comm h0 h1 (hρ.1.eigenvalues_pos i) (hρ.1.eigenvalues_pos j),
    mul_comm (_ : ℂ) (_ : ℂ)]

/-- The `WYD(p)` metric is positive definite at every density matrix: it is a Riemannian metric. -/
theorem IsWYDMetric.pos {n : ℕ} {p : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) {g : FormField n}
    (hg : IsWYDMetric p g) {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ ∈ density n)
    {A : tracelessHermitian (Fin n)} (hA : A ≠ 0) : 0 < g ρ A A := by
  rw [hg ρ hρ, trace_cLR _ hρ.1.1]
  set U := (hρ.1.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set M := star U * (A : Matrix (Fin n) (Fin n) ℂ) * U with hM
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hρ.1.1.eigenvectorUnitary.2
  have hAh : star (A : Matrix (Fin n) (Fin n) ℂ) = A := (mem_tracelessHermitian.1 A.2).1
  have hMh : star M = M := by
    rw [hM, star_mul, star_mul, star_star, hAh, Matrix.mul_assoc]
  have hsq : ∀ i j, (M i j * M j i).re = Complex.normSq (M i j) := fun i j ↦ by
    have : M j i = star (M i j) := by
      conv_lhs => rw [← hMh]
      rfl
    rw [this, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  have hMne : M ≠ 0 := fun h ↦ hA (Subtype.ext (by
    have : (A : Matrix (Fin n) (Fin n) ℂ) = U * M * star U := by
      rw [hM, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, hUU', Matrix.mul_one,
        ← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [this, h, Matrix.mul_zero, Matrix.zero_mul]; rfl))
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hMne (by ext i j; exact hcon i j)
  have hc : ∀ i j, 0 < cMC (fGI p) (hρ.1.1.eigenvalues j) (hρ.1.1.eigenvalues i) := fun i j ↦
    cMC_fGI_pos h0 h1 (hρ.1.eigenvalues_pos j) (hρ.1.eigenvalues_pos i)
  have hnn : ∀ i j, 0 ≤ cMC (fGI p) (hρ.1.1.eigenvalues j) (hρ.1.1.eigenvalues i) *
      (M i j * M j i).re := fun i j ↦ by
    rw [hsq]; exact mul_nonneg (hc i j).le (Complex.normSq_nonneg _)
  refine Finset.sum_pos' (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn i j) ⟨i, Finset.mem_univ _, ?_⟩
  refine Finset.sum_pos' (fun j _ ↦ hnn i j) ⟨j, Finset.mem_univ _, ?_⟩
  rw [hsq]
  exact mul_pos (hc i j) (Complex.normSq_pos.2 hij)

/-- `f_p = f_p̃`. -/
theorem fGI_conj {p : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) (x : ℝ) : fGI (conj p) x = fGI p x := by
  have hm : p - 1 ≠ 0 := sub_ne_zero.2 h1
  have hc1 : conj p ≠ 1 := by
    intro h; rw [conj, div_eq_one_iff_eq hm] at h; linarith
  have hq : conj (conj p) = p := by
    unfold conj
    have : p / (p - 1) - 1 = 1 / (p - 1) := by field_simp; ring
    rw [this]
    field_simp
  unfold fGI
  rw [hq]
  simp only [h1, hc1, ite_false]
  split_ifs
  · rfl
  · ring

/-- At `p = 1` the Morozova–Chentsov function is that of the Kubo–Mori metric. -/
theorem cMC_fGI_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x ≠ y) :
    cMC (fGI 1) x y = (Real.log x - Real.log y) / (x - y) := by
  have hne : x / y ≠ 1 := fun e ↦ h ((div_eq_one_iff_eq hy.ne').1 e)
  have e : y * ((x / y - 1) / Real.log (x / y)) = (x - y) / Real.log (x / y) := by field_simp
  rw [cMC, fGI, ite_eq_right hne, ite_eq_left rfl, e, one_div_div, Real.log_div hx.ne' hy.ne']

/-- The uniform distribution is more mixed than every other. -/
theorem moreMixed_uniform {n : ℕ} (hn : 0 < n) {y : Fin n → ℝ} (hy : ∑ i, y i = 1) :
    MoreMixed (fun _ ↦ (n : ℝ)⁻¹) y := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hd : ∀ i : Fin n, decr (fun _ : Fin n ↦ (n : ℝ)⁻¹) i = (n : ℝ)⁻¹ := fun _ ↦ rfl
  refine ⟨fun k _ ↦ ?_, ?_⟩
  · have hmono : Monovary (fun i : Fin n ↦ if i.val < k then (1 : ℝ) else 0) (decr y) := by
      intro i j hij
      have hji : j < i := by
        by_contra h
        exact absurd (antitone_decr y (not_lt.1 h)) (not_le.2 hij)
      dsimp only
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (lt_trans (Fin.lt_def.1 hji) h1) h2
      · exact zero_le_one
      · exact le_rfl
    have h := hmono.sum_mul_sum_le_card_mul_sum
    rw [sum_decr, hy, mul_one, Fintype.card_fin] at h
    simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter] at h
    simp only [hd]
    have e : ∑ i with (i : Fin n).val < k, (n : ℝ)⁻¹ =
        (n : ℝ)⁻¹ * ∑ i with (i : Fin n).val < k, (1 : ℝ) := by
      rw [Finset.mul_sum]; simp
    rw [e, inv_mul_le_iff₀ hn']
    exact h
  · rw [sum_decr, sum_decr, hy]
    simp [hn'.ne']

theorem eigenvalues_uniform {n : ℕ} {c : ℝ} (h : ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian)
    (i : Fin n) : h.eigenvalues i = c := by
  have e := h.mulVec_eigenvectorBasis i
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at e
  have hne : (h.eigenvectorBasis i).ofLp ≠ 0 := fun h0 ↦ by
    have := h.eigenvectorBasis.orthonormal.ne_zero i
    exact this (by ext j; exact congrFun h0 j)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have := congrFun e j
  simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul] at this
  exact_mod_cast (mul_right_cancel₀ hj this).symm

/-- The curvature at the most mixed state, in charts. -/
theorem curvature_lt_uniform_chart {n : ℕ} {p : ℝ} (hp : p ≤ -1 ∨ 1 / 2 ≤ p) (h1 : p ≠ 1) (h2 : p ≠ 2)
    (hn : 0 < n) {σ : Matrix (Fin n) (Fin n) ℂ} (hσ : σ.PosDef) (hσt : σ.trace = 1)
    (hne : σ ≠ ((n : ℝ)⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
    {G G' : tracelessHermitian (Fin n) →
      tracelessHermitian (Fin n) →L[ℝ] tracelessHermitian (Fin n) →L[ℝ] ℝ}
    (hG : IsWYD p (((n : ℝ)⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) G) (hG' : IsWYD p σ G') :
    scalarCurvature G' 0 < scalarCurvature G 0 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hc : (((n : ℝ)⁻¹ : ℂ)) = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have hρ : (((n : ℝ)⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
    rw [hc]
    exact Matrix.PosDef.one.smul (Complex.zero_lt_real.2 (inv_pos.2 hn'))
  have hρt : (((n : ℝ)⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).trace = 1 := by
    have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    simp [this]
  have hev : hρ.1.eigenvalues = fun _ ↦ (n : ℝ)⁻¹ := by
    funext i
    have : ∀ (c : ℂ) (h : (c • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian),
        c = (((n : ℝ)⁻¹ : ℝ) : ℂ) → h.eigenvalues i = (n : ℝ)⁻¹ := by
      rintro c h rfl; exact eigenvalues_uniform h i
    exact this _ hρ.1 hc
  have hsum : ∑ i, hσ.1.eigenvalues i = 1 := by
    have := hσ.1.trace_eq_sum_eigenvalues
    rw [hσt] at this
    have h' : ((∑ i, hσ.1.eigenvalues i : ℝ) : ℂ) = 1 := by rw [this]; push_cast; rfl
    exact Complex.ofReal_eq_one.1 h'
  refine wyd_strictly_chart hp h1 h2 hρ hσ hρt hσt ?_ ?_ hG hG'
  · rw [hev]; exact moreMixed_uniform hn hsum
  · intro τ h
    rw [hev] at h
    apply hne
    have hs : hσ.1.eigenvalues = fun _ ↦ (n : ℝ)⁻¹ := h.symm
    have hUU' := Matrix.mem_unitaryGroup_iff.1 hσ.1.eigenvectorUnitary.2
    have e := hσ.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, hs] at e
    have e2 : Matrix.diagonal (RCLike.ofReal ∘ fun _ : Fin n ↦ (n : ℝ)⁻¹) =
        ((n : ℝ)⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.smul_one_eq_diagonal]; congr 1; funext i; simp
    rw [e2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at e
    exact e.trans (by rw [hUU'])

/-- The state `I/n` has strictly larger scalar curvature than every other density matrix, for `p ≠ 1, 2`
as in `wyd_strictly`: the hypotheses of the theorems can be met, and the direction cannot be reversed. -/
theorem scal_lt_uniform {n : ℕ} {p : ℝ} (hp : p ≤ -1 ∨ 1 / 2 ≤ p) (h1 : p ≠ 1) (h2 : p ≠ 2)
    (hn : 0 < n) {g : FormField n} (hg : IsWYDMetric p g) {σ : Matrix (Fin n) (Fin n) ℂ}
    (hσ : σ ∈ density n) (hne : σ ≠ ((n : ℝ)⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    scal g σ < scal g (((n : ℝ)⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  have ht : (((n : ℝ)⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).trace = 1 := by
    have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    simp [this]
  exact curvature_lt_uniform_chart hp h1 h2 hn hσ.1 hσ.2 hne (hg.chart ht) (hg.chart hσ.2)

/-- The strict form fails at `p = 2`: it needs `p ≠ 2`. -/
theorem not_strict_at_two {n : ℕ} {g : FormField n} (hg : IsWYDMetric 2 g)
    {ρ σ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ ∈ density n) (hσ : σ ∈ density n) :
    scal g ρ = scal g σ := by
  rw [scal_wigner_yanase hg hρ, scal_wigner_yanase hg hσ]

/-- The order has the right direction: `(1, 0)` is not more mixed than `(½, ½)`. -/
theorem not_moreMixed : ¬ MoreMixed ![(1 : ℝ), 0] ![1 / 2, 1 / 2] := by
  rintro ⟨h, _⟩
  have h1 := h 1 (by norm_num)
  have e : ∀ x : Fin 2 → ℝ, ∑ i with (i : Fin 2).val < 1, decr x i = decr x 0 := fun x ↦ by
    rw [show (Finset.univ.filter fun i : Fin 2 ↦ i.val < 1) = {0} by decide, Finset.sum_singleton]
  rw [e, e] at h1
  have a : ∀ (x : Fin 2 → ℝ) (i : Fin 2), x i ≤ decr x 0 := fun x i ↦ by
    have := antitone_decr x (Fin.zero_le ((Tuple.sort x).symm i).rev)
    simp only [decr, Function.comp, Fin.rev_rev, Equiv.apply_symm_apply] at this
    exact this
  have b : decr ![(1 : ℝ) / 2, 1 / 2] 0 = 1 / 2 := by
    have : ∀ k : Fin 2, (![(1 : ℝ) / 2, 1 / 2]) k = 1 / 2 := fun k ↦ by fin_cases k <;> rfl
    exact this _
  have h3 : (1 : ℝ) ≤ decr ![(1 : ℝ), 0] 0 := a ![(1 : ℝ), 0] 0
  rw [b] at h1
  linarith

end WYD.Literal
