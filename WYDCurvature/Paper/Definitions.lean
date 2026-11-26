/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.Curvature.Basic
import AlphaCurvature.Quantum.ClosedForm
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The definitions of Gibilisco–Isola

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

`WYDCurvature/Paper/Conjecture81.lean` states Conjecture 8.1 with these definitions and proves it,
and `WYDCurvature/Paper/Theorem61.lean` proves Theorem 6.1. This file imports no part of the proof.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder
open Matrix
open AlphaCurvature AlphaCurvature.Curvature AlphaCurvature.Quantum

namespace WYD.Paper

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

end WYD.Paper
