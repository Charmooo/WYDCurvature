/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.ForMathlib.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The lemma of `PetzCurvature/ForMathlib/Basic.lean` that AlphaCurvature's copy lacks. -/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The inverse of a diagonal matrix with nonzero real entries. -/
theorem inv_diagonal_ofReal {v : n → ℝ} (hv : ∀ i, v i ≠ 0) :
    (diagonal fun i ↦ (v i : ℂ))⁻¹ = diagonal fun i ↦ (((v i)⁻¹ : ℝ) : ℂ) := by
  refine inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  push_cast
  exact inv_mul_cancel₀ (by exact_mod_cast hv i)

end Matrix
