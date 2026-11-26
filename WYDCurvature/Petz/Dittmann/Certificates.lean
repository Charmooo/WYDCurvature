/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Petz.Dittmann.Certificates.LowerHalf
import WYDCurvature.Petz.Dittmann.Certificates.UpperHalf

/-!
# The numerators of `∂₁₁hs` and `(∂₁ - ∂₂)²hs` are nonpositive

With `z = 1`, `x = e^A`, `y = e^B`, `a = A`, `b = B`, the plane of `(A, B)` is covered by the six
cones of the orderings of `A`, `B`, `0` (`spaceEval_nonpos_of_sectors`). On each cone both
numerators `spaceNum₁₁` and `spaceNum₃` are `≤ 0` by a kernel-checked certificate
(`Certificates/Cones.lean`, `Certificates/LowerHalf.lean`, `Certificates/UpperHalf.lean`); this
file assembles the twelve certificates.

## Main statements

* `PetzCurvature.spaceNum₁₁_nonpos_exp`, `PetzCurvature.spaceNum₃_nonpos_exp`: both
  numerators are `≤ 0` at `(e^A, e^B, 1, A, B)` for all `A`, `B`.

## References

* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]
-/

namespace PetzCurvature

/-- **The numerator of `∂₁₁hs` is `≤ 0`** at `(e^A, e^B, 1, A, B)`. -/
theorem spaceNum₁₁_nonpos_exp (A B : ℝ) :
    spaceEval spaceNum₁₁ (Real.exp A) (Real.exp B) 1 A B ≤ 0 :=
  spaceEval_nonpos_of_sectors
    (fun _ _ hp hq ↦ spaceNum₁₁_zeroBA hp hq (by simp [zeroBA]) (by simp [zeroBA]))
    (fun _ _ hp hq ↦ spaceNum₁₁_zeroAB hp hq (by simp [zeroAB]) (by simp [zeroAB]))
    (fun _ _ hp hq ↦ spaceNum₁₁_bZeroA hp hq (by simp [bZeroA]) (by simp [bZeroA]))
    (fun _ _ hp hq ↦ spaceNum₁₁_aZeroB hp hq (by simp [aZeroB]) (by simp [aZeroB]))
    (fun _ _ hp hq ↦ spaceNum₁₁_bAZero hp hq (by simp [bAZero]) (by simp [bAZero]; ring))
    (fun _ _ hp hq ↦ spaceNum₁₁_aBZero hp hq (by simp [aBZero]; ring) (by simp [aBZero])) A B

/-- **The numerator of `(∂₁ - ∂₂)²hs` is `≤ 0`** at `(e^A, e^B, 1, A, B)`. -/
theorem spaceNum₃_nonpos_exp (A B : ℝ) :
    spaceEval spaceNum₃ (Real.exp A) (Real.exp B) 1 A B ≤ 0 :=
  spaceEval_nonpos_of_sectors
    (fun _ _ hp hq ↦ spaceNum₃_zeroBA hp hq (by simp [zeroBA]) (by simp [zeroBA]))
    (fun _ _ hp hq ↦ spaceNum₃_zeroAB hp hq (by simp [zeroAB]) (by simp [zeroAB]))
    (fun _ _ hp hq ↦ spaceNum₃_bZeroA hp hq (by simp [bZeroA]) (by simp [bZeroA]))
    (fun _ _ hp hq ↦ spaceNum₃_aZeroB hp hq (by simp [aZeroB]) (by simp [aZeroB]))
    (fun _ _ hp hq ↦ spaceNum₃_bAZero hp hq (by simp [bAZero]) (by simp [bAZero]; ring))
    (fun _ _ hp hq ↦ spaceNum₃_aBZero hp hq (by simp [aBZero]; ring) (by simp [aBZero])) A B

end PetzCurvature
