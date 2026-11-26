/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Petz.Dittmann.Certificates.Cones
import WYDCurvature.Petz.Dittmann.Certificates.LowerHalf  -- build order only: one certificate check at a time

/-!
# Sector certificates: the cones with `A ≤ B`

The numerators `spaceNum₁₁` and `spaceNum₃` are `≤ 0` on the three cones with `A ≤ B` (`x ≤ y`):
`0 ≤ A ≤ B`, `A ≤ 0 ≤ B` and `A ≤ B ≤ 0`.

## Main statements

* `PetzCurvature.spaceNum₁₁_zeroAB`
* `PetzCurvature.spaceNum₁₁_aZeroB`
* `PetzCurvature.spaceNum₁₁_aBZero`
* `PetzCurvature.spaceNum₃_zeroAB`
* `PetzCurvature.spaceNum₃_aZeroB`
* `PetzCurvature.spaceNum₃_aBZero`

## References

* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]
-/

namespace PetzCurvature

open ExpPolynomial

sector_certificate spaceNum₁₁_zeroAB zeroAB spaceNum₁₁ 19 20
sector_certificate spaceNum₁₁_aZeroB aZeroB spaceNum₁₁ 28 17
sector_certificate spaceNum₁₁_aBZero aBZero spaceNum₁₁ 17 28

sector_certificate spaceNum₃_zeroAB zeroAB spaceNum₃ 39 42
sector_certificate spaceNum₃_aZeroB aZeroB spaceNum₃ 35 42
sector_certificate spaceNum₃_aBZero aBZero spaceNum₃ 32 35

end PetzCurvature
