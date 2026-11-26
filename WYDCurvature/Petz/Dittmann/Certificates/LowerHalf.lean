/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Petz.Dittmann.Certificates.Cones

/-!
# Sector certificates: the cones with `B ≤ A`

The numerators `spaceNum₁₁` and `spaceNum₃` are `≤ 0` on the three cones with `B ≤ A` (`y ≤ x`):
`0 ≤ B ≤ A`, `B ≤ 0 ≤ A` and `B ≤ A ≤ 0`.

## Main statements

* `PetzCurvature.spaceNum₁₁_zeroBA`
* `PetzCurvature.spaceNum₁₁_bZeroA`
* `PetzCurvature.spaceNum₁₁_bAZero`
* `PetzCurvature.spaceNum₃_zeroBA`
* `PetzCurvature.spaceNum₃_bZeroA`
* `PetzCurvature.spaceNum₃_bAZero`

## References

* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]
-/

namespace PetzCurvature

open ExpPolynomial

sector_certificate spaceNum₁₁_zeroBA zeroBA spaceNum₁₁ 18 33
sector_certificate spaceNum₁₁_bZeroA bZeroA spaceNum₁₁ 18 33
sector_certificate spaceNum₁₁_bAZero bAZero spaceNum₁₁ 17 18

sector_certificate spaceNum₃_zeroBA zeroBA spaceNum₃ 39 42
sector_certificate spaceNum₃_bZeroA bZeroA spaceNum₃ 35 42
sector_certificate spaceNum₃_bAZero bAZero spaceNum₃ 32 35

end PetzCurvature
