/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Petz.Dittmann.Space

/-!
# The six cones and the sector certificate

With `z = 1`, `x = e^A`, `y = e^B`, `a = A`, `b = B`, the plane of `(A, B)` is covered by the six
cones of the orderings of `A`, `B`, `0` (`spaceEval_nonpos_of_sectors`). This file names the cones
and defines the command `sector_certificate`, which states the five kernel checks of
`spaceEval_nonpos_of_checks` for a numerator on a cone, each proved by `decide +kernel`, and their
conclusion.

Each certificate has two depths `M` and `N`: the coefficients of `pᵐ qⁿ` with `m ≤ M` and `n ≤ N`
are checked one by one, and beyond them a few conditions on the top exponent bound the strips and
the corner (`ExpPolynomial.coef₂_nonneg_of_checks`). The depths are certificate data: the least at
which the checks pass, found by evaluation.

The certificates themselves are in `Certificates/LowerHalf.lean` (the cones with `B ≤ A`, that is
`y ≤ x`) and `Certificates/UpperHalf.lean` (`A ≤ B`), two modules that build in parallel.

## Main definitions

* `PetzCurvature.zeroBA`, …, `PetzCurvature.aBZero`: the six cones.
* `sector_certificate`: the certificate of a numerator on a cone.

## References

* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]
-/

namespace PetzCurvature

open ExpPolynomial

/-- The cone `0 ≤ B ≤ A`: `A = p + q`, `B = p`. -/
def zeroBA : Sector := ⟨1, 1, 1, 0⟩

/-- The cone `0 ≤ A ≤ B`: `A = p`, `B = p + q`. -/
def zeroAB : Sector := ⟨1, 0, 1, 1⟩

/-- The cone `B ≤ 0 ≤ A`: `A = q`, `B = -p`. -/
def bZeroA : Sector := ⟨0, 1, -1, 0⟩

/-- The cone `A ≤ 0 ≤ B`: `A = -p`, `B = q`. -/
def aZeroB : Sector := ⟨-1, 0, 0, 1⟩

/-- The cone `B ≤ A ≤ 0`: `A = -p`, `B = -p - q`. -/
def bAZero : Sector := ⟨-1, 0, -1, -1⟩

/-- The cone `A ≤ B ≤ 0`: `A = -p - q`, `B = -p`. -/
def aBZero : Sector := ⟨-1, -1, -1, 0⟩

open Lean in
/-- `sector_certificate n S P`: the five kernel checks of `spaceEval_nonpos_of_checks` for `P` on
the cone `S` at depths `M` and `N`, as the theorems `n_ident`, `n_rect`, `n_stripP`, `n_stripQ`,
`n_corner` (one `decide +kernel` each), and the conclusion `n`. -/
scoped macro "sector_certificate " n:ident S:term:max P:term:max M:num N:num : command => do
  let mk (s : String) := mkIdentFrom n (n.getId.appendAfter s)
  `(theorem $(mk "_ident") : Sector.identOk $S $P = true := by decide +kernel
    theorem $(mk "_rect") : rectOk (Sector.data $S $P) $M $N = true := by decide +kernel
    theorem $(mk "_stripP") : stripPOk (Sector.data $S $P) $M $N = true := by decide +kernel
    theorem $(mk "_stripQ") : stripQOk (Sector.data $S $P) $M $N = true := by decide +kernel
    theorem $(mk "_corner") : cornerOk (Sector.data $S $P) (groupsMaxE (Sector.data $S $P))
        (groupsMaxI (Sector.data $S $P)) $M $N = true := by decide +kernel
    theorem $n {p q A B : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
        (hA : A = (Sector.s₁ $S) * p + (Sector.t₁ $S) * q)
        (hB : B = (Sector.s₂ $S) * p + (Sector.t₂ $S) * q) :
        spaceEval $P (Real.exp A) (Real.exp B) 1 A B ≤ 0 :=
      spaceEval_nonpos_of_checks $S $(mk "_ident") $(mk "_rect") $(mk "_stripP") $(mk "_stripQ")
        $(mk "_corner") hp hq hA hB)

end PetzCurvature
