/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Newton

/-!
# Newton certificate for (65), position 0, `d < 1`

The exponents of the numerator, in increasing order. The kernel computes the Newton coefficients and
checks that they are polynomials in `t` with nonnegative coefficients. The check is cut into stages,
one theorem each, to keep the kernel's memory small.
-/

namespace WYD.Newton

namespace c65_0_1

def rows : List (Node × List (Node × PP)) := group (num65 par1 1 0 1 2)

def vs : List Node :=
  [(-2, -2), (-1, -3), (-2, 0), (-1, -1), (0, -2), (-2, 2), (1, -3), (-1, 1), (2, -4), (0, 0),
    (1, -1), (-1, 3), (2, -2), (0, 2), (3, -3), (1, 1), (2, 0), (3, -1), (1, 3), (4, -2),
    (2, 2), (3, 1), (4, 0), (2, 4), (5, -1), (3, 3), (4, 2), (5, 1)]

def u0 : List Node :=
  [(-5, -1), (-4, -2), (-3, -3), (-5, 1), (-2, -4), (-4, 0), (-1, -5), (-3, -1), (-2, -2),
    (-4, 2)]

def u1 : List Node :=
  [(-1, -3), (-3, 1), (0, -4), (-2, 0), (1, -5), (-1, -1), (-3, 3), (2, -6), (0, -2), (-2, 2)]

def u2 : List Node :=
  [(1, -3), (-1, 1), (2, -4), (0, 0), (-2, 4), (3, -5), (1, -1), (-1, 3), (2, -2), (0, 2)]

def u3 : List Node :=
  [(3, -3), (1, 1), (-1, 5), (4, -4), (2, 0), (0, 4), (3, -1), (1, 3), (4, -2), (2, 2)]

def u4 : List Node :=
  [(5, -3), (3, 1), (1, 5), (4, 0), (2, 4), (5, -1), (3, 3), (6, -2), (4, 2), (2, 6)]

def u5 : List Node :=
  [(5, 1), (3, 5), (4, 4), (5, 3), (6, 2)]

theorem h0 : part par1 u0 vs
    rows = true := by
  decide +kernel

theorem h1 : part par1 u1 vs
    (after par1 u0 rows) = true := by
  decide +kernel

theorem h2 : part par1 u2 vs
    (after par1 u1 (after par1 u0 rows)) = true := by
  decide +kernel

theorem h3 : part par1 u3 vs
    (after par1 u2 (after par1 u1 (after par1 u0 rows))) = true := by
  decide +kernel

theorem h4 : part par1 u4 vs
    (after par1 u3 (after par1 u2 (after par1 u1 (after par1 u0 rows)))) = true := by
  decide +kernel

theorem h5 : check2 par1 u5 vs
    (after par1 u4 (after par1 u3 (after par1 u2 (after par1 u1 (after par1 u0 rows))))) = true := by
  decide +kernel

end c65_0_1

theorem cert65_0_1 : ∃ us vs, check2 par1 us vs (group (num65 par1 1 0 1 2)) = true :=
  ⟨_, _, check2_append _ _ _ c65_0_1.h0
    (check2_append _ _ _ c65_0_1.h1
    (check2_append _ _ _ c65_0_1.h2
    (check2_append _ _ _ c65_0_1.h3
    (check2_append _ _ _ c65_0_1.h4
    (c65_0_1.h5)))))⟩

end WYD.Newton
