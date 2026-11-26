/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Newton.Basic
import WYDCurvature.Newton.Certificates.C65_0_1  -- build order only: one certificate check at a time

/-!
# Newton certificate for (65), position 0, `1 < d ≤ 3`

The exponents of the numerator, in increasing order. The kernel computes the Newton coefficients and
checks that they are polynomials in `t` with nonnegative coefficients. The check is cut into stages,
one theorem each, to keep the kernel's memory small.
-/

namespace WYD.Newton

namespace c65_0_2

def rows : List (Node × List (Node × PP)) := group (num65 par2 (-1) 0 1 2)

def vs : List Node :=
  [(-1, -3), (2, -4), (-2, -2), (1, -3), (0, -2), (3, -3), (-1, -1), (2, -2), (-2, 0),
    (1, -1), (4, -2), (0, 0), (3, -1), (-1, 1), (2, 0), (-2, 2), (5, -1), (1, 1), (4, 0),
    (0, 2), (3, 1), (-1, 3), (2, 2), (5, 1), (1, 3), (4, 2), (3, 3), (2, 4)]

def u0 : List Node :=
  [(-1, -5), (2, -6), (-2, -4), (1, -5), (-3, -3), (0, -4), (-4, -2), (3, -5), (-1, -3),
    (-5, -1)]

def u1 : List Node :=
  [(2, -4), (-2, -2), (1, -3), (-3, -1), (4, -4), (0, -2), (-4, 0), (3, -3), (-1, -1), (-5, 1)]

def u2 : List Node :=
  [(2, -2), (-2, 0), (5, -3), (1, -1), (-3, 1), (4, -2), (0, 0), (-4, 2), (3, -1), (-1, 1)]

def u3 : List Node :=
  [(6, -2), (2, 0), (-2, 2), (5, -1), (1, 1), (-3, 3), (4, 0), (0, 2), (3, 1), (-1, 3)]

def u4 : List Node :=
  [(2, 2), (-2, 4), (5, 1), (1, 3), (4, 2), (0, 4), (3, 3), (-1, 5), (6, 2), (2, 4)]

def u5 : List Node :=
  [(5, 3), (1, 5), (4, 4), (3, 5), (2, 6)]

theorem h0 : part par2 u0 vs
    rows = true := by
  decide +kernel

theorem h1 : part par2 u1 vs
    (after par2 u0 rows) = true := by
  decide +kernel

theorem h2 : part par2 u2 vs
    (after par2 u1 (after par2 u0 rows)) = true := by
  decide +kernel

theorem h3 : part par2 u3 vs
    (after par2 u2 (after par2 u1 (after par2 u0 rows))) = true := by
  decide +kernel

theorem h4 : part par2 u4 vs
    (after par2 u3 (after par2 u2 (after par2 u1 (after par2 u0 rows)))) = true := by
  decide +kernel

theorem h5 : check2 par2 u5 vs
    (after par2 u4 (after par2 u3 (after par2 u2 (after par2 u1 (after par2 u0 rows))))) = true := by
  decide +kernel

end c65_0_2

theorem cert65_0_2 : ∃ us vs, check2 par2 us vs (group (num65 par2 (-1) 0 1 2)) = true :=
  ⟨_, _, check2_append _ _ _ c65_0_2.h0
    (check2_append _ _ _ c65_0_2.h1
    (check2_append _ _ _ c65_0_2.h2
    (check2_append _ _ _ c65_0_2.h3
    (check2_append _ _ _ c65_0_2.h4
    (c65_0_2.h5)))))⟩

end WYD.Newton
