/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Petz.Certificate.ExpPolynomial
import WYDCurvature.Petz.Certificate.ListPoly
import WYDCurvature.Petz.Dittmann.Mixing

/-!
# Dittmann's inequalities (62) and (63): `hs` on the plane `x = y`

Dittmann's inequalities (62) and (63) (`DittmannInequalities.ineq62`, `ineq63`) only involve
`hs` on the plane `x = y`, through `φ(s, w) = hs(s, s, w)`: (63) says that `φ(·, l)` is concave,
and (62) follows from the concavity of `φ` along the lines of direction `(1, -1)`. Off the
diagonal `s = w`, `φ` is an explicit rational function of `s`, `w` and `L = log s - log w`:

`hs(s, s, w) = (s² w L² - 2 w² (s - w) L - (s - w)² (2 s - 3 w)) / (6 s w (s - w)² L²)`.

Its second derivatives along the two directions are again rational in `s`, `w`, `L`. To compute
them, polynomials in `s`, `w`, `L` are lists of monomials with integer coefficients (`planeEval`);
along a line of direction `(a, b)`, `d/dt p = Θ p / (s w)` with the polynomial
`Θ p = s w (a ∂ₛ p + b ∂_w p) + (a w - b s) ∂_L p` (`planeTheta`, `hasDerivAt_planeEval`). The
quotient rule twice, with the intermediate numerators given as data and checked by kernel
computation (`ListPoly`, `decide +kernel`), gives

* `∂ₛₛφ = P₆₃ / (3 L⁴ s³ w (s - w)⁴)` and `(∂ₛ - ∂_w)²φ = P₆₂ / (3 L⁴ s³ w³ (s - w)⁴)`

off the diagonal, with explicit polynomials `P₆₃ = plane63Num`, `P₆₂ = plane62Num` of 23 and 30
monomials. Both are `≤ 0` at `L = log s - log w`: by homogeneity
`P(w e^A, w, A) = w^d P(e^A, 1, A)`, and `-P(e^A, 1, A)` is an exponential polynomial whose Taylor
coefficients at `0`, and those of its reflection `A ↦ -A`, are nonnegative
(`Certificate/ExpPolynomial.lean`): the kernel checks them one by one below `45`
and by the tail check of `ExpPolynomial.tailOk` from `45` on (`ExpPolynomial.coefOk`).

Finally the signs give (62) and (63) for `hs′ = bkmHsDeriv`: along a line the derivative of
`hs(s, s, w)` is continuous (`hs` is `C²`) and, off the diagonal, has derivative `≤ 0`, so it does
not increase (the mean value theorem on the two sides of the diagonal point). These are the
segments `(x, x, λ) → (y, y, λ)` and `(x, x, y) → (y, y, x)` of Dittmann's Lemma 4; only concavity
along them is needed, not his Assertion that `hs` is concave on all of `ℝ³₊`. With these,
Dittmann's Theorem 3 needs only (64) and (65).

`-P₆₂(e^A, 1, A)` and its reflection have Taylor coefficients `0` below order `8` and `22400` at
order `8`, so `P₆₂ < 0` off the diagonal: its exponential polynomial is a nonzero power series
with nonnegative coefficients. With the strict mean value theorem this makes (62) strict, which
is all the strict form of Theorem 3 needs (`curvGrad_lt`).

## Main definitions

* `PetzCurvature.planeHs s w L`: the rational function above.
* `PetzCurvature.planeEval`, `PetzCurvature.planeTheta`: polynomials in `s`, `w`, `L`
  and their derivative along a line.
* `PetzCurvature.plane63Deriv`, `PetzCurvature.plane62Deriv`: the first derivatives
  `∂ₛφ` and `(∂ₛ - ∂_w)φ`.
* `PetzCurvature.plane63Num`, `PetzCurvature.plane62Num`: the numerators of the second
  derivatives.
* `PetzCurvature.planeExp`: `-P(e^A, 1, A)` as an exponential polynomial.
* `PetzCurvature.lineDeriv`: the derivative of `τ ↦ hs(s₀ + τ, s₀ + τ, w₀ + b τ)`.

## Main statements

* `PetzCurvature.bkmHs_plane`: `hs(s, s, w) = planeHs s w (log s - log w)` for positive
  `s ≠ w`.
* `PetzCurvature.hasDerivAt_planeEval`: the derivative of a polynomial in `s`, `w`,
  `log s - log w` along a line.
* `PetzCurvature.hasDerivAt_planeHs_fst`, `PetzCurvature.hasDerivAt_plane63Deriv`:
  the first and second derivatives of `φ` along `(1, 0)`.
* `PetzCurvature.hasDerivAt_planeHs_anti`, `PetzCurvature.hasDerivAt_plane62Deriv`:
  the same along `(1, -1)`.
* `PetzCurvature.planeEval_nonpos`: the sign of a plane numerator from two Taylor
  certificates.
* `PetzCurvature.plane63Num_nonpos`, `PetzCurvature.plane62Num_nonpos`: **the
  numerators behind (63) and (62) are nonpositive**.
* `PetzCurvature.planeEval_neg`, `PetzCurvature.plane62Num_neg`: strictly negative off the
  diagonal, from one positive Taylor coefficient on each side.
* `PetzCurvature.lineDeriv_le`: concavity of `hs(s, s, w)` along a line from the sign of the
  closed-form second derivative.
* `PetzCurvature.bkmHsDeriv_ineq63`, `PetzCurvature.bkmHsDeriv_ineq62`: **Dittmann's
  inequalities (63) and (62)**.
* `PetzCurvature.lineDeriv_lt`, `PetzCurvature.bkmHsDeriv_ineq62_pos`: strict concavity along a
  line, and **(62) strict**, which is what the strict form of Petz's conjecture needs.

## References

* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]

-/

namespace PetzCurvature

/-- Dittmann's `hs` on the plane `x = y`, as a rational function of `s`, `w` and
`L = log s - log w` (`bkmHs_plane`). -/
noncomputable def planeHs (s w L : ℝ) : ℝ :=
  (s ^ 2 * w * L ^ 2 - 2 * w ^ 2 * (s - w) * L - (s - w) ^ 2 * (2 * s - 3 * w)) /
    (6 * s * w * (s - w) ^ 2 * L ^ 2)

/-- **`hs` on the plane** in closed form: for positive `s ≠ w`,
`hs(s, s, w) = planeHs s w (log s - log w)`. -/
theorem bkmHs_plane {s w : ℝ} (hs : 0 < s) (hw : 0 < w) (hsw : s ≠ w) :
    bkmHs s s w = planeHs s w (Real.log s - Real.log w) := by
  have e : ∀ p q r, bkmSummand p q r = bkmIntegral₃ p q r ^ 2 /
      (2 * (bkmIntegral₂ p q * bkmIntegral₂ q r * bkmIntegral₂ r p)) -
        p * (bkmIntegral₃ p p q / bkmIntegral₂ p q) * (bkmIntegral₃ p p r / bkmIntegral₂ p r) :=
    fun _ _ _ ↦ by rw [bkmSummand]; ring
  have h1 : bkmIntegral₃ s w s = bkmIntegral₃ s s w := bkmIntegral₃_comm₂₃ s w s
  have h2 : bkmIntegral₃ w s s = bkmIntegral₃ s s w := by
    rw [bkmIntegral₃_comm₁₂, bkmIntegral₃_comm₂₃]
  rw [bkmHs, e, e, e, h1, h2, bkmIntegral₃_self_left hs hw hsw,
    bkmIntegral₃_self_left hw hs hsw.symm, bkmIntegral₃_self hs, bkmIntegral₂_self hs,
    bkmIntegral₂_of_ne hs hw hsw, bkmIntegral₂_of_ne hw hs hsw.symm, planeHs]
  have := sub_ne_zero.mpr hsw
  have := sub_ne_zero.mpr hsw.symm
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hs hw hsw)
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hw hs hsw.symm)
  field_simp
  ring

/-! ### Polynomials in `s`, `w` and `L = log s - log w` along lines -/

/-- A polynomial in `s`, `w`, `L` with integer coefficients, as a list of monomials:
`(c, i, j, k)` stands for `c sⁱ wʲ Lᵏ`. -/
def planeEval (p : List (ℤ × ℕ × ℕ × ℕ)) (s w L : ℝ) : ℝ :=
  (p.map fun m ↦ (m.1 : ℝ) * s ^ m.2.1 * w ^ m.2.2.1 * L ^ m.2.2.2).sum

/-- `Θ p = s w (a ∂ₛ p + b ∂_w p) + (a w - b s) ∂_L p`: along a line of direction `(a, b)`, with
`L = log s - log w`, `d/dt p = Θ p / (s w)`. -/
def planeTheta (a b : ℤ) (p : List (ℤ × ℕ × ℕ × ℕ)) : List (ℤ × ℕ × ℕ × ℕ) :=
  p.flatMap fun m ↦
    [(a * m.1 * m.2.1, m.2.1, m.2.2.1 + 1, m.2.2.2),
      (b * m.1 * m.2.2.1, m.2.1 + 1, m.2.2.1, m.2.2.2),
      (a * m.1 * m.2.2.2, m.2.1, m.2.2.1 + 1, m.2.2.2 - 1),
      (-(b * m.1 * m.2.2.2), m.2.1 + 1, m.2.2.1, m.2.2.2 - 1)]

theorem planeEval_nil (s w L : ℝ) : planeEval [] s w L = 0 := rfl

theorem planeEval_cons (m : ℤ × ℕ × ℕ × ℕ) (p : List (ℤ × ℕ × ℕ × ℕ)) (s w L : ℝ) :
    planeEval (m :: p) s w L = m.1 * s ^ m.2.1 * w ^ m.2.2.1 * L ^ m.2.2.2 + planeEval p s w L :=
  List.sum_cons

theorem planeEval_append (p q : List (ℤ × ℕ × ℕ × ℕ)) (s w L : ℝ) :
    planeEval (p ++ q) s w L = planeEval p s w L + planeEval q s w L := by
  simp [planeEval]

theorem natCast_mul_pow_pred_mul (n : ℕ) (x : ℝ) : (n : ℝ) * x ^ (n - 1) * x = n * x ^ n := by
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, mul_assoc, ← pow_succ]

variable {S W : ℝ → ℝ} {t : ℝ}

theorem hasDerivAt_planeMono {a b : ℤ} (hS : HasDerivAt S a t) (hW : HasDerivAt W b t)
    (hS0 : 0 < S t) (hW0 : 0 < W t) (c : ℤ) (i j k : ℕ) :
    HasDerivAt (fun t ↦ (c : ℝ) * S t ^ i * W t ^ j * (Real.log (S t) - Real.log (W t)) ^ k)
      (planeEval (planeTheta a b [(c, i, j, k)]) (S t) (W t)
        (Real.log (S t) - Real.log (W t)) / (S t * W t)) t := by
  have hL := (hS.log hS0.ne').sub (hW.log hW0.ne')
  have h := (((hS.pow i).const_mul (c : ℝ)).mul (hW.pow j)).mul (hL.pow k)
  refine h.congr_deriv ?_
  simp only [planeTheta, List.flatMap_cons, List.flatMap_nil, List.append_nil, planeEval_cons,
    planeEval_nil]
  push_cast
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
  field_simp
  linear_combination ((c : ℝ) * a * W t ^ (j + 1) * (Real.log (S t) - Real.log (W t)) ^ k) *
      natCast_mul_pow_pred_mul i (S t) +
    ((c : ℝ) * b * S t ^ (i + 1) * (Real.log (S t) - Real.log (W t)) ^ k) *
      natCast_mul_pow_pred_mul j (W t)

theorem hasDerivAt_planeEval {a b : ℤ} (hS : HasDerivAt S a t) (hW : HasDerivAt W b t)
    (hS0 : 0 < S t) (hW0 : 0 < W t) (p : List (ℤ × ℕ × ℕ × ℕ)) :
    HasDerivAt (fun t ↦ planeEval p (S t) (W t) (Real.log (S t) - Real.log (W t)))
      (planeEval (planeTheta a b p) (S t) (W t)
        (Real.log (S t) - Real.log (W t)) / (S t * W t)) t := by
  induction p with
  | nil => simpa [planeEval_nil, planeTheta] using hasDerivAt_const t (0 : ℝ)
  | cons m p ih =>
    obtain ⟨c, i, j, k⟩ := m
    have h := (hasDerivAt_planeMono hS hW hS0 hW0 c i j k).add ih
    simp only [planeEval_cons]
    refine h.congr_deriv ?_
    rw [show planeTheta a b ((c, i, j, k) :: p) =
      planeTheta a b [(c, i, j, k)] ++ planeTheta a b p by simp [planeTheta], planeEval_append,
      add_div]

/-- The quotient rule for `planeEval p / planeEval q` along a line. -/
theorem hasDerivAt_planeEval_div {a b : ℤ} (hS : HasDerivAt S a t) (hW : HasDerivAt W b t)
    (hS0 : 0 < S t) (hW0 : 0 < W t) (p q : List (ℤ × ℕ × ℕ × ℕ))
    (hq : planeEval q (S t) (W t) (Real.log (S t) - Real.log (W t)) ≠ 0) :
    HasDerivAt (fun t ↦ planeEval p (S t) (W t) (Real.log (S t) - Real.log (W t)) /
        planeEval q (S t) (W t) (Real.log (S t) - Real.log (W t)))
      ((planeEval (planeTheta a b p) (S t) (W t) (Real.log (S t) - Real.log (W t)) *
          planeEval q (S t) (W t) (Real.log (S t) - Real.log (W t)) -
        planeEval p (S t) (W t) (Real.log (S t) - Real.log (W t)) *
          planeEval (planeTheta a b q) (S t) (W t) (Real.log (S t) - Real.log (W t))) /
        (S t * W t * planeEval q (S t) (W t) (Real.log (S t) - Real.log (W t)) ^ 2)) t := by
  refine ((hasDerivAt_planeEval hS hW hS0 hW0 p).div (hasDerivAt_planeEval hS hW hS0 hW0 q)
    hq).congr_deriv ?_
  have := hS0.ne'
  have := hW0.ne'
  field_simp

/-! ### The certificate data

Monomial lists computed outside Lean by computer algebra. Their provenance does not matter: the
identities below check them by kernel computation. -/

/-- The numerator of `planeHs`. -/
def planeNum₀ : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-2, 3, 0, 0), (1, 2, 1, 2), (7, 2, 1, 0), (-2, 1, 2, 1), (-8, 1, 2, 0), (2, 0, 3, 1),
    (3, 0, 3, 0)]

/-- The denominator of `planeHs`: `6 s w (s - w)² L²`. -/
def planeDen₀ : List (ℤ × ℕ × ℕ × ℕ) :=
  [(6, 3, 1, 2), (-12, 2, 2, 2), (6, 1, 3, 2)]

/-- The denominator of the first derivatives: `s w D₀²`. -/
def planeDen₁ : List (ℤ × ℕ × ℕ × ℕ) :=
  [(36, 7, 3, 4), (-144, 6, 4, 4), (216, 5, 5, 4), (-144, 4, 6, 4), (36, 3, 7, 4)]

/-- The numerator of `∂ₛφ` (direction `(1, 0)`). -/
def plane63Num₁ : List (ℤ × ℕ × ℕ × ℕ) :=
  [(24, 6, 2, 1), (-6, 5, 3, 4), (-18, 5, 3, 2), (-132, 5, 3, 1), (24, 4, 4, 3), (84, 4, 4, 2),
    (288, 4, 4, 1), (6, 3, 5, 4), (-60, 3, 5, 3), (-144, 3, 5, 2), (-312, 3, 5, 1), (48, 2, 6, 3),
    (108, 2, 6, 2), (168, 2, 6, 1), (-12, 1, 7, 3), (-30, 1, 7, 2), (-36, 1, 7, 1)]

/-- The numerator of `(∂ₛ - ∂_w)φ` (direction `(1, -1)`). -/
def plane62Num₁ : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-12, 7, 1, 2), (24, 7, 1, 1), (48, 6, 2, 2), (-108, 6, 2, 1), (-18, 5, 3, 4), (12, 5, 3, 3),
    (-78, 5, 3, 2), (156, 5, 3, 1), (12, 4, 4, 4), (96, 4, 4, 2), (-24, 4, 4, 1), (6, 3, 5, 4),
    (-48, 3, 5, 3), (-120, 3, 5, 2), (-144, 3, 5, 1), (48, 2, 6, 3), (96, 2, 6, 2), (132, 2, 6, 1),
    (-12, 1, 7, 3), (-30, 1, 7, 2), (-36, 1, 7, 1)]

/-- The numerator `P` of `∂ₛₛφ = P / (3 L⁴ s³ w (s - w)⁴)`. -/
def plane63Num : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-2, 5, 0, 1), (-6, 5, 0, 0), (1, 4, 1, 4), (3, 4, 1, 2), (17, 4, 1, 1), (33, 4, 1, 0),
    (2, 3, 2, 4), (-6, 3, 2, 3), (-17, 3, 2, 2), (-50, 3, 2, 1), (-72, 3, 2, 0), (12, 2, 3, 3),
    (31, 2, 3, 2), (68, 2, 3, 1), (78, 2, 3, 0), (-8, 1, 4, 3), (-23, 1, 4, 2), (-44, 1, 4, 1),
    (-42, 1, 4, 0), (2, 0, 5, 3), (6, 0, 5, 2), (11, 0, 5, 1), (9, 0, 5, 0)]

/-- The numerator `P` of `(∂ₛ - ∂_w)²φ = P / (3 L⁴ s³ w³ (s - w)⁴)`. -/
def plane62Num : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-2, 7, 0, 2), (6, 7, 0, 1), (-6, 7, 0, 0), (8, 6, 1, 2), (-23, 6, 1, 1), (21, 6, 1, 0),
    (-13, 5, 2, 2), (34, 5, 2, 1), (-12, 5, 2, 0), (8, 4, 3, 4), (-6, 4, 3, 3), (6, 4, 3, 2),
    (-23, 4, 3, 1), (-33, 4, 3, 0), (4, 3, 4, 4), (-4, 3, 4, 2), (-6, 3, 4, 1), (42, 3, 4, 0),
    (12, 2, 5, 3), (20, 2, 5, 2), (35, 2, 5, 1), (3, 2, 5, 0), (-8, 1, 6, 3), (-21, 1, 6, 2),
    (-34, 1, 6, 1), (-24, 1, 6, 0), (2, 0, 7, 3), (6, 0, 7, 2), (11, 0, 7, 1), (9, 0, 7, 0)]

/-! ### The derivatives of `φ(s, w) = hs(s, s, w)` -/

theorem planeHs_eq_planeEval (s w L : ℝ) :
    planeHs s w L = planeEval planeNum₀ s w L / planeEval planeDen₀ s w L := by
  simp only [planeHs, planeEval, planeNum₀, planeDen₀, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  push_cast
  ring_nf

/-! ### The polynomial identities, by kernel computation

Each identity is checked as an identity of `ListPoly` polynomials in the variables `s, w, L`
(numbered `0, 1, 2`) by `decide +kernel`, and read back over `ℝ` through `eval_planeToList`. -/

section Identities

open ListPoly

/-- A polynomial in `s`, `w`, `L` as a `ListPoly` in the variables `0, 1, 2`. -/
def planeToList (p : List (ℤ × ℕ × ℕ × ℕ)) : List Mono :=
  p.map fun (c, i, j, k) ↦ mono c [i, j, k]

@[simp] theorem eval_planeToList (p : List (ℤ × ℕ × ℕ × ℕ)) (s w L : ℝ) :
    eval (planeToList p) [s, w, L] = planeEval p s w L := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    obtain ⟨c, i, j, k⟩ := t
    rw [planeToList, List.map_cons, eval_cons, ← planeToList, ih, planeEval_cons]
    simp only [mono, evalExp]
    ring

/-- The quotient-rule numerator `Θ N · D - N · Θ D` along the direction `(a, b)`. -/
def planeQuot (a b : ℤ) (N D : List (ℤ × ℕ × ℕ × ℕ)) : List Mono :=
  sub (mul (planeToList D) (norm (planeToList (planeTheta a b N))))
    (mul (planeToList N) (norm (planeToList (planeTheta a b D))))

@[simp] theorem eval_planeQuot (a b : ℤ) (N D : List (ℤ × ℕ × ℕ × ℕ)) (s w L : ℝ) :
    eval (planeQuot a b N D) [s, w, L] = planeEval (planeTheta a b N) s w L * planeEval D s w L -
      planeEval N s w L * planeEval (planeTheta a b D) s w L := by
  simp only [planeQuot, eval_sub, eval_mul, eval_norm, eval_planeToList]
  ring

local notation "𝐬" => var 0
local notation "𝐰" => var 1
local notation "𝐋" => var 2

theorem planeDen₀_check :
    sub (norm (planeToList planeDen₀)) (smul 6 (prod [𝐬, 𝐰, pow (sub 𝐬 𝐰) 2, pow 𝐋 2])) = [] := by
  decide +kernel

theorem planeDen₁_check :
    sub (norm (planeToList planeDen₁)) (prod [𝐬, 𝐰, pow (planeToList planeDen₀) 2]) = [] := by
  decide +kernel

theorem plane63Num₁_check :
    sub (norm (planeToList plane63Num₁)) (planeQuot 1 0 planeNum₀ planeDen₀) = [] := by
  decide +kernel

theorem plane62Num₁_check :
    sub (norm (planeToList plane62Num₁)) (planeQuot 1 (-1) planeNum₀ planeDen₀) = [] := by
  decide +kernel

theorem plane63Num_check : sub (planeQuot 1 0 plane63Num₁ planeDen₁)
    (smul 432 (prod [pow 𝐋 4, pow 𝐬 4, pow 𝐰 6, pow (sub 𝐬 𝐰) 4, planeToList plane63Num])) =
      [] := by
  decide +kernel

theorem plane62Num_check : sub (planeQuot 1 (-1) plane62Num₁ planeDen₁)
    (smul 432 (prod [pow 𝐋 4, pow 𝐬 4, pow 𝐰 4, pow (sub 𝐬 𝐰) 4, planeToList plane62Num])) =
      [] := by
  decide +kernel

theorem planeDen₀_eq (s w L : ℝ) : planeEval planeDen₀ s w L = 6 * s * w * (s - w) ^ 2 * L ^ 2 := by
  have h := eval_eq_of_sub_eq_nil planeDen₀_check [s, w, L]
  simp only [eval_norm, eval_planeToList, eval_smul, eval_prod, eval_sub, eval_pow, eval_var_zero,
    eval_var_succ, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at h
  linear_combination h

theorem planeDen₁_eq (s w L : ℝ) :
    planeEval planeDen₁ s w L = s * w * planeEval planeDen₀ s w L ^ 2 := by
  have h := eval_eq_of_sub_eq_nil planeDen₁_check [s, w, L]
  simp only [eval_norm, eval_planeToList, eval_prod, eval_pow, eval_var_zero, eval_var_succ,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at h
  linear_combination h

theorem plane63Num₁_eq (s w L : ℝ) :
    planeEval plane63Num₁ s w L = planeEval (planeTheta 1 0 planeNum₀) s w L *
      planeEval planeDen₀ s w L - planeEval planeNum₀ s w L *
        planeEval (planeTheta 1 0 planeDen₀) s w L := by
  have h := eval_eq_of_sub_eq_nil plane63Num₁_check [s, w, L]
  rwa [eval_norm, eval_planeToList, eval_planeQuot] at h

theorem plane62Num₁_eq (s w L : ℝ) :
    planeEval plane62Num₁ s w L = planeEval (planeTheta 1 (-1) planeNum₀) s w L *
      planeEval planeDen₀ s w L - planeEval planeNum₀ s w L *
        planeEval (planeTheta 1 (-1) planeDen₀) s w L := by
  have h := eval_eq_of_sub_eq_nil plane62Num₁_check [s, w, L]
  rwa [eval_norm, eval_planeToList, eval_planeQuot] at h

theorem plane63Num_eq (s w L : ℝ) :
    planeEval (planeTheta 1 0 plane63Num₁) s w L * planeEval planeDen₁ s w L -
      planeEval plane63Num₁ s w L * planeEval (planeTheta 1 0 planeDen₁) s w L =
        432 * L ^ 4 * s ^ 4 * w ^ 6 * (s - w) ^ 4 * planeEval plane63Num s w L := by
  have h := eval_eq_of_sub_eq_nil plane63Num_check [s, w, L]
  simp only [eval_planeQuot, eval_planeToList, eval_smul, eval_prod, eval_sub, eval_pow,
    eval_var_zero, eval_var_succ, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at h
  linear_combination h

theorem plane62Num_eq (s w L : ℝ) :
    planeEval (planeTheta 1 (-1) plane62Num₁) s w L * planeEval planeDen₁ s w L -
      planeEval plane62Num₁ s w L * planeEval (planeTheta 1 (-1) planeDen₁) s w L =
        432 * L ^ 4 * s ^ 4 * w ^ 4 * (s - w) ^ 4 * planeEval plane62Num s w L := by
  have h := eval_eq_of_sub_eq_nil plane62Num_check [s, w, L]
  simp only [eval_planeQuot, eval_planeToList, eval_smul, eval_prod, eval_sub, eval_pow,
    eval_var_zero, eval_var_succ, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at h
  linear_combination h

end Identities

theorem planeDen₀_ne_zero {s w : ℝ} (hs : 0 < s) (hw : 0 < w) (hsw : s ≠ w) :
    planeEval planeDen₀ s w (Real.log s - Real.log w) ≠ 0 := by
  rw [planeDen₀_eq]
  have := sub_ne_zero.mpr hsw
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hs hw hsw)
  positivity

theorem planeDen₁_ne_zero {s w : ℝ} (hs : 0 < s) (hw : 0 < w) (hsw : s ≠ w) :
    planeEval planeDen₁ s w (Real.log s - Real.log w) ≠ 0 := by
  rw [planeDen₁_eq]
  have := planeDen₀_ne_zero hs hw hsw
  positivity

/-- `∂ₛφ` on the plane, `φ(s, w) = hs(s, s, w)`, off the diagonal (`hasDerivAt_planeHs_fst`). -/
noncomputable def plane63Deriv (s w L : ℝ) : ℝ :=
  planeEval plane63Num₁ s w L / planeEval planeDen₁ s w L

/-- `(∂ₛ - ∂_w)φ` on the plane, `φ(s, w) = hs(s, s, w)`, off the diagonal
(`hasDerivAt_planeHs_anti`). -/
noncomputable def plane62Deriv (s w L : ℝ) : ℝ :=
  planeEval plane62Num₁ s w L / planeEval planeDen₁ s w L

theorem hasDerivAt_planeHs_line {a b : ℤ} (hS : HasDerivAt S a t) (hW : HasDerivAt W b t)
    (hS0 : 0 < S t) (hW0 : 0 < W t) (hSW : S t ≠ W t) :
    HasDerivAt (fun t ↦ planeHs (S t) (W t) (Real.log (S t) - Real.log (W t)))
      ((planeEval (planeTheta a b planeNum₀) (S t) (W t) (Real.log (S t) - Real.log (W t)) *
          planeEval planeDen₀ (S t) (W t) (Real.log (S t) - Real.log (W t)) -
        planeEval planeNum₀ (S t) (W t) (Real.log (S t) - Real.log (W t)) *
          planeEval (planeTheta a b planeDen₀) (S t) (W t) (Real.log (S t) - Real.log (W t))) /
        (S t * W t * planeEval planeDen₀ (S t) (W t) (Real.log (S t) - Real.log (W t)) ^ 2)) t := by
  simp only [planeHs_eq_planeEval]
  exact hasDerivAt_planeEval_div hS hW hS0 hW0 _ _ (planeDen₀_ne_zero hS0 hW0 hSW)

/-- The derivative of `φ(s, w) = hs(s, s, w)` in `s`, along a line of direction `(1, 0)`. -/
theorem hasDerivAt_planeHs_fst (hS : HasDerivAt S 1 t) (hW : HasDerivAt W 0 t) (hS0 : 0 < S t)
    (hW0 : 0 < W t) (hSW : S t ≠ W t) :
    HasDerivAt (fun t ↦ planeHs (S t) (W t) (Real.log (S t) - Real.log (W t)))
      (plane63Deriv (S t) (W t) (Real.log (S t) - Real.log (W t))) t := by
  refine (hasDerivAt_planeHs_line (a := 1) (b := 0) (by exact_mod_cast hS) (by exact_mod_cast hW)
    hS0 hW0 hSW).congr_deriv ?_
  rw [plane63Deriv, plane63Num₁_eq, planeDen₁_eq]

/-- The derivative of `φ(s, w) = hs(s, s, w)` along a line of direction `(1, -1)`. -/
theorem hasDerivAt_planeHs_anti (hS : HasDerivAt S 1 t) (hW : HasDerivAt W (-1) t)
    (hS0 : 0 < S t) (hW0 : 0 < W t) (hSW : S t ≠ W t) :
    HasDerivAt (fun t ↦ planeHs (S t) (W t) (Real.log (S t) - Real.log (W t)))
      (plane62Deriv (S t) (W t) (Real.log (S t) - Real.log (W t))) t := by
  refine (hasDerivAt_planeHs_line (a := 1) (b := -1) (by exact_mod_cast hS)
    (by exact_mod_cast hW) hS0 hW0 hSW).congr_deriv ?_
  rw [plane62Deriv, plane62Num₁_eq, planeDen₁_eq]

/-- **The second derivative behind (63)**: along a line of direction `(1, 0)`, off the diagonal,
`∂ₛₛφ = P / (3 L⁴ s³ w (s - w)⁴)` with `P = plane63Num`. -/
theorem hasDerivAt_plane63Deriv (hS : HasDerivAt S 1 t) (hW : HasDerivAt W 0 t) (hS0 : 0 < S t)
    (hW0 : 0 < W t) (hSW : S t ≠ W t) :
    HasDerivAt (fun t ↦ plane63Deriv (S t) (W t) (Real.log (S t) - Real.log (W t)))
      (planeEval plane63Num (S t) (W t) (Real.log (S t) - Real.log (W t)) /
        (3 * (Real.log (S t) - Real.log (W t)) ^ 4 * S t ^ 3 * W t * (S t - W t) ^ 4)) t := by
  refine (hasDerivAt_planeEval_div (a := 1) (b := 0) (by exact_mod_cast hS)
    (by exact_mod_cast hW) hS0 hW0 _ _ (planeDen₁_ne_zero hS0 hW0 hSW)).congr_deriv ?_
  rw [plane63Num_eq, planeDen₁_eq, planeDen₀_eq]
  have := sub_ne_zero.mpr hSW
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hS0 hW0 hSW)
  have := hS0.ne'
  have := hW0.ne'
  field_simp
  ring

/-- **The second derivative behind (62)**: along a line of direction `(1, -1)`, off the diagonal,
`(∂ₛ - ∂_w)²φ = P / (3 L⁴ s³ w³ (s - w)⁴)` with `P = plane62Num`. -/
theorem hasDerivAt_plane62Deriv (hS : HasDerivAt S 1 t) (hW : HasDerivAt W (-1) t)
    (hS0 : 0 < S t) (hW0 : 0 < W t) (hSW : S t ≠ W t) :
    HasDerivAt (fun t ↦ plane62Deriv (S t) (W t) (Real.log (S t) - Real.log (W t)))
      (planeEval plane62Num (S t) (W t) (Real.log (S t) - Real.log (W t)) /
        (3 * (Real.log (S t) - Real.log (W t)) ^ 4 * S t ^ 3 * W t ^ 3 * (S t - W t) ^ 4)) t := by
  refine (hasDerivAt_planeEval_div (a := 1) (b := -1) (by exact_mod_cast hS)
    (by exact_mod_cast hW) hS0 hW0 _ _ (planeDen₁_ne_zero hS0 hW0 hSW)).congr_deriv ?_
  rw [plane62Num_eq, planeDen₁_eq, planeDen₀_eq]
  have := sub_ne_zero.mpr hSW
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hS0 hW0 hSW)
  have := hS0.ne'
  have := hW0.ne'
  field_simp
  ring

/-! ### The signs of the numerators -/

/-- The exponential polynomial `-P(e^A, 1, A)` of a polynomial `P` in `s`, `w`, `L`. -/
def planeExp (p : List (ℤ × ℕ × ℕ × ℕ)) : List (ℤ × ℕ × ℕ) :=
  p.map fun m ↦ (-m.1, m.2.1, m.2.2.2)

/-- For `P` homogeneous of degree `d` in `(s, w)`: `P(w e^A, w, A) = -w^d (-P)(e^A, 1, A)`. -/
theorem planeEval_mul_exp {p : List (ℤ × ℕ × ℕ × ℕ)} {d : ℕ}
    (hd : ∀ m ∈ p, m.2.1 + m.2.2.1 = d) (w A : ℝ) :
    planeEval p (w * Real.exp A) w A = -(w ^ d * ExpPolynomial.eval (planeExp p) A) := by
  rw [planeEval, ExpPolynomial.eval, planeExp, List.map_map, ← List.sum_map_mul_left,
    neg_eq_neg_one_mul, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun m hm ↦ ?_)
  simp only [Function.comp_apply]
  rw [← hd m hm, mul_pow, ← Real.exp_nat_mul, pow_add]
  push_cast
  ring

/-- **Sign of a plane numerator from two Taylor certificates**: if `-P(e^A, 1, A)` and its
reflection have nonnegative Taylor coefficients, then `P(s, w, log s - log w) ≤ 0`. -/
theorem planeEval_nonpos {p : List (ℤ × ℕ × ℕ × ℕ)} {d K : ℕ}
    (hd : ∀ m ∈ p, m.2.1 + m.2.2.1 = d) (hK : ∀ m ∈ planeExp p, m.2.1 ≤ K)
    (hpos : ∀ n, 0 ≤ ExpPolynomial.coef (planeExp p) n)
    (hneg : ∀ n, 0 ≤ ExpPolynomial.coef (ExpPolynomial.reflect K (planeExp p)) n)
    {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    planeEval p s w (Real.log s - Real.log w) ≤ 0 := by
  have e : s = w * Real.exp (Real.log s - Real.log w) := by
    rw [Real.exp_sub, Real.exp_log hs, Real.exp_log hw]; field_simp
  generalize Real.log s - Real.log w = L at e ⊢
  subst e
  rw [planeEval_mul_exp hd]
  have hG : 0 ≤ ExpPolynomial.eval (planeExp p) L := by
    rcases le_total 0 L with h | h
    · exact ExpPolynomial.eval_nonneg hpos h
    · rw [ExpPolynomial.eval_reflect hK]
      exact mul_nonneg (Real.exp_pos _).le (ExpPolynomial.eval_nonneg hneg (by linarith))
  have := pow_pos hw d
  nlinarith

/-- **Sign of a plane numerator from two kernel checks**: `coefOk` for `-P(e^A, 1, A)` and for
its reflection at the top exponent. -/
theorem planeEval_nonpos_of_coefOk {p : List (ℤ × ℕ × ℕ × ℕ)} {d M : ℕ}
    (hd : ∀ m ∈ p, m.2.1 + m.2.2.1 = d) (h₁ : ExpPolynomial.coefOk (planeExp p) M = true)
    (h₂ : ExpPolynomial.coefOk
      (ExpPolynomial.reflect (ExpPolynomial.maxE (planeExp p)) (planeExp p)) M = true)
    {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    planeEval p s w (Real.log s - Real.log w) ≤ 0 :=
  planeEval_nonpos hd ExpPolynomial.le_maxE (ExpPolynomial.coefOk_spec h₁)
    (ExpPolynomial.coefOk_spec h₂) hs hw

/-- **The numerator behind (63) is nonpositive**: `P₆₃(s, w, log s - log w) ≤ 0` for `s, w > 0`.
`P₆₃` is homogeneous of degree `5` in `(s, w)`; the Taylor coefficients of `-P₆₃(e^A, 1, A)` on
both sides are checked one by one below `45` and by the tail check from `45` on. -/
theorem plane63Num_nonpos {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    planeEval plane63Num s w (Real.log s - Real.log w) ≤ 0 :=
  planeEval_nonpos_of_coefOk (d := 5) (M := 45) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hs hw

/-- **The numerator behind (62) is nonpositive**: `P₆₂(s, w, log s - log w) ≤ 0` for `s, w > 0`.
`P₆₂` is homogeneous of degree `7` in `(s, w)`; the Taylor coefficients of `-P₆₂(e^A, 1, A)` on
both sides are checked one by one below `45` and by the tail check from `45` on. -/
theorem plane62Num_nonpos {s w : ℝ} (hs : 0 < s) (hw : 0 < w) :
    planeEval plane62Num s w (Real.log s - Real.log w) ≤ 0 :=
  planeEval_nonpos_of_coefOk (d := 7) (M := 45) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hs hw

/-- **Strict sign of a plane numerator from two Taylor certificates**: if moreover a Taylor
coefficient of `-P(e^A, 1, A)` and one of its reflection are positive, then
`P(s, w, log s - log w) < 0` off the diagonal `s = w`. -/
theorem planeEval_neg {p : List (ℤ × ℕ × ℕ × ℕ)} {d K N₁ N₂ : ℕ}
    (hd : ∀ m ∈ p, m.2.1 + m.2.2.1 = d) (hK : ∀ m ∈ planeExp p, m.2.1 ≤ K)
    (hpos : ∀ n, 0 ≤ ExpPolynomial.coef (planeExp p) n)
    (hneg : ∀ n, 0 ≤ ExpPolynomial.coef (ExpPolynomial.reflect K (planeExp p)) n)
    (hN₁ : 0 < ExpPolynomial.coef (planeExp p) N₁)
    (hN₂ : 0 < ExpPolynomial.coef (ExpPolynomial.reflect K (planeExp p)) N₂)
    {s w : ℝ} (hs : 0 < s) (hw : 0 < w) (hsw : s ≠ w) :
    planeEval p s w (Real.log s - Real.log w) < 0 := by
  have hL : Real.log s - Real.log w ≠ 0 := sub_ne_zero.mpr (Real.log_injOn_pos.ne hs hw hsw)
  have e : s = w * Real.exp (Real.log s - Real.log w) := by
    rw [Real.exp_sub, Real.exp_log hs, Real.exp_log hw]; field_simp
  generalize Real.log s - Real.log w = L at e hL ⊢
  subst e
  rw [planeEval_mul_exp hd]
  have hG : 0 < ExpPolynomial.eval (planeExp p) L := by
    rcases hL.lt_or_gt with h | h
    · rw [ExpPolynomial.eval_reflect hK]
      exact mul_pos (Real.exp_pos _) (ExpPolynomial.eval_pos hneg hN₂ (by linarith))
    · exact ExpPolynomial.eval_pos hpos hN₁ h
  have := pow_pos hw d
  nlinarith

/-- **Strict sign of a plane numerator from kernel checks**: `coefOk` for `-P(e^A, 1, A)` and for
its reflection, and one positive coefficient of each. -/
theorem planeEval_neg_of_coefOk {p : List (ℤ × ℕ × ℕ × ℕ)} {d M N₁ N₂ : ℕ}
    (hd : ∀ m ∈ p, m.2.1 + m.2.2.1 = d) (h₁ : ExpPolynomial.coefOk (planeExp p) M = true)
    (h₂ : ExpPolynomial.coefOk
      (ExpPolynomial.reflect (ExpPolynomial.maxE (planeExp p)) (planeExp p)) M = true)
    (hN₁ : 0 < ExpPolynomial.coef (planeExp p) N₁)
    (hN₂ : 0 < ExpPolynomial.coef
      (ExpPolynomial.reflect (ExpPolynomial.maxE (planeExp p)) (planeExp p)) N₂)
    {s w : ℝ} (hs : 0 < s) (hw : 0 < w) (hsw : s ≠ w) :
    planeEval p s w (Real.log s - Real.log w) < 0 :=
  planeEval_neg hd ExpPolynomial.le_maxE (ExpPolynomial.coefOk_spec h₁)
    (ExpPolynomial.coefOk_spec h₂) hN₁ hN₂ hs hw hsw

/-- **The numerator behind (62) is negative off the diagonal**: `P₆₂(s, w, log s - log w) < 0`
for positive `s ≠ w`. The Taylor coefficients of order `8` of `-P₆₂(e^A, 1, A)` and of its
reflection are positive (`22400`); those below `8` vanish. -/
theorem plane62Num_neg {s w : ℝ} (hs : 0 < s) (hw : 0 < w) (hsw : s ≠ w) :
    planeEval plane62Num s w (Real.log s - Real.log w) < 0 :=
  planeEval_neg_of_coefOk (d := 7) (M := 45) (N₁ := 8) (N₂ := 8) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hs hw hsw

/-! ### Concavity along lines: Dittmann's (62) and (63) -/

section Line

open Set Filter Topology

/-- A function continuous on `[a, c]` whose derivative is `≤ 0` on `(a, c)` except at one point
`p` does not increase from `a` to `c`. -/
theorem le_of_hasDerivAt_nonpos_off {f f' : ℝ → ℝ} {a c p : ℝ} (hac : a ≤ c)
    (hf : ContinuousOn f (Icc a c))
    (hd : ∀ τ ∈ Ioo a c, τ ≠ p → HasDerivAt f (f' τ) τ ∧ f' τ ≤ 0) : f c ≤ f a := by
  have key : ∀ a' c', a ≤ a' → a' ≤ c' → c' ≤ c → p ∉ Ioo a' c' → f c' ≤ f a' := by
    intro a' c' h1 h2 h3 hp
    have hsub : ∀ x ∈ Ioo a' c', x ∈ Ioo a c ∧ x ≠ p := fun x hx ↦
      ⟨⟨h1.trans_lt hx.1, hx.2.trans_le h3⟩, fun h ↦ hp (h ▸ hx)⟩
    have hmono := antitoneOn_of_deriv_nonpos (convex_Icc a' c')
      (hf.mono (Icc_subset_Icc h1 h3)) (by
        rw [interior_Icc]
        intro x hx
        exact (hd x (hsub x hx).1 (hsub x hx).2).1.differentiableAt.differentiableWithinAt) (by
        rw [interior_Icc]
        intro x hx
        rw [(hd x (hsub x hx).1 (hsub x hx).2).1.deriv]
        exact (hd x (hsub x hx).1 (hsub x hx).2).2)
    exact hmono (left_mem_Icc.2 h2) (right_mem_Icc.2 h2) h2
  by_cases hp : p ∈ Ioo a c
  · exact (key p c hp.1.le hp.2.le le_rfl fun h ↦ lt_irrefl _ h.1).trans
      (key a p le_rfl hp.1.le hp.2.le fun h ↦ lt_irrefl _ h.2)
  · exact key a c le_rfl hac le_rfl hp

/-- A function continuous on `[a, c]` whose derivative is `< 0` on `(a, c)` except at one point
`p` decreases strictly from `a` to `c`. -/
theorem lt_of_hasDerivAt_neg_off {f f' : ℝ → ℝ} {a c p : ℝ} (hac : a < c)
    (hf : ContinuousOn f (Icc a c))
    (hd : ∀ τ ∈ Ioo a c, τ ≠ p → HasDerivAt f (f' τ) τ ∧ f' τ < 0) : f c < f a := by
  have hle : ∀ a' c', a ≤ a' → a' ≤ c' → c' ≤ c → f c' ≤ f a' := fun a' c' h1 h2 h3 ↦
    le_of_hasDerivAt_nonpos_off h2 (hf.mono (Icc_subset_Icc h1 h3)) fun τ hτ hp ↦
      have h := hd τ ⟨h1.trans_lt hτ.1, hτ.2.trans_le h3⟩ hp
      ⟨h.1, h.2.le⟩
  have hlt : ∀ a' c', a ≤ a' → a' < c' → c' ≤ c → p ∉ Ioo a' c' → f c' < f a' := by
    intro a' c' h1 h2 h3 hp
    have hsub : ∀ x ∈ Ioo a' c', x ∈ Ioo a c ∧ x ≠ p := fun x hx ↦
      ⟨⟨h1.trans_lt hx.1, hx.2.trans_le h3⟩, fun h ↦ hp (h ▸ hx)⟩
    refine strictAntiOn_of_deriv_neg (convex_Icc a' c') (hf.mono (Icc_subset_Icc h1 h3)) ?_
      (left_mem_Icc.2 h2.le) (right_mem_Icc.2 h2.le) h2
    rw [interior_Icc]
    intro x hx
    rw [(hd x (hsub x hx).1 (hsub x hx).2).1.deriv]
    exact (hd x (hsub x hx).1 (hsub x hx).2).2
  rcases le_or_gt p ((a + c) / 2) with hp | hp
  · exact (hlt ((a + c) / 2) c (by linarith) (by linarith) le_rfl fun h ↦ by
      linarith [h.1]).trans_le (hle a ((a + c) / 2) le_rfl (by linarith) (by linarith))
  · exact (hle ((a + c) / 2) c (by linarith) (by linarith) le_rfl).trans_lt
      (hlt a ((a + c) / 2) le_rfl (by linarith) (by linarith) fun h ↦ by linarith [h.2])

variable {s₀ w₀ b : ℝ}

/-- The derivative of `τ ↦ hs(s₀ + τ, s₀ + τ, w₀ + b τ)`:
`2 hs′(S, S, W) + b hs′(W, S, S)` (`hasDerivAt_bkmHs_line`). -/
noncomputable def lineDeriv (s₀ w₀ b τ : ℝ) : ℝ :=
  2 * bkmHsDeriv (s₀ + τ) (s₀ + τ) (w₀ + b * τ) + b * bkmHsDeriv (w₀ + b * τ) (s₀ + τ) (s₀ + τ)

theorem hasDerivAt_bkmHs_line {τ : ℝ} (hS : 0 < s₀ + τ) (hW : 0 < w₀ + b * τ) :
    HasDerivAt (fun τ ↦ bkmHs (s₀ + τ) (s₀ + τ) (w₀ + b * τ)) (lineDeriv s₀ w₀ b τ) τ := by
  have hs : HasDerivAt (fun τ ↦ s₀ + τ) 1 τ := (hasDerivAt_id τ).const_add s₀
  have hw : HasDerivAt (fun τ ↦ w₀ + b * τ) b τ := by
    simpa using ((hasDerivAt_id τ).const_mul b).const_add w₀
  convert hasDerivAt_bkmHs_comp hs hs hw hS hS hW using 1
  rw [lineDeriv]
  ring

theorem eventually_line_pos {τ : ℝ} (hS : 0 < s₀ + τ) (hW : 0 < w₀ + b * τ) :
    ∀ᶠ τ' in 𝓝 τ, 0 < s₀ + τ' ∧ 0 < w₀ + b * τ' :=
  (continuousAt_const.eventually_lt (by fun_prop) hS).and
    (continuousAt_const.eventually_lt (by fun_prop) hW)

/-- `lineDeriv` is continuous: `hs` is `C²`. -/
theorem continuousAt_lineDeriv {τ : ℝ} (hS : 0 < s₀ + τ) (hW : 0 < w₀ + b * τ) :
    ContinuousAt (lineDeriv s₀ w₀ b) τ := by
  have hc := contDiffAt_bkmHs_comp (n := 2) (f := fun τ ↦ s₀ + τ) (g := fun τ ↦ s₀ + τ)
    (h := fun τ ↦ w₀ + b * τ) (by fun_prop) (by fun_prop) (by fun_prop) hS hS hW
  rw [show ((2 : ℕ) : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) + 1 by norm_num] at hc
  obtain ⟨f', ⟨u, hu, hf⟩, hf'⟩ := contDiffAt_succ_iff_hasFDerivAt.mp hc
  have heq : (fun τ' ↦ f' τ' 1) =ᶠ[𝓝 τ] lineDeriv s₀ w₀ b := by
    filter_upwards [hu, eventually_line_pos hS hW] with τ' h1 h2
    exact (hf τ' h1).hasDerivAt.unique (hasDerivAt_bkmHs_line h2.1 h2.2)
  exact ((hf'.continuousAt.clm_apply continuousAt_const).congr heq)

/-- Off the diagonal `lineDeriv` is the derivative of the closed form `planeHs` along the line, so
it is differentiable wherever that derivative is. -/
theorem hasDerivAt_lineDeriv_of_ne {D₁ : ℝ → ℝ} {d₂ τ : ℝ} (hS : 0 < s₀ + τ)
    (hW : 0 < w₀ + b * τ) (hne : s₀ + τ ≠ w₀ + b * τ)
    (hD₁ : ∀ τ', 0 < s₀ + τ' → 0 < w₀ + b * τ' → s₀ + τ' ≠ w₀ + b * τ' →
      HasDerivAt (fun τ ↦ planeHs (s₀ + τ) (w₀ + b * τ)
        (Real.log (s₀ + τ) - Real.log (w₀ + b * τ))) (D₁ τ') τ')
    (hD₂ : HasDerivAt D₁ d₂ τ) : HasDerivAt (lineDeriv s₀ w₀ b) d₂ τ := by
  have hV : ∀ᶠ τ' in 𝓝 τ, (0 < s₀ + τ' ∧ 0 < w₀ + b * τ') ∧ s₀ + τ' ≠ w₀ + b * τ' :=
    (eventually_line_pos hS hW).and
      ((ContinuousAt.eventually_ne (g := fun τ' ↦ s₀ + τ' - (w₀ + b * τ')) (by fun_prop)
        (sub_ne_zero.mpr hne)).mono fun _ h ↦ sub_ne_zero.mp h)
  refine hD₂.congr_of_eventuallyEq ?_
  filter_upwards [hV.eventually_nhds] with τ' h
  have hh : (fun τ ↦ bkmHs (s₀ + τ) (s₀ + τ) (w₀ + b * τ)) =ᶠ[𝓝 τ'] fun τ ↦
      planeHs (s₀ + τ) (w₀ + b * τ) (Real.log (s₀ + τ) - Real.log (w₀ + b * τ)) := by
    filter_upwards [h] with τ'' h'' using bkmHs_plane h''.1.1 h''.1.2 h''.2
  exact (hasDerivAt_bkmHs_line h.self_of_nhds.1.1 h.self_of_nhds.1.2).unique
    ((hD₁ τ' h.self_of_nhds.1.1 h.self_of_nhds.1.2 h.self_of_nhds.2).congr_of_eventuallyEq hh)

/-- **Concavity along a line**: if the closed form has a second derivative `≤ 0` off the
diagonal, then `lineDeriv` does not increase on an interval of the positive region. -/
theorem lineDeriv_le {D₁ D₂ : ℝ → ℝ} (hb : b ≠ 1) {a c : ℝ} (hac : a ≤ c)
    (hpos : ∀ τ ∈ Icc a c, 0 < s₀ + τ ∧ 0 < w₀ + b * τ)
    (hD₁ : ∀ τ', 0 < s₀ + τ' → 0 < w₀ + b * τ' → s₀ + τ' ≠ w₀ + b * τ' →
      HasDerivAt (fun τ ↦ planeHs (s₀ + τ) (w₀ + b * τ)
        (Real.log (s₀ + τ) - Real.log (w₀ + b * τ))) (D₁ τ') τ')
    (hD₂ : ∀ τ, 0 < s₀ + τ → 0 < w₀ + b * τ → s₀ + τ ≠ w₀ + b * τ →
      HasDerivAt D₁ (D₂ τ) τ ∧ D₂ τ ≤ 0) :
    lineDeriv s₀ w₀ b c ≤ lineDeriv s₀ w₀ b a := by
  refine le_of_hasDerivAt_nonpos_off (f' := D₂) (p := (w₀ - s₀) / (1 - b)) hac
    (fun τ hτ ↦ (continuousAt_lineDeriv (hpos τ hτ).1 (hpos τ hτ).2).continuousWithinAt)
    fun τ hτ hp ↦ ?_
  have hτ' := hpos τ (Ioo_subset_Icc_self hτ)
  have hne : s₀ + τ ≠ w₀ + b * τ := by
    intro h
    apply hp
    have : (1 - b) ≠ 0 := sub_ne_zero.mpr hb.symm
    field_simp
    linarith
  have h := hD₂ τ hτ'.1 hτ'.2 hne
  exact ⟨hasDerivAt_lineDeriv_of_ne hτ'.1 hτ'.2 hne hD₁ h.1, h.2⟩

/-- **Strict concavity along a line**: if the closed form has a second derivative `< 0` off the
diagonal, then `lineDeriv` decreases strictly on an interval of the positive region. -/
theorem lineDeriv_lt {D₁ D₂ : ℝ → ℝ} (hb : b ≠ 1) {a c : ℝ} (hac : a < c)
    (hpos : ∀ τ ∈ Icc a c, 0 < s₀ + τ ∧ 0 < w₀ + b * τ)
    (hD₁ : ∀ τ', 0 < s₀ + τ' → 0 < w₀ + b * τ' → s₀ + τ' ≠ w₀ + b * τ' →
      HasDerivAt (fun τ ↦ planeHs (s₀ + τ) (w₀ + b * τ)
        (Real.log (s₀ + τ) - Real.log (w₀ + b * τ))) (D₁ τ') τ')
    (hD₂ : ∀ τ, 0 < s₀ + τ → 0 < w₀ + b * τ → s₀ + τ ≠ w₀ + b * τ →
      HasDerivAt D₁ (D₂ τ) τ ∧ D₂ τ < 0) :
    lineDeriv s₀ w₀ b c < lineDeriv s₀ w₀ b a := by
  refine lt_of_hasDerivAt_neg_off (f' := D₂) (p := (w₀ - s₀) / (1 - b)) hac
    (fun τ hτ ↦ (continuousAt_lineDeriv (hpos τ hτ).1 (hpos τ hτ).2).continuousWithinAt)
    fun τ hτ hp ↦ ?_
  have hτ' := hpos τ (Ioo_subset_Icc_self hτ)
  have hne : s₀ + τ ≠ w₀ + b * τ := by
    intro h
    apply hp
    have : (1 - b) ≠ 0 := sub_ne_zero.mpr hb.symm
    field_simp
    linarith
  have h := hD₂ τ hτ'.1 hτ'.2 hne
  exact ⟨hasDerivAt_lineDeriv_of_ne hτ'.1 hτ'.2 hne hD₁ h.1, h.2⟩

end Line

/-- **Dittmann's inequality (63)**: `hs′(x, x, λ) ≥ hs′(y, y, λ)` for positive `x < y` and `λ`. -/
theorem bkmHsDeriv_ineq63 {x y l : ℝ} (hx : 0 < x) (hxy : x < y) (hl : 0 < l) :
    0 ≤ bkmHsDeriv x x l - bkmHsDeriv y y l := by
  have h := lineDeriv_le (s₀ := 0) (w₀ := l) (b := 0) (D₁ := fun τ ↦
      plane63Deriv (0 + τ) (l + 0 * τ) (Real.log (0 + τ) - Real.log (l + 0 * τ)))
    (D₂ := fun τ ↦ planeEval plane63Num (0 + τ) (l + 0 * τ)
      (Real.log (0 + τ) - Real.log (l + 0 * τ)) / (3 * (Real.log (0 + τ) -
        Real.log (l + 0 * τ)) ^ 4 * (0 + τ) ^ 3 * (l + 0 * τ) * (0 + τ - (l + 0 * τ)) ^ 4))
    zero_ne_one hxy.le (fun τ hτ ↦ ⟨by linarith [hτ.1], by simpa using hl⟩)
    (fun τ hS hW hne ↦ hasDerivAt_planeHs_fst ((hasDerivAt_id τ).const_add 0)
      (by simpa using hasDerivAt_const τ l) hS hW hne)
    fun τ hS hW hne ↦ ⟨hasDerivAt_plane63Deriv ((hasDerivAt_id τ).const_add 0)
      (by simpa using hasDerivAt_const τ l) hS hW hne,
      div_nonpos_of_nonpos_of_nonneg (plane63Num_nonpos hS hW) (by positivity)⟩
  simp only [lineDeriv, zero_add, zero_mul, add_zero] at h
  linarith

/-- **Dittmann's inequality (62)**: `2 hs′(x, x, y) - hs′(y, x, x) - 2 hs′(y, x, y) + hs′(x, y, y)
≥ 0` for positive `x < y`. -/
theorem bkmHsDeriv_ineq62 {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 ≤ 2 * bkmHsDeriv x x y - bkmHsDeriv y x x - 2 * bkmHsDeriv y x y + bkmHsDeriv x y y := by
  have hW : ∀ τ, HasDerivAt (fun τ ↦ y + -1 * τ) (-1) τ := fun τ ↦ by
    simpa using ((hasDerivAt_id τ).const_mul (-1 : ℝ)).const_add y
  have h := lineDeriv_le (s₀ := x) (w₀ := y) (b := -1) (D₁ := fun τ ↦
      plane62Deriv (x + τ) (y + -1 * τ) (Real.log (x + τ) - Real.log (y + -1 * τ)))
    (D₂ := fun τ ↦ planeEval plane62Num (x + τ) (y + -1 * τ)
      (Real.log (x + τ) - Real.log (y + -1 * τ)) / (3 * (Real.log (x + τ) -
        Real.log (y + -1 * τ)) ^ 4 * (x + τ) ^ 3 * (y + -1 * τ) ^ 3 * (x + τ - (y + -1 * τ)) ^ 4))
    (by norm_num) (sub_nonneg.mpr hxy.le)
    (fun τ hτ ↦ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
    (fun τ hS hW' hne ↦ hasDerivAt_planeHs_anti ((hasDerivAt_id τ).const_add x) (hW τ) hS hW' hne)
    fun τ hS hW' hne ↦ ⟨hasDerivAt_plane62Deriv ((hasDerivAt_id τ).const_add x) (hW τ) hS hW' hne,
      div_nonpos_of_nonpos_of_nonneg (plane62Num_nonpos hS hW') (by positivity)⟩
  have e1 : x + (y - x) = y := by ring
  have e2 : y + -1 * (y - x) = x := by ring
  simp only [lineDeriv, add_zero, mul_zero, e1, e2] at h
  rw [bkmHsDeriv_comm₂₃ y x y]
  linarith

/-- **Dittmann's inequality (62), strict**: `2 hs′(x, x, y) - hs′(y, x, x) - 2 hs′(y, x, y) +
hs′(x, y, y) > 0` for positive `x < y`. -/
theorem bkmHsDeriv_ineq62_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < 2 * bkmHsDeriv x x y - bkmHsDeriv y x x - 2 * bkmHsDeriv y x y + bkmHsDeriv x y y := by
  have hW : ∀ τ, HasDerivAt (fun τ ↦ y + -1 * τ) (-1) τ := fun τ ↦ by
    simpa using ((hasDerivAt_id τ).const_mul (-1 : ℝ)).const_add y
  have h := lineDeriv_lt (s₀ := x) (w₀ := y) (b := -1) (D₁ := fun τ ↦
      plane62Deriv (x + τ) (y + -1 * τ) (Real.log (x + τ) - Real.log (y + -1 * τ)))
    (D₂ := fun τ ↦ planeEval plane62Num (x + τ) (y + -1 * τ)
      (Real.log (x + τ) - Real.log (y + -1 * τ)) / (3 * (Real.log (x + τ) -
        Real.log (y + -1 * τ)) ^ 4 * (x + τ) ^ 3 * (y + -1 * τ) ^ 3 * (x + τ - (y + -1 * τ)) ^ 4))
    (by norm_num) (sub_pos.mpr hxy)
    (fun τ hτ ↦ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
    (fun τ hS hW' hne ↦ hasDerivAt_planeHs_anti ((hasDerivAt_id τ).const_add x) (hW τ) hS hW' hne)
    fun τ hS hW' hne ↦ ⟨hasDerivAt_plane62Deriv ((hasDerivAt_id τ).const_add x) (hW τ) hS hW' hne,
      div_neg_of_neg_of_pos (plane62Num_neg hS hW' hne) (by
        have h₁ := sub_ne_zero.mpr hne
        have h₂ := sub_ne_zero.mpr (Real.log_injOn_pos.ne hS hW' hne)
        have h₃ : 0 < x + τ := hS
        have h₄ : 0 < y + -1 * τ := hW'
        exact mul_pos (mul_pos (mul_pos (mul_pos three_pos (Even.pow_pos (by decide) h₂))
          (pow_pos h₃ 3)) (pow_pos h₄ 3)) (Even.pow_pos (by decide) h₁))⟩
  have e1 : x + (y - x) = y := by ring
  have e2 : y + -1 * (y - x) = x := by ring
  simp only [lineDeriv, add_zero, mul_zero, e1, e2] at h
  rw [bkmHsDeriv_comm₂₃ y x y]
  linarith

end PetzCurvature
