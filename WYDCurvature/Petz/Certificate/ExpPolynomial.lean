/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponential polynomials with nonnegative Taylor coefficients

An exponential polynomial `G(A) = ∑ c e^{E A} Aᵏ` (integer `c`, natural `E`, `k`), given as a list
of triples `(c, E, k)`, is entire, with Taylor coefficients `cₙ = γₙ / n!` at `0`, where
`γₙ = ∑ c Eⁿ⁻ᵏ n (n - 1) ⋯ (n - k + 1)` is an integer (`ExpPolynomial.coef`). If every `γₙ ≥ 0`,
then `G ≥ 0` on `[0, ∞)`. Negative arguments reduce to positive ones: `G(A) = e^{K A} H(-A)` with
`H` the reflected exponential polynomial `∑ c (-1)ᵏ e^{(K - E) B} Bᵏ`.

In two variables, `G(p, q) = ∑ c e^{α p + β q} pⁱ qʲ` with all `γ(m, n) ≥ 0`, `γ(m, n)` being
`m! n!` times the Taylor coefficient of `pᵐ qⁿ`, is `≥ 0` on the quadrant `p, q ≥ 0`: its Taylor
series in `p` has as coefficients exponential polynomials in `q` whose own coefficients are the
`γ(m, n)`. A rectangle `m ≤ M`, `n ≤ N` of the `γ(m, n)` is checked by the kernel in factored
form, grouping the terms by `(α, i)` (`rectOk`, sound by `rectOk_spec`).

The tails need no rectangle. In one variable, if the largest exponent is `K` and the powers are
at most `d`, then `γₘ ≥ K^{m-d} T(m) - K^{m-M} R` for `m ≥ M`, where `T` is the top part in
falling-factorial form and `R = ∑_{E < K} |c| E^{M-k} Mᵏ`, provided `E (M + 1)ᵏ ≤ K Mᵏ` for the
lower terms. `T` is nondecreasing from `M` when its differences of orders `1, …, d` are
nonnegative at `M`. So `γₘ ≥ 0` for all `m ≥ M` follows from conditions at `M` alone
(`tailOk`); below `M` they are checked one by one (`coefOk`). In two variables, the strips
`n ≤ N` and `m ≤ M` are one such check per column or row. In the corner `m ≥ M`, `n ≥ N`, the
conditions in `m` are exponential polynomials in `n`, each with its own tail check (`cornerOk`).
Terms with equal exponents are combined first (`combineG`), since the per-term bound `R` is far
too coarse otherwise.

## Main definitions

* `ExpPolynomial.eval r A`: `∑ c e^{E A} Aᵏ` over the triples `(c, E, k)` of `r`.
* `ExpPolynomial.coef r n`: `n!` times the `n`-th Taylor coefficient at `0`.
* `ExpPolynomial.reflect K r`: the triples `(c (-1)ᵏ, K - E, k)`.
* `ExpPolynomial.eval₂`, `ExpPolynomial.coef₂`: two variables.
* `ExpPolynomial.flatten₂`, `ExpPolynomial.colVec`, `ExpPolynomial.dot`, `ExpPolynomial.rectOk`:
  grouped terms and the factored check of a rectangle of coefficients.
* `ExpPolynomial.evalFF`, `ExpPolynomial.diffFF`, `ExpPolynomial.topFF`, `ExpPolynomial.restLoad`:
  falling-factorial polynomials, their differences, the top part and the load of the rest.
* `ExpPolynomial.tailOk`, `ExpPolynomial.coefOk`: the decidable tail check in one variable, and
  the check of all coefficients.
* `ExpPolynomial.mergeAdd`, `ExpPolynomial.combineG`: combining terms with equal exponents.
* `ExpPolynomial.stripPOk`, `ExpPolynomial.stripQOk`, `ExpPolynomial.cornerOk`: the two strips and
  the corner.

## Main statements

* `ExpPolynomial.hasSum_eval`: the Taylor series of `eval r` at `0`.
* `ExpPolynomial.eval_nonneg`: nonnegative `coef` give `eval r A ≥ 0` for `A ≥ 0`.
* `ExpPolynomial.eval_pos`: if moreover one `coef` is positive, `eval r A > 0` for `A > 0`.
* `ExpPolynomial.eval_reflect`: `eval r A = e^{K A} eval (reflect K r) (-A)`.
* `ExpPolynomial.hasSum_eval₂`, `ExpPolynomial.eval₂_nonneg`: nonnegative coefficients give
  `eval₂ r p q ≥ 0` on the quadrant.
* `ExpPolynomial.dot_colVec`, `ExpPolynomial.rectOk_spec`: soundness of the factored check.
* `ExpPolynomial.evalFF_le_of_diffFF`: monotonicity from finitely many differences.
* `ExpPolynomial.coef_nonneg_of_tail`, `ExpPolynomial.tailOk_spec`, `ExpPolynomial.coefOk_spec`:
  the tail in one variable, and all coefficients.
* `ExpPolynomial.coef₂_nonneg_of_checks`: all `γ(m, n) ≥ 0` from the rectangle, the strips and
  the corner.

-/

open Finset

namespace PetzCurvature.ExpPolynomial

/-- `∑ c e^{E A} Aᵏ` over the triples `(c, E, k)` of `r`. -/
noncomputable def eval (r : List (ℤ × ℕ × ℕ)) (A : ℝ) : ℝ :=
  (r.map fun m ↦ (m.1 : ℝ) * Real.exp (m.2.1 * A) * A ^ m.2.2).sum

/-- `n!` times the `n`-th Taylor coefficient of `eval r` at `0`:
`∑ c Eⁿ⁻ᵏ n (n - 1) ⋯ (n - k + 1)`. -/
def coef (r : List (ℤ × ℕ × ℕ)) (n : ℕ) : ℤ :=
  (r.map fun m ↦ m.1 * ((m.2.1 ^ (n - m.2.2) * n.descFactorial m.2.2 : ℕ) : ℤ)).sum

/-- The Taylor series of `e^{E A} Aᵏ` at `0`. -/
theorem hasSum_exp_mul_pow (E k : ℕ) (A : ℝ) :
    HasSum (fun n ↦ ((E ^ (n - k) * n.descFactorial k : ℕ) : ℝ) / n.factorial * A ^ n)
      (Real.exp (E * A) * A ^ k) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (E * A : ℝ)).mul_right (A ^ k)
  rw [← Real.exp_eq_exp_ℝ] at h
  rw [← hasSum_nat_add_iff' k, Finset.sum_eq_zero fun i hi ↦ by
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr (mem_range.mp hi)], sub_zero]
  convert h using 1
  funext m
  have e := Nat.factorial_mul_descFactorial (Nat.le_add_left k m)
  rw [Nat.add_sub_cancel] at e
  have e' : ((m + k).descFactorial k : ℝ) * m.factorial = (m + k).factorial := by
    rw [mul_comm]; exact_mod_cast e
  have := Nat.factorial_ne_zero m
  have := Nat.factorial_ne_zero (m + k)
  rw [Nat.add_sub_cancel, ← e']
  push_cast
  field_simp
  ring

/-- The Taylor series of an exponential polynomial at `0`. -/
theorem hasSum_eval (r : List (ℤ × ℕ × ℕ)) (A : ℝ) :
    HasSum (fun n ↦ (coef r n : ℝ) / n.factorial * A ^ n) (eval r A) := by
  induction r with
  | nil => simp [coef, eval, hasSum_zero]
  | cons m r ih =>
    convert ((hasSum_exp_mul_pow m.2.1 m.2.2 A).mul_left (m.1 : ℝ)).add ih using 1
    · funext n
      simp only [coef, List.map_cons, List.sum_cons]
      push_cast
      ring
    · simp only [eval, List.map_cons, List.sum_cons]
      ring

/-- **Nonnegative Taylor coefficients**: if every `coef r n ≥ 0`, then `eval r A ≥ 0` for
`A ≥ 0`. -/
theorem eval_nonneg {r : List (ℤ × ℕ × ℕ)} (h : ∀ n, 0 ≤ coef r n) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ eval r A :=
  (hasSum_eval r A).nonneg fun n ↦ by
    have := h n
    have : (0 : ℝ) ≤ coef r n := by exact_mod_cast this
    positivity

/-- **Nonnegative Taylor coefficients, one positive**: if every `coef r n ≥ 0` and some
`coef r N > 0`, then `eval r A > 0` for `A > 0`. -/
theorem eval_pos {r : List (ℤ × ℕ × ℕ)} (h : ∀ n, 0 ≤ coef r n) {N : ℕ} (hN : 0 < coef r N)
    {A : ℝ} (hA : 0 < A) : 0 < eval r A := by
  refine hasSum_lt (f := fun _ ↦ (0 : ℝ)) (i := N) (fun n ↦ ?_) ?_ hasSum_zero (hasSum_eval r A)
  · have := h n
    have : (0 : ℝ) ≤ coef r n := by exact_mod_cast this
    positivity
  · have : (0 : ℝ) < coef r N := by exact_mod_cast hN
    positivity

/-- The reflected exponential polynomial: `(c, E, k) ↦ (c (-1)ᵏ, K - E, k)`. -/
def reflect (K : ℕ) (r : List (ℤ × ℕ × ℕ)) : List (ℤ × ℕ × ℕ) :=
  r.map fun m ↦ (m.1 * (-1) ^ m.2.2, K - m.2.1, m.2.2)

/-- `eval r A = e^{K A} eval (reflect K r) (-A)` when every exponent is at most `K`. -/
theorem eval_reflect {K : ℕ} {r : List (ℤ × ℕ × ℕ)} (hK : ∀ m ∈ r, m.2.1 ≤ K) (A : ℝ) :
    eval r A = Real.exp (K * A) * eval (reflect K r) (-A) := by
  rw [eval, eval, reflect, List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun m hm ↦ ?_)
  have hm' := hK m hm
  simp only [Function.comp_apply]
  push_cast
  rw [Nat.cast_sub hm', neg_pow]
  have e : Real.exp (m.2.1 * A) = Real.exp (K * A) * Real.exp ((K - m.2.1) * -A) := by
    rw [← Real.exp_add]; ring_nf
  have : ((-1 : ℝ) ^ m.2.2) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [e]
  linear_combination (-(m.1 : ℝ) * Real.exp (K * A) * Real.exp ((K - m.2.1) * -A) *
    A ^ m.2.2) * this

/-! ### Two variables -/

/-- `∑ c e^{α p} pⁱ e^{β q} qʲ` over the terms `(c, α, i, β, j)` of `r`. -/
noncomputable def eval₂ (r : List (ℤ × ℕ × ℕ × ℕ × ℕ)) (p q : ℝ) : ℝ :=
  (r.map fun (c, α, i, β, j) ↦
    (c : ℝ) * Real.exp (α * p) * p ^ i * (Real.exp (β * q) * q ^ j)).sum

/-- `m! n!` times the Taylor coefficient of `pᵐ qⁿ` of `eval₂ r` at `0`. -/
def coef₂ (r : List (ℤ × ℕ × ℕ × ℕ × ℕ)) (m n : ℕ) : ℤ :=
  (r.map fun (c, α, i, β, j) ↦ c * ((α ^ (m - i) * m.descFactorial i : ℕ) : ℤ) *
    ((β ^ (n - j) * n.descFactorial j : ℕ) : ℤ)).sum

/-- The exponential polynomial in `q` that multiplies `pᵐ / m!` in `eval₂ r`. -/
def row (r : List (ℤ × ℕ × ℕ × ℕ × ℕ)) (m : ℕ) : List (ℤ × ℕ × ℕ) :=
  r.map fun (c, α, i, β, j) ↦ (c * ((α ^ (m - i) * m.descFactorial i : ℕ) : ℤ), β, j)

theorem coef_row (r : List (ℤ × ℕ × ℕ × ℕ × ℕ)) (m n : ℕ) : coef (row r m) n = coef₂ r m n := by
  induction r with
  | nil => rfl
  | cons t r ih =>
    obtain ⟨c, α, i, β, j⟩ := t
    simp only [row, coef, coef₂, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

/-- The Taylor series of `eval₂ r` in `p`, with coefficients exponential polynomials in `q`. -/
theorem hasSum_eval₂ (r : List (ℤ × ℕ × ℕ × ℕ × ℕ)) (p q : ℝ) :
    HasSum (fun m ↦ eval (row r m) q / m.factorial * p ^ m) (eval₂ r p q) := by
  induction r with
  | nil => simp [eval, eval₂, row, hasSum_zero]
  | cons t r ih =>
    obtain ⟨c, α, i, β, j⟩ := t
    convert ((hasSum_exp_mul_pow α i p).mul_left
      ((c : ℝ) * (Real.exp (β * q) * q ^ j))).add ih using 1
    · funext m
      simp only [row, eval, List.map_cons, List.sum_cons]
      push_cast
      ring
    · simp only [eval₂, List.map_cons, List.sum_cons]
      ring

/-- **Nonnegative Taylor coefficients in two variables**: if every `coef₂ r m n ≥ 0`, then
`eval₂ r p q ≥ 0` for `p, q ≥ 0`. -/
theorem eval₂_nonneg {r : List (ℤ × ℕ × ℕ × ℕ × ℕ)} (h : ∀ m n, 0 ≤ coef₂ r m n) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) : 0 ≤ eval₂ r p q :=
  (hasSum_eval₂ r p q).nonneg fun m ↦ by
    have := eval_nonneg (r := row r m) (fun n ↦ (coef_row r m n).symm ▸ h m n) hq
    positivity

/-! ### The factored kernel check of a rectangle of coefficients -/

/-- Terms grouped by `(α, i)`: `(α, i, [(c, β, j)])` stands for the terms `(c, α, i, β, j)`. -/
def flatten₂ (G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))) : List (ℤ × ℕ × ℕ × ℕ × ℕ) :=
  G.flatMap fun (α, i, L) ↦ L.map fun (c, β, j) ↦ (c, α, i, β, j)

/-- For each group, `(α, i, ∑ c β^{n-j} (n)_j)`. -/
def colVec (G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))) (n : ℕ) : List (ℕ × ℕ × ℤ) :=
  G.map fun (α, i, L) ↦ (α, i, coef L n)

/-- `∑ α^{m-i} (m)_i s` over `(α, i, s)`. -/
def dot (w : List (ℕ × ℕ × ℤ)) (m : ℕ) : ℤ :=
  (w.map fun (α, i, s) ↦ ((α ^ (m - i) * m.descFactorial i : ℕ) : ℤ) * s).sum

theorem coef₂_append (r r' : List (ℤ × ℕ × ℕ × ℕ × ℕ)) (m n : ℕ) :
    coef₂ (r ++ r') m n = coef₂ r m n + coef₂ r' m n := by
  simp [coef₂]

theorem coef₂_map (α i : ℕ) (L : List (ℤ × ℕ × ℕ)) (m n : ℕ) :
    coef₂ (L.map fun (c, β, j) ↦ (c, α, i, β, j)) m n =
      ((α ^ (m - i) * m.descFactorial i : ℕ) : ℤ) * coef L n := by
  induction L with
  | nil => simp [coef₂, coef]
  | cons t L ih =>
    obtain ⟨c, β, j⟩ := t
    simp only [coef₂, coef, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring

/-- The factored evaluation computes the coefficients: `γ(m, n) = ∑ α^{m-i}(m)_i W_n`. -/
theorem dot_colVec (G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))) (m n : ℕ) :
    dot (colVec G n) m = coef₂ (flatten₂ G) m n := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    obtain ⟨α, i, L⟩ := g
    rw [show flatten₂ ((α, i, L) :: G) =
      (L.map fun (c, β, j) ↦ (c, α, i, β, j)) ++ flatten₂ G from rfl, coef₂_append, coef₂_map,
      ← ih]
    rfl

/-- The check of one column: `0 ≤ dot w m` for all `m ≤ M`. -/
def colOk (w : List (ℕ × ℕ × ℤ)) : ℕ → Bool
  | 0 => decide (0 ≤ dot w 0)
  | m + 1 => decide (0 ≤ dot w (m + 1)) && colOk w m

/-- The check of the rectangle `m ≤ M`, `n ≤ N`, column by column. -/
def rectOk (G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))) (M : ℕ) : ℕ → Bool
  | 0 => colOk (colVec G 0) M
  | n + 1 => colOk (colVec G (n + 1)) M && rectOk G M n

theorem colOk_spec {w : List (ℕ × ℕ × ℤ)} {M : ℕ} (h : colOk w M = true) :
    ∀ m ≤ M, 0 ≤ dot w m := by
  induction M with
  | zero =>
    intro m hm
    obtain rfl : m = 0 := by omega
    simpa [colOk] using h
  | succ M ih =>
    simp only [colOk, Bool.and_eq_true, decide_eq_true_eq] at h
    intro m hm
    rcases Nat.lt_or_ge m (M + 1) with hm' | hm'
    · exact ih h.2 m (by omega)
    · obtain rfl : m = M + 1 := by omega
      exact h.1

/-- **Soundness of the rectangle check**. -/
theorem rectOk_spec {G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))} {M N : ℕ} (h : rectOk G M N = true) :
    ∀ m ≤ M, ∀ n ≤ N, 0 ≤ coef₂ (flatten₂ G) m n := by
  induction N with
  | zero =>
    intro m hm n hn
    obtain rfl : n = 0 := by omega
    rw [← dot_colVec]
    exact colOk_spec (by simpa [rectOk] using h) m hm
  | succ N ih =>
    simp only [rectOk, Bool.and_eq_true] at h
    intro m hm n hn
    rcases Nat.lt_or_ge n (N + 1) with hn' | hn'
    · exact ih h.2 m hm n (by omega)
    · obtain rfl : n = N + 1 := by omega
      rw [← dot_colVec]
      exact colOk_spec h.1 m hm

/-! ### Tails: dominance of the top exponent from finitely many conditions -/

theorem coef_nil (n : ℕ) : coef [] n = 0 := rfl

theorem coef_cons (t : ℤ × ℕ × ℕ) (l : List (ℤ × ℕ × ℕ)) (n : ℕ) :
    coef (t :: l) n = t.1 * ((t.2.1 ^ (n - t.2.2) * n.descFactorial t.2.2 : ℕ) : ℤ) + coef l n :=
  by simp [coef]

theorem coef_append (l l' : List (ℤ × ℕ × ℕ)) (n : ℕ) :
    coef (l ++ l') n = coef l n + coef l' n := by
  simp [coef]

/-- `∑ c (m)ₖ` over the pairs `(c, k)` of `l`: a polynomial in falling-factorial form. -/
def evalFF (l : List (ℤ × ℕ)) (m : ℕ) : ℤ :=
  (l.map fun t ↦ t.1 * (m.descFactorial t.2 : ℤ)).sum

/-- The `j`-th forward difference of `evalFF l`: `(c, k) ↦ (c (k)ⱼ, k - j)`. -/
def diffFF (j : ℕ) (l : List (ℤ × ℕ)) : List (ℤ × ℕ) :=
  l.map fun t ↦ (t.1 * (t.2.descFactorial j : ℤ), t.2 - j)

theorem succ_descFactorial_eq (m k : ℕ) :
    (m + 1).descFactorial k = m.descFactorial k + k * m.descFactorial (k - 1) := by
  rcases k with _ | k
  · simp
  rw [Nat.succ_descFactorial_succ, Nat.descFactorial_succ, Nat.add_sub_cancel]
  rcases le_or_gt k m with h | h
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show k + a - k = a by omega]
    ring
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr h]

theorem evalFF_succ (l : List (ℤ × ℕ)) (m : ℕ) :
    evalFF l (m + 1) = evalFF l m + evalFF (diffFF 1 l) m := by
  induction l with
  | nil => simp [evalFF, diffFF]
  | cons t l ih =>
    simp only [evalFF, diffFF, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, succ_descFactorial_eq, Nat.descFactorial_one]
    push_cast
    ring

theorem diffFF_diffFF_one (j : ℕ) (l : List (ℤ × ℕ)) :
    diffFF j (diffFF 1 l) = diffFF (j + 1) l := by
  simp only [diffFF, List.map_map]
  refine List.map_congr_left fun t _ ↦ ?_
  obtain ⟨c, k⟩ := t
  rcases k with _ | k
  · simp
  · simp only [Function.comp_apply, Nat.descFactorial_one, Nat.add_sub_cancel,
      Nat.succ_descFactorial_succ, Prod.mk.injEq]
    constructor
    · push_cast; ring
    · omega

/-- `evalFF l` is nondecreasing from `M` when its first difference is nonnegative there. -/
theorem evalFF_le_of_diff {l : List (ℤ × ℕ)} {M : ℕ}
    (h : ∀ x, M ≤ x → 0 ≤ evalFF (diffFF 1 l) x) {m : ℕ} (hm : M ≤ m) :
    evalFF l M ≤ evalFF l m := by
  induction m, hm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => rw [evalFF_succ]; linarith [h m hm]

/-- **Monotonicity from finitely many differences**: if every term has degree at most `d` and
the differences of orders `1, …, d` are nonnegative at `M`, then `evalFF l` is nondecreasing from
`M`. -/
theorem evalFF_le_of_diffFF {d : ℕ} {l : List (ℤ × ℕ)} {M : ℕ} (hd : ∀ t ∈ l, t.2 ≤ d)
    (h : ∀ j ∈ Icc 1 d, 0 ≤ evalFF (diffFF j l) M) {m : ℕ} (hm : M ≤ m) :
    evalFF l M ≤ evalFF l m := by
  induction d generalizing l m with
  | zero =>
    refine evalFF_le_of_diff (fun x _ ↦ le_of_eq ?_) hm
    simp only [evalFF, diffFF, List.map_map]
    refine (List.sum_eq_zero fun y hy ↦ ?_).symm
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    simp [Nat.le_zero.mp (hd t ht)]
  | succ d ih =>
    have hd' : ∀ t ∈ diffFF 1 l, t.2 ≤ d := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have := hd s hs
      simp only
      omega
    have h' : ∀ j ∈ Icc 1 d, 0 ≤ evalFF (diffFF j (diffFF 1 l)) M := fun j hj ↦ by
      rw [diffFF_diffFF_one]
      exact h (j + 1) (by simp only [mem_Icc] at hj ⊢; omega)
    exact evalFF_le_of_diff (fun x hx ↦ (h 1 (by simp)).trans (ih hd' h' hx)) hm

/-- `E^{m-k} mᵏ ≤ K^{m-M} E^{M-k} Mᵏ` for `m ≥ M`, from the ratio condition at `M`. -/
theorem pow_sub_mul_pow_le {E K M k : ℕ} (hkM : k ≤ M) (hM : 1 ≤ M)
    (h : E * (M + 1) ^ k ≤ K * M ^ k) {m : ℕ} (hm : M ≤ m) :
    E ^ (m - k) * m ^ k ≤ K ^ (m - M) * (E ^ (M - k) * M ^ k) := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h2 : ((m + 1) * M) ^ k ≤ ((M + 1) * m) ^ k := Nat.pow_le_pow_left (by nlinarith) k
    rw [mul_pow, mul_pow] at h2
    have h3 : E * (m + 1) ^ k ≤ K * m ^ k := by
      refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (by omega : 0 < M) k)
      calc E * (m + 1) ^ k * M ^ k = E * ((m + 1) ^ k * M ^ k) := by ring
        _ ≤ E * ((M + 1) ^ k * m ^ k) := Nat.mul_le_mul_left _ h2
        _ = E * (M + 1) ^ k * m ^ k := by ring
        _ ≤ K * M ^ k * m ^ k := Nat.mul_le_mul_right _ h
        _ = K * m ^ k * M ^ k := by ring
    calc E ^ (m + 1 - k) * (m + 1) ^ k = E ^ (m - k) * (E * (m + 1) ^ k) := by
          rw [show m + 1 - k = m - k + 1 by omega, pow_succ]; ring
      _ ≤ E ^ (m - k) * (K * m ^ k) := Nat.mul_le_mul_left _ h3
      _ = K * (E ^ (m - k) * m ^ k) := by ring
      _ ≤ K * (K ^ (m - M) * (E ^ (M - k) * M ^ k)) := Nat.mul_le_mul_left _ ih
      _ = K ^ (m + 1 - M) * (E ^ (M - k) * M ^ k) := by
          rw [show m + 1 - M = m - M + 1 by omega, pow_succ]; ring

/-- The top part in falling-factorial form: `(c K^{d-k}, k)` over the terms with `E = K`. -/
def topFF (p : List (ℤ × ℕ × ℕ)) (K d : ℕ) : List (ℤ × ℕ) :=
  (p.filter fun t ↦ t.2.1 = K).map fun t ↦ (t.1 * ((K ^ (d - t.2.2) : ℕ) : ℤ), t.2.2)

/-- `∑_{E < K} |c| E^{M-k} Mᵏ`. -/
def restLoad (p : List (ℤ × ℕ × ℕ)) (K M : ℕ) : ℕ :=
  ((p.filter fun t ↦ t.2.1 < K).map fun t ↦ t.1.natAbs * (t.2.1 ^ (M - t.2.2) * M ^ t.2.2)).sum

/-- `γₘ ≥ K^{m-d} T(m) - K^{m-M} R` for `m ≥ M`. -/
theorem coef_ge_tail {p : List (ℤ × ℕ × ℕ)} {K d M : ℕ} (hdM : d ≤ M) (hM : 1 ≤ M)
    (hE : ∀ t ∈ p, t.2.1 ≤ K) (hk : ∀ t ∈ p, t.2.2 ≤ d)
    (hr : ∀ t ∈ p, t.2.1 < K → t.2.1 * (M + 1) ^ t.2.2 ≤ K * M ^ t.2.2) {m : ℕ} (hm : M ≤ m) :
    (K : ℤ) ^ (m - d) * evalFF (topFF p K d) m - ((K ^ (m - M) * restLoad p K M : ℕ) : ℤ) ≤
      coef p m := by
  induction p with
  | nil => simp [topFF, restLoad, evalFF, coef]
  | cons t p ih =>
    rw [List.forall_mem_cons] at hE hk hr
    have h := ih hE.2 hk.2 hr.2
    obtain ⟨c, E, k⟩ := t
    simp only at hE hk hr
    rw [coef_cons]
    by_cases hEK : E = K
    · subst hEK
      have hrest : restLoad ((c, E, k) :: p) E M = restLoad p E M := by simp [restLoad]
      have htop : evalFF (topFF ((c, E, k) :: p) E d) m =
          c * ((E ^ (d - k) : ℕ) : ℤ) * (m.descFactorial k : ℤ) + evalFF (topFF p E d) m := by
        simp [topFF, evalFF]
      rw [hrest, htop]
      have hp : (E : ℤ) ^ (m - d) * (E : ℤ) ^ (d - k) = (E : ℤ) ^ (m - k) := by
        rw [← pow_add, show m - d + (d - k) = m - k by omega]
      push_cast at h ⊢
      linear_combination h + c * (m.descFactorial k : ℤ) * hp
    · have hlt : E < K := lt_of_le_of_ne hE.1 hEK
      have hrest : restLoad ((c, E, k) :: p) K M =
          c.natAbs * (E ^ (M - k) * M ^ k) + restLoad p K M := by
        simp [restLoad, hlt]
      have htop : topFF ((c, E, k) :: p) K d = topFF p K d := by simp [topFF, hEK]
      rw [hrest, htop]
      have hb : E ^ (m - k) * m.descFactorial k ≤ K ^ (m - M) * (E ^ (M - k) * M ^ k) :=
        (Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow m k)).trans
          (pow_sub_mul_pow_le (by omega) hM (hr.1 hlt) hm)
      have hb' : |c * ((E ^ (m - k) * m.descFactorial k : ℕ) : ℤ)| ≤
          (c.natAbs : ℤ) * ((K ^ (m - M) * (E ^ (M - k) * M ^ k) : ℕ) : ℤ) := by
        rw [abs_mul, Int.abs_natCast, ← Int.natCast_natAbs]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hb) (by positivity)
      have := neg_abs_le (c * ((E ^ (m - k) * m.descFactorial k : ℕ) : ℤ))
      push_cast at h hb' this ⊢
      linarith

/-- **Tail by dominance of the top exponent**: `γₘ ≥ 0` for all `m ≥ M` from finitely many
conditions at `M`: the ratio conditions of the lower exponents, the differences of the top part,
and the comparison of the top part with the load of the lower ones. -/
theorem coef_nonneg_of_tail {p : List (ℤ × ℕ × ℕ)} {K d M : ℕ} (hdM : d ≤ M) (hM : 1 ≤ M)
    (hE : ∀ t ∈ p, t.2.1 ≤ K) (hk : ∀ t ∈ p, t.2.2 ≤ d)
    (hr : ∀ t ∈ p, t.2.1 < K → t.2.1 * (M + 1) ^ t.2.2 ≤ K * M ^ t.2.2)
    (hΔ : ∀ j ∈ Icc 1 d, 0 ≤ evalFF (diffFF j (topFF p K d)) M)
    (hb : (restLoad p K M : ℤ) ≤ (K : ℤ) ^ (M - d) * evalFF (topFF p K d) M)
    {m : ℕ} (hm : M ≤ m) : 0 ≤ coef p m := by
  have h := coef_ge_tail hdM hM hE hk hr hm
  have hT : evalFF (topFF p K d) M ≤ evalFF (topFF p K d) m := by
    refine evalFF_le_of_diffFF (fun t ht ↦ ?_) hΔ hm
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact hk s (List.mem_of_mem_filter hs)
  have hpow : (K : ℤ) ^ (m - d) = (K : ℤ) ^ (m - M) * (K : ℤ) ^ (M - d) := by
    rw [← pow_add, show m - M + (M - d) = m - d by omega]
  have hK0 : (0 : ℤ) ≤ (K : ℤ) ^ (m - M) := by positivity
  have hK1 : (0 : ℤ) ≤ (K : ℤ) ^ (m - d) := by positivity
  have e1 := mul_le_mul_of_nonneg_left hT hK1
  have e2 := mul_le_mul_of_nonneg_left hb hK0
  push_cast at h
  rw [hpow] at e1 h
  rw [← mul_assoc] at e2
  linarith

/-! ### Decidable tail checks -/

/-- The largest exponent `E` of the terms. -/
def maxE (p : List (ℤ × ℕ × ℕ)) : ℕ := p.foldr (fun t a ↦ max t.2.1 a) 0

/-- The largest power `k` of the terms. -/
def maxK (p : List (ℤ × ℕ × ℕ)) : ℕ := p.foldr (fun t a ↦ max t.2.2 a) 0

theorem le_maxE {p : List (ℤ × ℕ × ℕ)} : ∀ t ∈ p, t.2.1 ≤ maxE p := by
  induction p with
  | nil => simp
  | cons s p ih =>
    simp only [List.forall_mem_cons, maxE, List.foldr_cons] at ih ⊢
    exact ⟨le_max_left _ _, fun t ht ↦ (ih t ht).trans (le_max_right _ _)⟩

theorem le_maxK {p : List (ℤ × ℕ × ℕ)} : ∀ t ∈ p, t.2.2 ≤ maxK p := by
  induction p with
  | nil => simp
  | cons s p ih =>
    simp only [List.forall_mem_cons, maxK, List.foldr_cons] at ih ⊢
    exact ⟨le_max_left _ _, fun t ht ↦ (ih t ht).trans (le_max_right _ _)⟩

/-- The conditions of `coef_nonneg_of_tail` at `M`, with `K = maxE p` and `d = maxK p`. -/
def tailCheck (p : List (ℤ × ℕ × ℕ)) (M : ℕ) : Bool :=
  decide (maxK p ≤ M) && decide (1 ≤ M) &&
    p.all (fun t ↦ decide (maxE p ≤ t.2.1) ||
      decide (t.2.1 * (M + 1) ^ t.2.2 ≤ maxE p * M ^ t.2.2)) &&
    (List.range (maxK p)).all (fun j ↦
      decide (0 ≤ evalFF (diffFF (j + 1) (topFF p (maxE p) (maxK p))) M)) &&
    decide ((restLoad p (maxE p) M : ℤ) ≤
      (maxE p : ℤ) ^ (M - maxK p) * evalFF (topFF p (maxE p) (maxK p)) M)

/-- The tail check after dropping the zero terms. -/
def tailOk (l : List (ℤ × ℕ × ℕ)) (M : ℕ) : Bool :=
  tailCheck (l.filter fun t ↦ t.1 != 0) M

theorem coef_filter_ne_zero (l : List (ℤ × ℕ × ℕ)) (n : ℕ) :
    coef (l.filter fun t ↦ t.1 != 0) n = coef l n := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    by_cases h : t.1 = 0
    · simp [h, coef_cons, ih]
    · simp [h, coef_cons, ih]

theorem tailCheck_spec {p : List (ℤ × ℕ × ℕ)} {M : ℕ} (h : tailCheck p M = true) {m : ℕ}
    (hm : M ≤ m) : 0 ≤ coef p m := by
  simp only [tailCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hdM, hM⟩, hr⟩, hΔ⟩, hb⟩ := h
  refine coef_nonneg_of_tail hdM hM le_maxE le_maxK (fun t ht hlt ↦ ?_) (fun j hj ↦ ?_) hb hm
  · exact (hr t ht).resolve_left (by omega)
  · simp only [mem_Icc] at hj
    have := hΔ (j - 1) (by omega)
    rwa [Nat.sub_add_cancel hj.1] at this

/-- **Soundness of the tail check**: `γₘ ≥ 0` for all `m ≥ M`. -/
theorem tailOk_spec {l : List (ℤ × ℕ × ℕ)} {M : ℕ} (h : tailOk l M = true) {m : ℕ}
    (hm : M ≤ m) : 0 ≤ coef l m :=
  coef_filter_ne_zero l m ▸ tailCheck_spec h hm

/-- All Taylor coefficients: checked one by one below `M`, by the tail check from `M`. -/
def coefOk (l : List (ℤ × ℕ × ℕ)) (M : ℕ) : Bool :=
  (List.range M).all (fun n ↦ decide (0 ≤ coef l n)) && tailOk l M

/-- **Soundness of `coefOk`**: `γₙ ≥ 0` for all `n`. -/
theorem coefOk_spec {l : List (ℤ × ℕ × ℕ)} {M : ℕ} (h : coefOk l M = true) (n : ℕ) :
    0 ≤ coef l n := by
  simp only [coefOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  rcases lt_or_ge n M with hn | hn
  · exact h.1 n hn
  · exact tailOk_spec h.2 hn

/-! ### Combining equal terms -/

/-- Merge two term lists, adding the coefficients of equal `(E, k)` when they meet. Sound for any
fuel; with `a.length + b.length` and both lists sorted it merges them completely. -/
def mergeAdd : ℕ → List (ℤ × ℕ × ℕ) → List (ℤ × ℕ × ℕ) → List (ℤ × ℕ × ℕ)
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, s :: a, [] => s :: a
  | f + 1, s :: a, t :: b =>
    if s.2 = t.2 then (s.1 + t.1, s.2) :: mergeAdd f a b
    else if s.2.1 < t.2.1 ∨ s.2.1 = t.2.1 ∧ s.2.2 < t.2.2 then s :: mergeAdd f a (t :: b)
    else t :: mergeAdd f (s :: a) b

theorem coef_mergeAdd (f : ℕ) (a b : List (ℤ × ℕ × ℕ)) (n : ℕ) :
    coef (mergeAdd f a b) n = coef a n + coef b n := by
  induction f generalizing a b with
  | zero => simp [mergeAdd, coef_append]
  | succ f ih =>
    rcases a with _ | ⟨s, a⟩ <;> rcases b with _ | ⟨t, b⟩
    · simp [mergeAdd, coef_nil]
    · simp [mergeAdd, coef_nil]
    · simp [mergeAdd, coef_nil]
    · simp only [mergeAdd]
      split_ifs with h1 h2
      · simp only [coef_cons, ih, h1]
        push_cast; ring
      · simp only [coef_cons, ih]; ring
      · simp only [coef_cons, ih]; ring

/-- `(f α i c, β, j)` for the terms `(c, α, i, β, j)`. -/
def mapTerms (f : ℕ → ℕ → ℤ → ℤ) (r : List (ℤ × ℕ × ℕ × ℕ × ℕ)) : List (ℤ × ℕ × ℕ) :=
  r.map fun (c, α, i, β, j) ↦ (f α i c, β, j)

/-- `mapTerms f (flatten₂ G)`, combined over equal `(β, j)` by merging group by group. -/
def combineG (f : ℕ → ℕ → ℤ → ℤ) (G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))) : List (ℤ × ℕ × ℕ) :=
  G.foldr (fun g acc ↦ mergeAdd (g.2.2.length + acc.length)
    (g.2.2.map fun t ↦ (f g.1 g.2.1 t.1, t.2)) acc) []

theorem coef_combineG (f : ℕ → ℕ → ℤ → ℤ) (G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))) (n : ℕ) :
    coef (combineG f G) n = coef (mapTerms f (flatten₂ G)) n := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    obtain ⟨α, i, L⟩ := g
    have e : flatten₂ ((α, i, L) :: G) =
        (L.map fun (c, β, j) ↦ (c, α, i, β, j)) ++ flatten₂ G := rfl
    simp only [combineG, List.foldr_cons] at ih ⊢
    rw [coef_mergeAdd, ih, e, mapTerms, mapTerms, List.map_append, coef_append, List.map_map]
    rfl

/-! ### Strips and corner -/

/-- The exponential polynomial in `p` that multiplies `qⁿ / n!` in `eval₂ r`. -/
def col (r : List (ℤ × ℕ × ℕ × ℕ × ℕ)) (n : ℕ) : List (ℤ × ℕ × ℕ) :=
  r.map fun (c, α, i, β, j) ↦ (c * ((β ^ (n - j) * n.descFactorial j : ℕ) : ℤ), α, i)

theorem coef_col (r : List (ℤ × ℕ × ℕ × ℕ × ℕ)) (m n : ℕ) : coef (col r n) m = coef₂ r m n := by
  induction r with
  | nil => rfl
  | cons t r ih =>
    obtain ⟨c, α, i, β, j⟩ := t
    simp only [col, coef, coef₂, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring

/-- The terms `(s, α, i)` of the grouped column `(α, i, s)`. -/
def triples (w : List (ℕ × ℕ × ℤ)) : List (ℤ × ℕ × ℕ) := w.map fun (α, i, s) ↦ (s, α, i)

theorem coef_triples (w : List (ℕ × ℕ × ℤ)) (m : ℕ) : coef (triples w) m = dot w m := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    obtain ⟨α, i, s⟩ := t
    simp only [triples, coef, dot, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring

/-- The weight of row `m`: `c ↦ c α^{m-i} (m)ᵢ`. -/
def rowWeight (m α i : ℕ) (c : ℤ) : ℤ := c * ((α ^ (m - i) * m.descFactorial i : ℕ) : ℤ)

/-- The strip `n ≤ N`, `m ≥ M`: one tail check in `m` per column. -/
def stripPOk (G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))) (M N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n ↦ tailOk (triples (colVec G n)) M

/-- The strip `m ≤ M`, `n ≥ N`: one tail check in `n` per row, after combining. -/
def stripQOk (G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))) (M N : ℕ) : Bool :=
  (List.range (M + 1)).all fun m ↦ tailOk (combineG (rowWeight m) G) N

theorem stripPOk_spec {G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))} {M N : ℕ}
    (h : stripPOk G M N = true) {m n : ℕ} (hm : M ≤ m) (hn : n ≤ N) :
    0 ≤ coef₂ (flatten₂ G) m n := by
  simp only [stripPOk, List.all_eq_true, List.mem_range] at h
  rw [← dot_colVec, ← coef_triples]
  exact tailOk_spec (h n (by omega)) hm

theorem stripQOk_spec {G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))} {M N : ℕ}
    (h : stripQOk G M N = true) {m n : ℕ} (hm : m ≤ M) (hn : N ≤ n) :
    0 ≤ coef₂ (flatten₂ G) m n := by
  simp only [stripQOk, List.all_eq_true, List.mem_range] at h
  have := tailOk_spec (h m (by omega)) hn
  rwa [coef_combineG, show mapTerms (rowWeight m) (flatten₂ G) = row (flatten₂ G) m from rfl,
    coef_row] at this

/-- The differences of the top part of `col r n` at `M`, as terms in `n`. -/
def topWeight (K d M j α i : ℕ) (c : ℤ) : ℤ :=
  if α = K then c * ((K ^ (d - i) * i.descFactorial j * M.descFactorial (i - j) : ℕ) : ℤ) else 0

/-- The top part of `col r n` at `M` minus its load, as terms in `n`. -/
def baseWeight (K d M α i : ℕ) (c : ℤ) : ℤ :=
  if α = K then c * ((K ^ (M - d) * K ^ (d - i) * M.descFactorial i : ℕ) : ℤ)
  else if α < K then -((c.natAbs * (α ^ (M - i) * M ^ i) : ℕ) : ℤ) else 0

theorem evalFF_diffFF_topFF_col (r : List (ℤ × ℕ × ℕ × ℕ × ℕ)) (K d M j n : ℕ) :
    evalFF (diffFF j (topFF (col r n) K d)) M = coef (mapTerms (topWeight K d M j) r) n := by
  induction r with
  | nil => rfl
  | cons t r ih =>
    obtain ⟨c, α, i, β, j'⟩ := t
    by_cases h : α = K
    · subst h
      simp only [topFF, diffFF, evalFF, col, mapTerms, topWeight, List.map_cons,
        List.filter_cons, decide_true, ite_true, List.sum_cons, coef_cons] at ih ⊢
      rw [ih]
      push_cast
      ring
    · simp only [topFF, diffFF, evalFF, col, mapTerms, topWeight, List.map_cons,
        List.filter_cons, h, decide_false, Bool.false_eq_true, ite_false, coef_cons, zero_mul,
        zero_add] at ih ⊢
      exact ih

theorem base_col (r : List (ℤ × ℕ × ℕ × ℕ × ℕ)) (K d M n : ℕ) :
    (K : ℤ) ^ (M - d) * evalFF (topFF (col r n) K d) M - (restLoad (col r n) K M : ℤ) =
      coef (mapTerms (baseWeight K d M) r) n := by
  induction r with
  | nil => simp [topFF, evalFF, restLoad, mapTerms, coef_nil, col]
  | cons t r ih =>
    obtain ⟨c, α, i, β, j⟩ := t
    rw [show mapTerms (baseWeight K d M) ((c, α, i, β, j) :: r) =
      (baseWeight K d M α i c, β, j) :: mapTerms (baseWeight K d M) r from rfl, coef_cons, ← ih]
    rcases lt_trichotomy α K with h | rfl | h
    · simp only [topFF, evalFF, restLoad, col, baseWeight, List.map_cons, List.filter_cons,
        h, h.ne, decide_true, decide_false, ite_true, ite_false, List.sum_cons]
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      push_cast
      ring
    · simp only [topFF, evalFF, restLoad, col, baseWeight, List.map_cons, List.filter_cons,
        lt_irrefl, decide_true, decide_false, ite_true, ite_false, List.sum_cons]
      push_cast
      ring
    · simp only [topFF, evalFF, restLoad, col, baseWeight, List.map_cons, List.filter_cons,
        h.ne', not_lt.mpr h.le, decide_false, ite_false]
      simp

/-- The corner `m ≥ M`, `n ≥ N` with top row exponent `K` and powers of `p` at most `d`: the
conditions of `coef_nonneg_of_tail` in `m`, each a tail check in `n`. -/
def cornerOk (G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))) (K d M N : ℕ) : Bool :=
  decide (d ≤ M) && decide (1 ≤ M) &&
    (flatten₂ G).all (fun t ↦ decide (t.2.1 ≤ K) && decide (t.2.2.1 ≤ d) &&
      (decide (K ≤ t.2.1) || decide (t.2.1 * (M + 1) ^ t.2.2.1 ≤ K * M ^ t.2.2.1))) &&
    (List.range d).all (fun j ↦ tailOk (combineG (topWeight K d M (j + 1)) G) N) &&
    tailOk (combineG (baseWeight K d M) G) N

theorem cornerOk_spec {G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))} {K d M N : ℕ}
    (h : cornerOk G K d M N = true) {m n : ℕ} (hm : M ≤ m) (hn : N ≤ n) :
    0 ≤ coef₂ (flatten₂ G) m n := by
  simp only [cornerOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hdM, hM⟩, hr⟩, hΔ⟩, hb⟩ := h
  rw [← coef_col]
  have hcol : ∀ t ∈ col (flatten₂ G) n, ∃ s ∈ flatten₂ G, t.2 = (s.2.1, s.2.2.1) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact ⟨s, hs, rfl⟩
  refine coef_nonneg_of_tail (K := K) hdM hM (fun t ht ↦ ?_) (fun t ht ↦ ?_) (fun t ht hlt ↦ ?_)
    (fun j hj ↦ ?_) ?_ hm
  · obtain ⟨s, hs, e⟩ := hcol t ht
    rw [e]; exact (hr s hs).1.1
  · obtain ⟨s, hs, e⟩ := hcol t ht
    rw [e]; exact (hr s hs).1.2
  · obtain ⟨s, hs, e⟩ := hcol t ht
    rw [e] at hlt ⊢
    exact (hr s hs).2.resolve_left (by simp only at hlt; omega)
  · simp only [mem_Icc] at hj
    have := tailOk_spec (hΔ (j - 1) (by omega)) hn
    rwa [Nat.sub_add_cancel hj.1, coef_combineG, ← evalFF_diffFF_topFF_col] at this
  · have := tailOk_spec hb hn
    rw [coef_combineG, ← base_col] at this
    linarith

/-- **All coefficients nonnegative from four finite checks**: the rectangle `m ≤ M`, `n ≤ N`,
the two strips and the corner. -/
theorem coef₂_nonneg_of_checks {G : List (ℕ × ℕ × List (ℤ × ℕ × ℕ))} {K d M N : ℕ}
    (hR : rectOk G M N = true) (hP : stripPOk G M N = true) (hQ : stripQOk G M N = true)
    (hC : cornerOk G K d M N = true) (m n : ℕ) : 0 ≤ coef₂ (flatten₂ G) m n := by
  rcases le_total m M with hm | hm <;> rcases le_total n N with hn | hn
  · exact rectOk_spec hR m hm n hn
  · exact stripQOk_spec hQ hm hn
  · exact stripPOk_spec hP hm hn
  · exact cornerOk_spec hC hm hn

end PetzCurvature.ExpPolynomial
