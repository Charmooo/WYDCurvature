/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Polynomials as lists of monomials, normalized by the kernel

A polynomial with integer coefficients in variables `x₀, x₁, …` is a list of monomials, each a
coefficient `c`, a sort key and an exponent vector `[e₀, e₁, …]`, standing for
`c x₀^{e₀} x₁^{e₁} ⋯` (`ListPoly.eval`, in any commutative ring; missing exponents are `0`).
Sums, differences, products and powers are computable (`ListPoly.add`, `ListPoly.sub`,
`ListPoly.mul`, `ListPoly.pow`), and so is a normal form (`ListPoly.norm`). Every operation
preserves `eval`, so an identity `p = q` between polynomials built from data follows from the
kernel computation `sub p q = []` (`ListPoly.eval_eq_of_sub_eq_nil`), by `decide +kernel`, without
`ring`.

Monomials are kept sorted by their key (`ListPoly.pack`, the exponents as digits in base `1024`),
so that the kernel compares two monomials with one `Nat.blt` on literals; the exponent vectors
themselves are compared (`ListPoly.keyEq`) only when the keys agree, before two monomials are
added. The key never enters `eval`, so soundness does not depend on it; it only decides whether
the computation finds every cancellation. Sums merge sorted lists (`ListPoly.merge`); a product
is the balanced merge (`ListPoly.mergeAll`) of its rows `s · q`, each sorted when `q` is. All
recursion is structural or on a fuel argument, so the kernel can evaluate it; any fuel is sound.

## Main definitions

* `ListPoly.eval`: the value of a list of monomials at a list of points.
* `ListPoly.add`, `ListPoly.sub`, `ListPoly.smul`, `ListPoly.mul`, `ListPoly.pow`,
  `ListPoly.prod`, `ListPoly.var`, `ListPoly.const`: arithmetic.
* `ListPoly.merge`, `ListPoly.mergeAll`, `ListPoly.norm`: sorting and the normal form.

## Main statements

* `ListPoly.eval_add`, `ListPoly.eval_sub`, `ListPoly.eval_mul`, `ListPoly.eval_pow`,
  `ListPoly.eval_prod`: the arithmetic is sound.
* `ListPoly.eval_norm`: the normal form has the same value.
* `ListPoly.eval_eq_of_sub_eq_nil`, `ListPoly.eval_eq_of_norm_sub`: `sub p q = []`, or
  `norm (sub p q) = []`, gives `eval p = eval q`.

-/

namespace PetzCurvature.ListPoly

/-- A monomial `c x₀^{e₀} x₁^{e₁} ⋯`: the coefficient `c`, a sort key and the exponent vector.
The key only orders monomials; `eval` ignores it. -/
abbrev Mono := ℤ × ℕ × List ℕ

/-- The sort key of an exponent vector: its entries as digits in base `1024`. Trailing zeros do not
change it, and it is additive (`ListPoly.pack_addExp`). -/
def pack : List ℕ → ℕ
  | [] => 0
  | e :: es => e + 1024 * pack es

/-- The monomial `c x₀^{e₀} x₁^{e₁} ⋯` with its key. -/
def mono (c : ℤ) (e : List ℕ) : Mono := (c, pack e, e)

variable {R : Type*} [CommRing R]

/-- `x₀^{e₀} x₁^{e₁} ⋯`, stopping at the shorter of the two lists. -/
def evalExp : List ℕ → List R → R
  | e :: es, x :: xs => x ^ e * evalExp es xs
  | _, _ => 1

/-- The value of a list of monomials. -/
def eval (p : List Mono) (xs : List R) : R :=
  (p.map fun m ↦ (m.1 : R) * evalExp m.2.2 xs).sum

@[simp] theorem eval_nil (xs : List R) : eval [] xs = 0 := rfl

@[simp] theorem eval_cons (m : Mono) (p : List Mono) (xs : List R) :
    eval (m :: p) xs = m.1 * evalExp m.2.2 xs + eval p xs := List.sum_cons

@[simp] theorem eval_append (p q : List Mono) (xs : List R) :
    eval (p ++ q) xs = eval p xs + eval q xs := by
  simp [eval]

theorem eval_flatten (ls : List (List Mono)) (xs : List R) :
    eval ls.flatten xs = (ls.map fun p ↦ eval p xs).sum := by
  induction ls with
  | nil => rfl
  | cons p ls ih => rw [List.flatten_cons, eval_append, ih, List.map_cons, List.sum_cons]

/-! ### Exponent vectors -/

/-- All exponents zero. -/
def allZero : List ℕ → Bool
  | [] => true
  | a :: as => a == 0 && allZero as

/-- Equality of exponent vectors padded with zeros (structural in the first argument, so that
the kernel can evaluate it). -/
def keyEq : List ℕ → List ℕ → Bool
  | [], bs => allZero bs
  | a :: as, [] => a == 0 && allZero as
  | a :: as, b :: bs => a == b && keyEq as bs

theorem evalExp_nil_left (xs : List R) : evalExp [] xs = 1 := by
  cases xs <;> rfl

theorem evalExp_of_allZero {a : List ℕ} (h : allZero a = true) (xs : List R) :
    evalExp a xs = 1 := by
  induction a generalizing xs with
  | nil => exact evalExp_nil_left xs
  | cons a as ih =>
    simp only [allZero, Bool.and_eq_true, beq_iff_eq] at h
    cases xs with
    | nil => rfl
    | cons x xs => rw [evalExp, h.1, pow_zero, one_mul, ih h.2]

theorem evalExp_eq_of_keyEq {a b : List ℕ} (h : keyEq a b = true) (xs : List R) :
    evalExp a xs = evalExp b xs := by
  induction a generalizing b xs with
  | nil => rw [evalExp_nil_left, evalExp_of_allZero h]
  | cons a as ih =>
    cases b with
    | nil =>
      rw [evalExp_nil_left]
      exact evalExp_of_allZero (by simpa [keyEq, allZero] using h) xs
    | cons b bs =>
      simp only [keyEq, Bool.and_eq_true, beq_iff_eq] at h
      cases xs with
      | nil => rfl
      | cons x xs => rw [evalExp, evalExp, h.1, ih h.2]

/-- Addition of exponent vectors, padding the shorter one with zeros. -/
def addExp : List ℕ → List ℕ → List ℕ
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addExp as bs

theorem evalExp_addExp (a b : List ℕ) (xs : List R) :
    evalExp (addExp a b) xs = evalExp a xs * evalExp b xs := by
  induction a generalizing b xs with
  | nil => rw [addExp, evalExp_nil_left, one_mul]
  | cons a as ih =>
    cases b with
    | nil =>
      rw [addExp, evalExp_nil_left, mul_one]
    | cons b bs =>
      cases xs with
      | nil => simp [addExp, evalExp]
      | cons x xs =>
        rw [addExp, evalExp, evalExp, evalExp, ih, pow_add]
        ring

theorem pack_addExp (a b : List ℕ) : pack (addExp a b) = pack a + pack b := by
  induction a generalizing b with
  | nil => simp [addExp, pack]
  | cons a as ih =>
    cases b with
    | nil => simp [addExp, pack]
    | cons b bs =>
      rw [addExp, pack, pack, pack, ih]
      ring

/-! ### Sorting -/

/-- Merge two lists sorted by key, adding the coefficients of equal monomials and dropping zero
sums. Sound for any fuel and any lists; with `a.length + b.length` it merges completely. -/
def merge : ℕ → List Mono → List Mono → List Mono
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, s :: a, [] => s :: a
  | f + 1, s :: a, t :: b =>
    if Nat.beq s.2.1 t.2.1 && keyEq s.2.2 t.2.2 then
      (if s.1 + t.1 == 0 then merge f a b else (s.1 + t.1, s.2) :: merge f a b)
    else if Nat.blt s.2.1 t.2.1 then s :: merge f a (t :: b)
    else t :: merge f (s :: a) b

/-- Merge neighbouring lists in pairs. -/
def mergePairs : List (List Mono) → List (List Mono)
  | a :: b :: rest => merge (a.length + b.length) a b :: mergePairs rest
  | l => l

/-- Merge a list of sorted lists into one, in a balanced tree. -/
def mergeAll : ℕ → List (List Mono) → List Mono
  | 0, ls => ls.flatten
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | f + 1, a :: b :: ls => mergeAll f (mergePairs (a :: b :: ls))

theorem eval_merge (f : ℕ) (a b : List Mono) (xs : List R) :
    eval (merge f a b) xs = eval a xs + eval b xs := by
  induction f generalizing a b with
  | zero => simp [merge]
  | succ f ih =>
    rcases a with _ | ⟨s, a⟩ <;> rcases b with _ | ⟨t, b⟩
    · simp [merge]
    · simp [merge]
    · simp [merge]
    · simp only [merge]
      split_ifs with h1 h2 h3
      · have e := evalExp_eq_of_keyEq ((Bool.and_eq_true _ _).mp h1).2 xs
        have h0 : ((s.1 + t.1 : ℤ) : R) = 0 := by
          rw [beq_iff_eq] at h2; rw [h2, Int.cast_zero]
        simp only [ih, eval_cons, ← e]
        push_cast at h0
        linear_combination (-evalExp s.2.2 xs) * h0
      · have e := evalExp_eq_of_keyEq ((Bool.and_eq_true _ _).mp h1).2 xs
        simp only [eval_cons, ih, ← e]
        push_cast
        ring
      · simp only [eval_cons, ih]
        ring
      · simp only [eval_cons, ih]
        ring

theorem eval_mergePairs (xs : List R) : ∀ ls : List (List Mono),
    ((mergePairs ls).map fun p ↦ eval p xs).sum = (ls.map fun p ↦ eval p xs).sum
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    rw [mergePairs, List.map_cons, List.sum_cons, eval_merge, eval_mergePairs xs rest]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem eval_mergeAll (f : ℕ) (ls : List (List Mono)) (xs : List R) :
    eval (mergeAll f ls) xs = (ls.map fun p ↦ eval p xs).sum := by
  induction f generalizing ls with
  | zero => rw [mergeAll, eval_flatten]
  | succ f ih =>
    match ls with
    | [] => rfl
    | [a] => simp [mergeAll]
    | a :: b :: ls => rw [mergeAll, ih, eval_mergePairs]

/-- The normal form: sorted by key, equal monomials combined, zero coefficients dropped. -/
def norm (p : List Mono) : List Mono := (mergeAll 64 (p.map ([·]))).filter fun m ↦ m.1 != 0

theorem eval_filter_ne_zero (p : List Mono) (xs : List R) :
    eval (p.filter fun m ↦ m.1 != 0) xs = eval p xs := by
  induction p with
  | nil => rfl
  | cons m l ih =>
    by_cases h : m.1 = 0
    · simp [h, ih]
    · simp [h, ih]

@[simp] theorem eval_norm (p : List Mono) (xs : List R) : eval (norm p) xs = eval p xs := by
  rw [norm, eval_filter_ne_zero, eval_mergeAll]
  induction p with
  | nil => rfl
  | cons m p ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, ih]
    simp

/-! ### Arithmetic -/

/-- `p + q` (sorted when `p` and `q` are). -/
def add (p q : List Mono) : List Mono := merge (p.length + q.length) p q

/-- `c p`. -/
def smul (c : ℤ) (p : List Mono) : List Mono := p.map fun m ↦ (c * m.1, m.2)

/-- `p - q`. -/
def sub (p q : List Mono) : List Mono := add p (smul (-1) q)

/-- `p q`: the balanced merge of the rows `s · q`, `s ∈ p` (sorted when `q` is). -/
def mul (p q : List Mono) : List Mono :=
  mergeAll 64 (p.map fun s ↦ q.map fun t ↦ (s.1 * t.1, s.2.1 + t.2.1, addExp s.2.2 t.2.2))

/-- The constant `c`. -/
def const (c : ℤ) : List Mono := [mono c []]

/-- The variable `xᵢ`. -/
def var (i : ℕ) : List Mono := [mono 1 (List.replicate i 0 ++ [1])]

@[simp] theorem eval_add (p q : List Mono) (xs : List R) :
    eval (add p q) xs = eval p xs + eval q xs :=
  eval_merge _ p q xs

@[simp] theorem eval_smul (c : ℤ) (p : List Mono) (xs : List R) :
    eval (smul c p) xs = c * eval p xs := by
  induction p with
  | nil => simp [smul]
  | cons m p ih =>
    simp only [smul, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

@[simp] theorem eval_sub (p q : List Mono) (xs : List R) :
    eval (sub p q) xs = eval p xs - eval q xs := by
  simp only [sub, eval_add, eval_smul]
  push_cast
  ring

theorem eval_map_mulMono (s : Mono) (q : List Mono) (xs : List R) :
    eval (q.map fun t ↦ (s.1 * t.1, s.2.1 + t.2.1, addExp s.2.2 t.2.2)) xs =
      s.1 * evalExp s.2.2 xs * eval q xs := by
  induction q with
  | nil => simp
  | cons t q ih =>
    simp only [List.map_cons, eval_cons] at ih ⊢
    rw [ih, evalExp_addExp]
    push_cast
    ring

@[simp] theorem eval_mul (p q : List Mono) (xs : List R) :
    eval (mul p q) xs = eval p xs * eval q xs := by
  rw [mul, eval_mergeAll]
  induction p with
  | nil => simp
  | cons s p ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, ih, eval_map_mulMono, eval_cons]
    ring

@[simp] theorem eval_const (c : ℤ) (xs : List R) : eval (const c) xs = c := by
  simp [const, mono, eval, evalExp_nil_left]

theorem evalExp_replicate_append (i : ℕ) (xs : List R) (h : i < xs.length) :
    evalExp (List.replicate i 0 ++ [1]) xs = xs[i] := by
  induction i generalizing xs with
  | zero =>
    obtain ⟨x, xs, rfl⟩ : ∃ x xs', xs = x :: xs' := List.exists_cons_of_length_pos h
    simp [evalExp]
  | succ i ih =>
    obtain ⟨x, xs, rfl⟩ : ∃ x xs', xs = x :: xs' := List.exists_cons_of_length_pos (by omega)
    rw [List.replicate_succ, List.cons_append, evalExp, pow_zero, one_mul,
      ih xs (by simpa using h)]
    rfl

theorem eval_var (i : ℕ) (xs : List R) (h : i < xs.length) : eval (var i) xs = xs[i] := by
  simp [var, mono, eval, evalExp_replicate_append i xs h]

@[simp] theorem eval_var_zero (x : R) (xs : List R) : eval (var 0) (x :: xs) = x :=
  eval_var 0 (x :: xs) (by simp)

@[simp] theorem eval_var_succ (i : ℕ) (x : R) (xs : List R) :
    eval (var (i + 1)) (x :: xs) = eval (var i) xs := by
  simp [var, mono, eval, List.replicate_succ, evalExp]

/-- `pᵏ` (sorted when `p` is). -/
def pow (p : List Mono) : ℕ → List Mono
  | 0 => const 1
  | k + 1 => mul p (pow p k)

@[simp] theorem eval_pow (p : List Mono) (k : ℕ) (xs : List R) :
    eval (pow p k) xs = eval p xs ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => rw [pow, eval_mul, ih, pow_succ, mul_comm]

/-- The product of a list of polynomials (sorted). -/
def prod (ps : List (List Mono)) : List Mono := ps.foldr mul (const 1)

@[simp] theorem eval_prod (ps : List (List Mono)) (xs : List R) :
    eval (prod ps) xs = (ps.map fun p ↦ eval p xs).prod := by
  induction ps with
  | nil => simp [prod]
  | cons p ps ih =>
    simp only [prod, List.foldr_cons, eval_mul, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

/-- **Identities by computation**: if `p - q` reduces to `[]`, then `p` and `q` agree at every
point of every commutative ring. -/
theorem eval_eq_of_sub_eq_nil {p q : List Mono} (h : sub p q = []) (xs : List R) :
    eval p xs = eval q xs := by
  have := eval_sub p q xs
  rw [h, eval_nil] at this
  exact (sub_eq_zero.mp this.symm)

/-- `ListPoly.eval_eq_of_sub_eq_nil` for lists that are not sorted. -/
theorem eval_eq_of_norm_sub {p q : List Mono} (h : norm (sub p q) = []) (xs : List R) :
    eval p xs = eval q xs := by
  have := eval_norm (sub p q) xs
  rw [h, eval_nil, eval_sub] at this
  exact (sub_eq_zero.mp this.symm)

end PetzCurvature.ListPoly
