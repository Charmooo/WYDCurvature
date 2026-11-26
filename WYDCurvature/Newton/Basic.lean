/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Notation
import Mathlib.Order.Basic

/-!
# Newton certificates: the computable part

An exponential polynomial `f(u) = ∑ c e^{Eu}` with exponents among `E₁, …, E_k` has the Newton expansion
`f = ∑ᵢ fᵢ(0) [E₁, …, Eᵢ₊₁]e^{·u}`, with `f₀ = f` and `fᵢ = fᵢ₋₁' - Eᵢ fᵢ₋₁`. The divided differences
of the exponential are positive for `u > 0`, whatever the order of the nodes, so `f ≥ 0` on `[0, ∞)`
as soon as every `fᵢ(0) ≥ 0`. The same holds in two variables. For the numerators of (64) and (65)
the nodes are `i p + j q` (with `d = q/p`), and the numbers `fᵢⱼ(0, 0)` are polynomials in a parameter
`t ≥ 0` with integer coefficients, all of them nonnegative.

A polynomial in `t` is packed into one integer, its value at `base`, with a bound for the sum of the
absolute values of its coefficients. Everything here is evaluated by the kernel; the soundness is in
`WYD.NewtonSound`.
-/

namespace WYD.Newton

/-- Half the packing base: a bound for the coefficients. -/
def half : ℕ := 2 ^ 400

/-- The packing base. -/
def base : ℕ := 2 * half

/-- A polynomial in `t` packed as its value at `base`, with a bound for the sum of the absolute
values of its coefficients. -/
abbrev PP := ℤ × ℕ

namespace PP

def add : PP → PP → PP
  | (a, m), (b, n) => (Int.add a b, Nat.add m n)
def mul : PP → PP → PP
  | (a, m), (b, n) => (Int.mul a b, Nat.mul m n)
def smul : ℤ → PP → PP
  | n, (a, m) => (Int.mul n a, Nat.mul n.natAbs m)
def zero : PP := (0, 0)

/-- The digits of `x` in base `base` are all small. -/
def dig : ℕ → ℕ → Bool
  | 0, x => x.beq 0
  | f + 1, x => bif (x.beq 0) then true else
      Nat.ble (x % base) half && dig f (x / base)

def nonneg (a : PP) : Bool :=
  match a with
  | (Int.ofNat x, b) => Nat.ble (b + 1) half && dig 200 x
  | (Int.negSucc _, _) => false

end PP

/-- The parameters: `p` and `q` as packed polynomials. -/
structure Par where
  p : PP
  q : PP

def Par.lin (P : Par) (i j : ℤ) : PP := (PP.smul i P.p).add (PP.smul j P.q)

/-- A term `c e^{(mi p + mj q) u + (ni p + nj q) v}`; the key only orders terms. -/
structure Term where
  key : ℕ
  mi : ℤ
  mj : ℤ
  ni : ℤ
  nj : ℤ
  c : PP

def off : ℕ := 512 * (1 + 1024 + 1024 ^ 2 + 1024 ^ 3)

def mkKey (mi mj ni nj : ℤ) : ℕ :=
  (mi + 512).toNat + 1024 * ((mj + 512).toNat + 1024 * ((ni + 512).toNat + 1024 * (nj + 512).toNat))

def Term.mk' (mi mj ni nj : ℤ) (c : PP) : Term := ⟨mkKey mi mj ni nj, mi, mj, ni, nj, c⟩

def Term.mul (a b : Term) : Term :=
  ⟨a.key + b.key - off, a.mi + b.mi, a.mj + b.mj, a.ni + b.ni, a.nj + b.nj, a.c.mul b.c⟩

def Term.same (a b : Term) : Bool :=
  decide (a.mi = b.mi) && decide (a.mj = b.mj) && decide (a.ni = b.ni) && decide (a.nj = b.nj)

abbrev EP := List Term

def merge : ℕ → EP → EP → EP
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a, [] => a
  | n + 1, x :: xs, y :: ys =>
    bif Nat.blt x.key y.key then x :: merge n xs (y :: ys)
    else bif Nat.blt y.key x.key then y :: merge n (x :: xs) ys
    else bif x.same y then { x with c := x.c.add y.c } :: merge n xs ys
    else x :: y :: merge n xs ys

def EP.add (a b : EP) : EP := merge (a.length + b.length) a b

def mergePairs : List EP → List EP
  | a :: b :: r => EP.add a b :: mergePairs r
  | l => l

def mergeAll : ℕ → List EP → EP
  | _, [] => []
  | _, [a] => a
  | 0, l => l.flatten
  | n + 1, l => mergeAll n (mergePairs l)

def EP.mul (a b : EP) : EP := mergeAll 20 (a.map fun x ↦ b.map fun y ↦ x.mul y)

def EP.smul (c : PP) (a : EP) : EP := a.map fun x ↦ { x with c := c.mul x.c }

/-- The formal derivative: multiplication by a linear form in the exponents. -/
def Term.lin (P : Par) (k : ℕ) (w : ℤ) (x : Term) : PP :=
  match k with
  | 0 => P.lin (-x.mi) (-x.mj)
  | 1 => P.lin (x.mi - x.ni) (x.mj - x.nj)
  | _ => P.lin (x.ni + w) x.nj

def EP.der (P : Par) (k : ℕ) (w : ℤ) (a : EP) : EP := a.map fun x ↦ { x with c := (x.lin P k w).mul x.c }

def isZero (a : PP) : Bool := (decide (a.1 = 0)) && Nat.ble (a.2 + 1) half

def EP.clean : EP → EP
  | [] => []
  | x :: l => bif isZero x.c then EP.clean l else x :: EP.clean l

/-! ### The Newton check -/

/-- `(i, j)` stands for the exponent `i p + j q`. -/
abbrev Node := ℤ × ℤ

def sumPP : List (Node × PP) → PP
  | [] => PP.zero
  | x :: l => x.2.add (sumPP l)

def stepAux (P : Par) (x : Node × PP) (r : List (Node × PP)) : ℤ → ℤ → List (Node × PP)
  | Int.ofNat 0, Int.ofNat 0 => r
  | i, j => (x.1, (P.lin i j).mul x.2) :: r

def step (P : Par) (n : Node) : List (Node × PP) → List (Node × PP)
  | [] => []
  | x :: l => stepAux P x (step P n l) (x.1.1 - n.1) (x.1.2 - n.2)

def check1 (P : Par) : List Node → List (Node × PP) → Bool
  | [], l => l.isEmpty
  | n :: ns, l => (sumPP l).nonneg && check1 P ns (step P n l)

def check2 (P : Par) : List Node → List Node → List (Node × List (Node × PP)) → Bool
  | [], _, rows => rows.all fun r ↦ r.2.isEmpty
  | n :: ns, vs, rows =>
    check1 P vs (rows.map fun r ↦ (r.1, sumPP r.2)) &&
      check2 P ns vs (rows.map fun r ↦ (r.1, step P n r.2))

/-- The part of `check2` for the nodes `ns`, without the final test. -/
def part (P : Par) : List Node → List Node → List (Node × List (Node × PP)) → Bool
  | [], _, _ => true
  | n :: ns, vs, rows =>
    check1 P vs (rows.map fun r ↦ (r.1, sumPP r.2)) &&
      part P ns vs (rows.map fun r ↦ (r.1, step P n r.2))

/-- The rows after the nodes `ns`. -/
def after (P : Par) : List Node → List (Node × List (Node × PP)) → List (Node × List (Node × PP))
  | [], rows => rows
  | n :: ns, rows => after P ns (rows.map fun r ↦ (r.1, step P n r.2))

/-- `check2` in two pieces. -/
theorem check2_append {P : Par} (us us' vs : List Node) : ∀ {rows : List (Node × List (Node × PP))},
    part P us vs rows = true → check2 P us' vs (after P us rows) = true →
      check2 P (us ++ us') vs rows = true := by
  induction us with
  | nil => intro rows _ h; exact h
  | cons n ns ih =>
    intro rows h h'
    rw [part, Bool.and_eq_true] at h
    rw [List.cons_append, check2, Bool.and_eq_true]
    exact ⟨h.1, ih h.2 h'⟩

theorem after_append {P : Par} (us us' : List Node) : ∀ rows : List (Node × List (Node × PP)),
    after P (us ++ us') rows = after P us' (after P us rows) := by
  induction us with
  | nil => intro rows; rfl
  | cons n ns ih => intro rows; exact ih _

/-- Group the terms by their exponent in `v`. -/
def group : EP → List (Node × List (Node × PP))
  | [] => []
  | x :: l =>
    match group l with
    | [] => [((x.ni, x.nj), [((x.mi, x.mj), x.c)])]
    | r :: rs =>
      bif decide (r.1.1 = x.ni) && decide (r.1.2 = x.nj) then
        (r.1, ((x.mi, x.mj), x.c) :: r.2) :: rs
      else ((x.ni, x.nj), [((x.mi, x.mj), x.c)]) :: r :: rs

/-! ### The numerators -/

section Num

variable (P : Par)

/-- Exponent of `σ_i - σ_j` (times `x p + y q`) in gap coordinates, `i, j` in `{0, 1, 2}`. -/
def pos : ℕ → ℤ × ℤ       -- σ_k = -(pos.1 u + pos.2 v) + σ_2
  | 0 => (1, 1)
  | 1 => (0, 1)
  | _ => (0, 0)

/-- `e^{(x p + y q)(σ_i - σ_j)}`. -/
def eT (i j : ℕ) (x y : ℤ) (c : PP) : Term :=
  let a := (pos j).1 - (pos i).1
  let b := (pos j).2 - (pos i).2
  Term.mk' (x * a) (y * a) (x * b) (y * b) c

def sortT : List Term → EP := fun l ↦ mergeAll 5 (l.map fun x ↦ [x])

def neg1 : PP → PP := PP.smul (-1)

/-- `2F(σ_i - σ_j)`, `F = p sinh(qs) - q sinh(ps)`. -/
def epF (i j : ℕ) : EP := sortT [eT i j 0 1 P.p, eT i j 0 (-1) (neg1 P.p), eT i j 1 0 (neg1 P.q), eT i j (-1) 0 P.q]

/-- `2G(σ_i - σ_j)`, `G = q (cosh(qs) - cosh(ps))`. -/
def epG (i j : ℕ) : EP := sortT [eT i j 0 1 P.q, eT i j 0 (-1) P.q, eT i j 1 0 (neg1 P.q), eT i j (-1) 0 (neg1 P.q)]

/-- `e^{-k p (σ_i - σ_2)}`, i.e. `e^{-kσ_i}` up to the weight. -/
def epW (k : ℤ) (i : ℕ) : EP := [eT i 2 (-k) 0 (1, 1)]

def epK (i j : ℕ) : EP := EP.add (epF P i j) (EP.smul (-1, 1) (epG P i j))

def epN : EP := EP.add (EP.mul (epW 1 2) (epF P 0 1))
  (EP.add (EP.mul (epW 1 0) (epF P 1 2)) (EP.mul (epW 1 1) (epF P 2 0)))

def epV (i j k : ℕ) : EP := EP.mul (EP.mul (epW 2 i) (epG P j k)) (EP.mul (epK P j i) (epK P k i))

/-- `A`, with `H = A / (24 p² (2G)(2G)(2G))`. -/
def epA : EP := EP.clean <| EP.add
  (EP.smul (PP.mul (PP.smul 3 P.q) (PP.add (PP.mul P.q P.q) (neg1 (PP.mul P.p P.p)))) (EP.mul (epN P) (epN P)))
  (EP.smul (PP.smul (-2) (PP.mul P.p P.p))
    (EP.add (epV P 0 1 2) (EP.add (epV P 1 2 0) (epV P 2 0 1))))

/-- The numerator for (65), differentiating `σ_k`. -/
def num65 (s : ℤ) (k i j : ℕ) : EP :=
  let A := epA P
  let Q := EP.mul (epG P k i) (epG P k j)
  let A1 := EP.der P k (-2) A
  let Q1 := EP.der P k 0 Q
  let A2 := EP.der P k (-2) A1
  let Q2 := EP.der P k 0 Q1
  let tp := PP.smul 2 P.p
  let B := EP.add (EP.mul (EP.add A2 (EP.smul (neg1 tp) A1)) Q)
    (EP.add (EP.mul A1 (EP.smul (-2, 2) Q1)) (EP.mul A (EP.add (EP.smul tp Q1) (EP.smul (-1, 1) Q2))))
  EP.clean (EP.smul (s, 1) (EP.add (EP.mul B Q) (EP.mul A (EP.smul (2, 2) (EP.mul Q1 Q1)))))

/-- The numerator for (64), `i < j`. -/
def num64 (i j : ℕ) : EP :=
  let A := epA P
  let D := EP.mul (EP.mul (epG P 0 1) (epG P 1 2)) (epG P 0 2)
  let L := fun k ↦ EP.mul (epW 2 k) (EP.add (EP.mul (EP.der P k (-2) A) D)
    (EP.smul (-1, 1) (EP.mul A (EP.der P k 0 D))))
  EP.clean (EP.add (L i) (EP.smul (-1, 1) (L j)))

end Num

def par1 : Par := ⟨(1 + base, 2), (base, 1)⟩
def par2 : Par := ⟨(1 + base, 2), (3 + base, 4)⟩

end WYD.Newton
