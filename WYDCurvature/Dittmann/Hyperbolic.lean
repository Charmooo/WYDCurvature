/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Dittmann.Forms

/-!
# The hyperbolic form of `hs_β`

For pairwise distinct `σᵢ` and `λᵢ = e^{2σᵢ}`, `hs_β(λ₁, λ₂, λ₃) = d² H(σ₁, σ₂, σ₃)` with `H = hypH d`
elementary (`wydHs_eq_hypH`). It is the function that the computer check of (64) and (65) uses.
-/

open Real
open WYD.Ineq63 (qubitK)

namespace WYD

variable {β : ℝ}

/-- `φ(s) = (sinh s - sinh(ds)/d)/(1 - d²)`. -/
noncomputable def hypPhi (d s : ℝ) : ℝ := (sinh s - sinh (d * s) / d) / (1 - d ^ 2)

/-- `φ'(s) = (cosh s - cosh(ds))/(1 - d²)`. -/
noncomputable def hypPhi' (d s : ℝ) : ℝ := (cosh s - cosh (d * s)) / (1 - d ^ 2)

/-- The hyperbolic form `H(σ₁, σ₂, σ₃)`, with `K = φ/φ'`. -/
noncomputable def hypH (d a b c : ℝ) : ℝ :=
  (exp (-c) * hypPhi d (a - b) + exp (-a) * hypPhi d (b - c) + exp (-b) * hypPhi d (c - a)) ^ 2 /
      (16 * (hypPhi' d (a - b) * hypPhi' d (b - c) * hypPhi' d (c - a))) -
    (exp (-2 * a) * ((qubitK d (b - a) - 1) * (qubitK d (c - a) - 1)) +
      exp (-2 * b) * ((qubitK d (c - b) - 1) * (qubitK d (a - b) - 1)) +
      exp (-2 * c) * ((qubitK d (a - c) - 1) * (qubitK d (b - c) - 1))) / 12

/-- The metric kernel through `P = e^{βx}`, `Q = e^{(1-β)x}`. -/
theorem metK_mul (x y : ℝ) : metK β x y * (β * (1 - β) * (x - y) ^ 2) =
    (exp (β * x) - exp (β * y)) * (exp ((1 - β) * x) - exp ((1 - β) * y)) := by
  rw [← e1_mul_sub, ← e1_mul_sub, metK]; ring

/-- The cubic kernel through `P`, `Q`. -/
theorem cubK_mul (x k y : ℝ) :
    cubK β x k y * (β * (1 - β) * ((x - k) * (x - y) * (k - y))) =
      (exp (β * x) - exp (β * y)) * (exp ((1 - β) * k) - exp ((1 - β) * y)) -
        (exp (β * k) - exp (β * y)) * (exp ((1 - β) * x) - exp ((1 - β) * y)) := by
  rw [← e1_mul_sub, ← e1_mul_sub, ← e1_mul_sub, ← e1_mul_sub]
  linear_combination (β * (1 - β) * (x - y) * (k - y)) * cubK_mul_sub (β := β) x k y

/-- `φ'` through `P`, `Q`. -/
theorem hypPhi'_mul (hd : (2 * β - 1) ^ 2 ≠ 1) (a b : ℝ) :
    exp (a + b) * hypPhi' (2 * β - 1) (a - b) * (2 * (1 - (2 * β - 1) ^ 2)) =
      (exp (β * (2 * a)) - exp (β * (2 * b))) *
        (exp ((1 - β) * (2 * a)) - exp ((1 - β) * (2 * b))) := by
  have hne : 1 - (2 * β - 1) ^ 2 ≠ 0 := sub_ne_zero.2 hd.symm
  rw [hypPhi', cosh_eq, cosh_eq]
  have e1 : exp (a + b) * exp (a - b) = exp (β * (2 * a)) * exp ((1 - β) * (2 * a)) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  have e2 : exp (a + b) * exp (-(a - b)) = exp (β * (2 * b)) * exp ((1 - β) * (2 * b)) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  have e3 : exp (a + b) * exp ((2 * β - 1) * (a - b)) =
      exp (β * (2 * a)) * exp ((1 - β) * (2 * b)) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  have e4 : exp (a + b) * exp (-((2 * β - 1) * (a - b))) =
      exp (β * (2 * b)) * exp ((1 - β) * (2 * a)) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  generalize exp (a + b) = E at *
  generalize exp (a - b) = U at *
  generalize exp (-(a - b)) = U' at *
  generalize exp ((2 * β - 1) * (a - b)) = V at *
  generalize exp (-((2 * β - 1) * (a - b))) = V' at *
  generalize exp (β * (2 * a)) = A at *
  generalize exp ((1 - β) * (2 * a)) = A' at *
  generalize exp (β * (2 * b)) = B at *
  generalize exp ((1 - β) * (2 * b)) = B' at *
  field_simp
  linear_combination e1 + e2 - e3 - e4

/-- `φ` through `P`, `Q`. -/
theorem hypPhi_mul (hd : (2 * β - 1) ^ 2 ≠ 1) (h2 : 2 * β - 1 ≠ 0) (a b : ℝ) :
    exp (a + b) * hypPhi (2 * β - 1) (a - b) * (2 * ((2 * β - 1) * (1 - (2 * β - 1) ^ 2))) =
      (2 * β - 1) * (exp (2 * a) - exp (2 * b)) - (exp (β * (2 * a)) * exp ((1 - β) * (2 * b)) -
        exp (β * (2 * b)) * exp ((1 - β) * (2 * a))) := by
  have hne : 1 - (2 * β - 1) ^ 2 ≠ 0 := sub_ne_zero.2 hd.symm
  rw [hypPhi, sinh_eq, sinh_eq]
  have e1 : exp (a + b) * exp (a - b) = exp (2 * a) := by rw [← exp_add]; congr 1; ring
  have e2 : exp (a + b) * exp (-(a - b)) = exp (2 * b) := by rw [← exp_add]; congr 1; ring
  have e3 : exp (a + b) * exp ((2 * β - 1) * (a - b)) =
      exp (β * (2 * a)) * exp ((1 - β) * (2 * b)) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  have e4 : exp (a + b) * exp (-((2 * β - 1) * (a - b))) =
      exp (β * (2 * b)) * exp ((1 - β) * (2 * a)) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  generalize exp (a + b) = E at *
  generalize exp (a - b) = U at *
  generalize exp (-(a - b)) = U' at *
  generalize exp ((2 * β - 1) * (a - b)) = V at *
  generalize exp (-((2 * β - 1) * (a - b))) = V' at *
  generalize exp (β * (2 * a)) = A at *
  generalize exp ((1 - β) * (2 * a)) = A' at *
  generalize exp (β * (2 * b)) = B at *
  generalize exp ((1 - β) * (2 * b)) = B' at *
  generalize exp (2 * a) = F at *
  generalize exp (2 * b) = F' at *
  field_simp
  linear_combination (2 * β - 1) * e1 - (2 * β - 1) * e2 - e3 + e4

/-- The symmetric part of `curvK`. -/
theorem cubK_sq_eq (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) {a b c : ℝ} (hab : a ≠ b)
    (hbc : b ≠ c) (hca : c ≠ a) :
    cubK β (2 * a) (2 * b) (2 * c) ^ 2 / (2 * (metK β (2 * a) (2 * b) * metK β (2 * b) (2 * c) *
      metK β (2 * c) (2 * a))) = (2 * β - 1) ^ 2 *
    ((exp (-c) * hypPhi (2 * β - 1) (a - b) + exp (-a) * hypPhi (2 * β - 1) (b - c) +
        exp (-b) * hypPhi (2 * β - 1) (c - a)) ^ 2 /
      (16 * (hypPhi' (2 * β - 1) (a - b) * hypPhi' (2 * β - 1) (b - c) *
        hypPhi' (2 * β - 1) (c - a)))) := by
  have h1' : 1 - β ≠ 0 := sub_ne_zero.2 h1.symm
  have hd2 : (2 * β - 1) ^ 2 ≠ 1 := fun h ↦ by
    have : β * (1 - β) = 0 := by linarith
    exact mul_ne_zero h0 h1' this
  have hb : β * (1 - β) ≠ 0 := mul_ne_zero h0 h1'
  set p := 2 * β - 1 with hp
  have hb4 : 1 - p ^ 2 = 4 * (β * (1 - β)) := by rw [hp]; ring
  have dab := sub_ne_zero.2 hab; have dbc := sub_ne_zero.2 hbc; have dca := sub_ne_zero.2 hca
  -- `M` through `φ'`
  have M : ∀ x y : ℝ, x ≠ y → metK β (2 * x) (2 * y) =
      2 * exp (x + y) * hypPhi' p (x - y) / (x - y) ^ 2 := by
    intro x y hxy
    have hxy' := sub_ne_zero.2 hxy
    have m1 := metK_mul (β := β) (2 * x) (2 * y)
    have m2 := hypPhi'_mul hd2 x y
    rw [eq_div_iff (pow_ne_zero 2 hxy')]
    apply mul_right_cancel₀ (mul_ne_zero four_ne_zero hb)
    rw [← m2, ← hp, hb4] at m1
    linear_combination m1
  -- `C` through `φ`
  set T := exp (a + b) * hypPhi p (a - b) + exp (b + c) * hypPhi p (b - c) +
    exp (c + a) * hypPhi p (c - a) with hT
  have hC : cubK β (2 * a) (2 * b) (2 * c) ^ 2 =
      p ^ 2 * T ^ 2 / ((a - b) * (b - c) * (c - a)) ^ 2 := by
    have c1 := cubK_mul (β := β) (2 * a) (2 * b) (2 * c)
    have t1 := hypPhi_mul hd2 h2 a b
    have t2 := hypPhi_mul hd2 h2 b c
    have t3 := hypPhi_mul hd2 h2 c a
    rw [← hp, hb4] at t1 t2 t3
    have hC' : cubK β (2 * a) (2 * b) (2 * c) * ((a - b) * (b - c) * (c - a)) = p * T := by
      apply mul_right_cancel₀ (mul_ne_zero (show (8 : ℝ) ≠ 0 by norm_num) hb)
      rw [hT]
      linear_combination -c1 - t1 - t2 - t3
    rw [eq_div_iff (by positivity), ← mul_pow, ← mul_pow, hC']
  have hsum : exp (-c) * hypPhi p (a - b) + exp (-a) * hypPhi p (b - c) +
      exp (-b) * hypPhi p (c - a) = exp (-(a + b + c)) * T := by
    rw [hT, mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← exp_add, ← exp_add,
      ← exp_add]
    rw [show -(a + b + c) + (a + b) = -c by ring, show -(a + b + c) + (b + c) = -a by ring,
      show -(a + b + c) + (c + a) = -b by ring]
  have hE : exp (a + b) * exp (b + c) * exp (c + a) = exp (a + b + c) ^ 2 := by
    rw [← exp_add, ← exp_add, ← exp_nat_mul]; congr 1; push_cast; ring
  rw [hC, M a b hab, M b c hbc, M c a hca, hsum, exp_neg]
  have he := exp_pos (a + b + c)
  rcases eq_or_ne (hypPhi' p (a - b) * hypPhi' p (b - c) * hypPhi' p (c - a)) 0 with h | h
  · rw [h]
    have : 2 * exp (a + b) * hypPhi' p (a - b) / (a - b) ^ 2 *
        (2 * exp (b + c) * hypPhi' p (b - c) / (b - c) ^ 2) *
        (2 * exp (c + a) * hypPhi' p (c - a) / (c - a) ^ 2) =
      (hypPhi' p (a - b) * hypPhi' p (b - c) * hypPhi' p (c - a)) *
        (8 * exp (a + b) * exp (b + c) * exp (c + a) /
          ((a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2)) := by
      field_simp; ring
    rw [this, h]
    simp
  have hfab : hypPhi' p (a - b) ≠ 0 := fun h' ↦ h (by rw [h']; ring)
  have hfbc : hypPhi' p (b - c) ≠ 0 := fun h' ↦ h (by rw [h']; ring)
  have hfca : hypPhi' p (c - a) ≠ 0 := fun h' ↦ h (by rw [h']; ring)
  have ea := exp_pos (a + b); have eb := exp_pos (b + c); have ec := exp_pos (c + a)
  generalize exp (a + b) = x at *
  generalize exp (b + c) = y at *
  generalize exp (c + a) = z at *
  generalize exp (a + b + c) = e at *
  have h3 : (e⁻¹ * T) ^ 2 = T ^ 2 / (x * y * z) := by rw [hE, mul_pow, inv_pow]; ring
  rw [h3]
  field_simp
  ring

/-- **The hyperbolic form**: `hs_β(e^{2a}, e^{2b}, e^{2c}) = d² H(a, b, c)` for distinct `a, b, c`. -/
theorem wydHs_eq_hypH (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) {a b c : ℝ} (hab : a ≠ b)
    (hbc : b ≠ c) (hca : c ≠ a) :
    wydHs β (exp (2 * a)) (exp (2 * b)) (exp (2 * c)) = (2 * β - 1) ^ 2 * hypH (2 * β - 1) a b c := by
  have C : ∀ x y z, curvK β x y z = cubK β x y z ^ 2 / (2 * (metK β x y * metK β y z * metK β z x)) -
      exp (-x) * ((cubK β x x y / metK β x y) * (cubK β x x z / metK β x z)) := by
    intro x y z
    have := exp_pos x
    have m1 := (metK_pos (β := β) x y).ne'
    have m2 := (metK_pos (β := β) x z).ne'
    rw [curvK, metK_self, exp_neg]
    field_simp
  have q1 : cubK β (2 * b) (2 * c) (2 * a) = cubK β (2 * a) (2 * b) (2 * c) := by
    rw [cubK_comm₁₃, cubK_comm₂₃]
  have q2 : cubK β (2 * c) (2 * a) (2 * b) = cubK β (2 * a) (2 * b) (2 * c) := by
    rw [cubK_comm₁₂, cubK_comm₂₃]
  have q3 : metK β (2 * b) (2 * c) * metK β (2 * c) (2 * a) * metK β (2 * a) (2 * b) =
      metK β (2 * a) (2 * b) * metK β (2 * b) (2 * c) * metK β (2 * c) (2 * a) := by ring
  have q4 : metK β (2 * c) (2 * a) * metK β (2 * a) (2 * b) * metK β (2 * b) (2 * c) =
      metK β (2 * a) (2 * b) * metK β (2 * b) (2 * c) * metK β (2 * c) (2 * a) := by ring
  have hh : ∀ x y : ℝ, (2 * y - 2 * x) / 2 = y - x := fun x y ↦ by ring
  rw [wydHs, log_exp, log_exp, log_exp, hsL, C, C, C, q1, q2, q3, q4,
    cubK_sq_eq h0 h1 h2 hab hbc hca]
  simp only [cubK_div_metK h0 h1 h2, hh, hypH, neg_mul]
  ring

/-- `H` depends on `d` only through `|d|`. -/
theorem hypH_neg (d a b c : ℝ) : hypH (-d) a b c = hypH d a b c := by
  have h1 : ∀ s, hypPhi (-d) s = hypPhi d s := fun s ↦ by
    simp only [hypPhi, neg_mul, sinh_neg, neg_div_neg_eq, neg_sq]
  have h2 : ∀ s, hypPhi' (-d) s = hypPhi' d s := fun s ↦ by
    simp only [hypPhi', neg_mul, cosh_neg, neg_sq]
  have h3 : ∀ s, qubitK (-d) s = qubitK d s := fun s ↦ by
    rw [← qubitK_abs (-d), abs_neg, qubitK_abs]
  simp only [hypH, h1, h2, h3]

end WYD
