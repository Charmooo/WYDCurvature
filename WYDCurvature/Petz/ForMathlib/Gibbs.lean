/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.ForMathlib.Majorization
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Heating mixes: Gibbs distributions are ordered by temperature

The Gibbs distribution of energy levels `E₁, …, Eₙ` at inverse temperature `β` is
`pᵢ(β) = e^{-β Eᵢ} / ∑ⱼ e^{-β Eⱼ}`. For `0 ≤ β₁ ≤ β₂` the hotter distribution `p(β₁)` is majorized
by the colder one `p(β₂)`. This is the ordering of Gibbs states from which Petz derives his
condition (i), that the scalar curvature increases with the temperature, from the monotonicity of
the scalar curvature under mixing (Petz 1994, p. 791).

The proof compares the two distributions through their ratio. Listed by decreasing energy, both
increase, and so does the ratio `p(β₂)/p(β₁)`, which is `e^{-(β₂ - β₁) Eᵢ}` up to a constant.
Reweighting a distribution by an increasing factor moves mass towards its largest entries
(`Majorization.sum_range_mul_le`), and that is majorization (`isMajorizedBy_of_monotone_div`).

## Main statements

* `isMajorizedBy_of_monotone_div`: majorization from an increasing likelihood ratio.
* `isMajorizedBy_gibbsDist`: for `0 ≤ β₁ ≤ β₂`, `p(β₁)` is majorized by `p(β₂)`.

## References

* [D. Petz, *Geometry of canonical correlation on the state space of a quantum system*][petz1994]
-/

open Finset

namespace Majorization

/-- **Reweighting by an increasing factor moves mass to the end**: for weights `x ≥ 0` on `[0, n)`
with positive total and `r` increasing there, if `∑ xᵢ rᵢ = ∑ xᵢ`, then
`∑_{i < k} xᵢ rᵢ ≤ ∑_{i < k} xᵢ` for every `k ≤ n`. -/
theorem sum_range_mul_le {x r : ℕ → ℝ} {n k : ℕ} (hk : k ≤ n) (hx : ∀ i < n, 0 ≤ x i)
    (hr : ∀ i j, i ≤ j → j < n → r i ≤ r j) (hpos : 0 < ∑ i ∈ range n, x i)
    (hsum : ∑ i ∈ range n, x i * r i = ∑ i ∈ range n, x i) :
    ∑ i ∈ range k, x i * r i ≤ ∑ i ∈ range k, x i := by
  -- Every head index `i < k` is reweighted by less than every tail index `j ≥ k`.
  have key : ∑ i ∈ range k, ∑ j ∈ Ico k n, x i * x j * (r i - r j) ≤ 0 :=
    sum_nonpos fun i hi ↦ sum_nonpos fun j hj ↦ by
      rw [mem_range] at hi
      rw [mem_Ico] at hj
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hx i (by omega)) (hx j hj.2))
        (sub_nonpos.2 (hr i j (by omega) hj.2))
  have e : ∑ i ∈ range k, ∑ j ∈ Ico k n, x i * x j * (r i - r j) =
      (∑ i ∈ range k, x i * r i) * (∑ j ∈ Ico k n, x j) -
        (∑ i ∈ range k, x i) * ∑ j ∈ Ico k n, x j * r j := by
    rw [sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [← sum_range_add_sum_Ico _ hk] at hpos hsum
  rw [← sum_range_add_sum_Ico _ hk] at hsum
  set u := ∑ i ∈ range k, x i * r i
  set a := ∑ i ∈ range k, x i
  set v := ∑ j ∈ Ico k n, x j * r j
  set b := ∑ j ∈ Ico k n, x j
  -- With `u + v = a + b`: `(u - a)(a + b) = u b - a v ≤ 0`.
  have h : (u - a) * (a + b) = u * b - a * v + a * (u + v - (a + b)) := by ring
  rw [hsum, sub_self, mul_zero, add_zero, ← e] at h
  refine le_of_not_gt fun hlt ↦ ?_
  linarith [mul_pos (sub_pos.2 hlt) hpos]

end Majorization

open Majorization

/-- **Majorization from an increasing likelihood ratio**: if `x > 0` and `y` have the same total
and one ordering `σ` of the entries makes `x`, `y` and the ratio `y / x` all increasing, then `x`
is majorized by `y`. -/
theorem isMajorizedBy_of_monotone_div {n : ℕ} {x y : Fin n → ℝ} (σ : Equiv.Perm (Fin n))
    (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i = ∑ i, y i) (hxσ : Monotone (x ∘ σ))
    (hyσ : Monotone (y ∘ σ)) (hr : Monotone fun i ↦ y (σ i) / x (σ i)) : IsMajorizedBy x y := by
  refine ⟨hsum, fun k hk ↦ ?_⟩
  have ex : sortInc x = x ∘ σ := (Tuple.comp_sort_eq_comp_iff_monotone.2 hxσ).symm
  have ey : sortInc y = y ∘ σ := (Tuple.comp_sort_eq_comp_iff_monotone.2 hyσ).symm
  rw [ex, ey]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : k = 0 := by omega
    simp
  have hxy : ∀ i, toSeq (x ∘ σ) i * toSeq (fun i ↦ y (σ i) / x (σ i)) i = toSeq (y ∘ σ) i := by
    intro i
    by_cases h : i < n
    · simp only [toSeq, h, ↓reduceDIte, Function.comp_apply]
      exact mul_div_cancel₀ _ (hx _).ne'
    · simp [toSeq, h]
  have h := sum_range_mul_le (x := toSeq (x ∘ σ)) (r := toSeq fun i ↦ y (σ i) / x (σ i)) hk
    (fun i hi ↦ by simp only [toSeq, hi, ↓reduceDIte, Function.comp_apply]; exact (hx _).le)
    (fun i j hij hj ↦ by
      simp only [toSeq, hj, lt_of_le_of_lt hij hj, ↓reduceDIte]
      exact hr (Fin.mk_le_mk.2 hij))
    (by
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      rw [sum_range_toSeq]
      exact sum_pos (fun i _ ↦ hx _) univ_nonempty)
    (by
      simp only [hxy, sum_range_toSeq, Function.comp_apply]
      rw [Equiv.sum_comp σ x, Equiv.sum_comp σ y, hsum])
  simpa only [hxy] using h

/-! ### Gibbs distributions -/

section Gibbs

variable {ι : Type*} [Fintype ι]

/-- The **Gibbs distribution** of energy levels `E` at inverse temperature `β`:
`pᵢ = e^{-β Eᵢ} / ∑ⱼ e^{-β Eⱼ}`. -/
noncomputable def gibbsDist (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  Real.exp (-(β * E i)) / ∑ j, Real.exp (-(β * E j))

/-- The partition function `∑ⱼ e^{-β Eⱼ}` is positive. -/
theorem sum_exp_neg_mul_pos [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    0 < ∑ j, Real.exp (-(β * E j)) :=
  sum_pos (fun _ _ ↦ Real.exp_pos _) univ_nonempty

theorem gibbsDist_pos [Nonempty ι] (E : ι → ℝ) (β : ℝ) (i : ι) : 0 < gibbsDist E β i :=
  div_pos (Real.exp_pos _) (sum_exp_neg_mul_pos E β)

theorem sum_gibbsDist [Nonempty ι] (E : ι → ℝ) (β : ℝ) : ∑ i, gibbsDist E β i = 1 := by
  simp only [gibbsDist, div_eq_mul_inv, ← sum_mul]
  exact mul_inv_cancel₀ (sum_exp_neg_mul_pos E β).ne'

/-- The Gibbs distribution does not depend on how the levels are labeled. -/
theorem gibbsDist_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (E : ι → ℝ) (β : ℝ) :
    gibbsDist (E ∘ e) β = gibbsDist E β ∘ e := by
  ext i
  simp only [gibbsDist, Function.comp_apply]
  congr 1
  exact e.sum_comp fun j ↦ Real.exp (-(β * E j))

end Gibbs

/-- **Heating mixes**: for energy levels `E` and inverse temperatures `0 ≤ β₁ ≤ β₂`, the Gibbs
distribution at `β₁` is majorized by the one at `β₂`. -/
theorem isMajorizedBy_gibbsDist {n : ℕ} (E : Fin n → ℝ) {β₁ β₂ : ℝ} (h₁ : 0 ≤ β₁)
    (h₁₂ : β₁ ≤ β₂) : IsMajorizedBy (gibbsDist E β₁) (gibbsDist E β₂) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨by simp, fun k hk ↦ ?_⟩
    obtain rfl : k = 0 := by omega
    simp
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- List the levels by decreasing energy.
  set σ := Tuple.sort fun i ↦ -E i
  have hE : Monotone fun i ↦ -E (σ i) := Tuple.monotone_sort fun i ↦ -E i
  have hmono : ∀ β, 0 ≤ β → Monotone (gibbsDist E β ∘ σ) := fun β hβ i j hij ↦ by
    simp only [Function.comp_apply, gibbsDist]
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg
      (mul_le_mul_of_nonneg_left (neg_le_neg_iff.1 (hE hij)) hβ))) (sum_exp_neg_mul_pos E β).le
  refine isMajorizedBy_of_monotone_div σ (gibbsDist_pos E β₁)
    (by rw [sum_gibbsDist, sum_gibbsDist]) (hmono β₁ h₁) (hmono β₂ (h₁.trans h₁₂)) ?_
  -- The ratio is `e^{(β₂ - β₁)(-Eᵢ)}` times a positive constant.
  have hratio : ∀ i, gibbsDist E β₂ i / gibbsDist E β₁ i = Real.exp ((β₂ - β₁) * -E i) *
      ((∑ j, Real.exp (-(β₁ * E j))) / ∑ j, Real.exp (-(β₂ * E j))) := by
    intro i
    have h1 := (sum_exp_neg_mul_pos E β₁).ne'
    have h2 := (sum_exp_neg_mul_pos E β₂).ne'
    simp only [gibbsDist]
    rw [show -(β₂ * E i) = (β₂ - β₁) * -E i + -(β₁ * E i) by ring, Real.exp_add]
    field_simp
  intro i j hij
  simp only [hratio]
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hE hij) (sub_nonneg.2 h₁₂)))
    (div_pos (sum_exp_neg_mul_pos E β₁) (sum_exp_neg_mul_pos E β₂)).le
