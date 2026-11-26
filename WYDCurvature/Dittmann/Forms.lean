/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Metric.Kernel
import WYDCurvature.Dittmann.Reduction
import WYDCurvature.Dittmann.Ineq63

/-!
# The two-point form of `hs_β`, and Dittmann's inequalities (62) and (63)

`hs_β(x, x, l) = d²/(24 l) ψ(½ log (l/x))`, `d = 2β - 1`, with `ψ = e^{2s}(K-1)(3K+1) - 2(K+1)²`
and `K = qubitK d` (`wydHs_self_left`). With `WYD.Ineq63.wyd_ineq63` this is (63); the sum
`hs(x, x, y) + hs(x, y, y)` gives (62).
-/

open Set Filter Real
open scoped Topology
open WYD.Ineq63 (qubitK psi Data)

namespace WYD

variable {β : ℝ}

/-! ### The two-point kernel -/

theorem qubitK_zero (d : ℝ) : qubitK d 0 = 0 := by simp [qubitK]

theorem qubitK_neg (d s : ℝ) : qubitK d (-s) = -qubitK d s := by
  simp only [qubitK, mul_neg, sinh_neg, cosh_neg]; ring

theorem qubitK_abs (d s : ℝ) : qubitK |d| s = qubitK d s := by
  rcases abs_choice d with h | h <;> rw [h]
  simp only [qubitK, neg_mul, sinh_neg, cosh_neg]
  rw [← neg_div_neg_eq]; congr 1 <;> ring

theorem cosh_sub_ne {d s : ℝ} (hd : d ^ 2 ≠ 1) (hs : s ≠ 0) : cosh s - cosh (d * s) ≠ 0 := by
  intro h
  have h1 : |s| = |d * s| := by
    have : cosh s = cosh (d * s) := sub_eq_zero.1 h
    rcases lt_trichotomy |s| |d * s| with h' | h' | h'
    · exact absurd this (cosh_lt_cosh.2 h').ne
    · exact h'
    · exact absurd this (cosh_lt_cosh.2 h').ne'
  rw [abs_mul] at h1
  have h2 : |d| = 1 :=
    (mul_right_cancel₀ (abs_pos.2 hs).ne' (show (1 : ℝ) * |s| = |d| * |s| by rwa [one_mul])).symm
  exact hd (by rw [← sq_abs, h2, one_pow])

/-- **The two-point kernel**: `C(X, X, Y)/M(X, Y) = (d/2)(1 - K((Y - X)/2))`. -/
theorem cubK_div_metK (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) (X Y : ℝ) :
    cubK β X X Y / metK β X Y = (2 * β - 1) / 2 * (1 - qubitK (2 * β - 1) ((Y - X) / 2)) := by
  rcases eq_or_ne X Y with rfl | hXY
  · rw [cubK_self, metK_self, sub_self, zero_div, qubitK_zero, sub_zero, mul_one,
      mul_div_assoc, div_self (exp_pos _).ne', mul_one]
  have h1' : 1 - β ≠ 0 := sub_ne_zero.2 h1.symm
  set s := (Y - X) / 2 with hs
  have hs0 : s ≠ 0 := by
    rw [hs]; exact div_ne_zero (sub_ne_zero.2 hXY.symm) two_ne_zero
  have hC : cubK β X X Y * (X - Y) = exp (β * X) * e1 ((1 - β) * Y) ((1 - β) * X) -
      e1 (β * Y) (β * X) * exp ((1 - β) * X) := by
    rw [cubK_comm₂₃, cubK_mul_sub, e1_self, e1_self]
  have key : ∀ b : ℝ, b ≠ 0 → e1 (b * X) (b * Y) = exp (b * X) * exp (b * s) * sinh (b * s) / (b * s) := by
    intro b hb
    have hne : b * X ≠ b * Y := fun h ↦ hXY (mul_left_cancel₀ hb h)
    rw [e1_of_ne hne, sinh_eq, show b * Y = b * X + (b * s + b * s) by rw [hs]; ring, exp_add,
      exp_add, exp_neg]
    have := exp_pos (b * s); have := exp_pos (b * X)
    field_simp
    ring
  have hsh : ∀ b : ℝ, b ≠ 0 → sinh (b * s) ≠ 0 := fun b hb h ↦
    mul_ne_zero hb hs0 (sinh_eq_zero.1 h)
  have hd2 : (2 * β - 1) ^ 2 ≠ 1 := fun h ↦ by
    have : β * (1 - β) = 0 := by linarith
    exact mul_ne_zero h0 h1' this
  have hcne := cosh_sub_ne hd2 hs0
  have hM := (metK_pos (β := β) X Y).ne'
  rw [div_eq_iff hM]
  apply mul_right_cancel₀ (sub_ne_zero.2 hXY)
  rw [hC, e1_comm ((1 - β) * Y), e1_comm (β * Y), metK, key β h0, key (1 - β) h1',
    show X - Y = -2 * s by rw [hs]; ring, qubitK]
  -- product formulas
  have p1 : cosh s = cosh (β * s) * cosh ((1 - β) * s) + sinh (β * s) * sinh ((1 - β) * s) := by
    rw [← cosh_add]; congr 1; ring
  have p2 : cosh ((2 * β - 1) * s) =
      cosh (β * s) * cosh ((1 - β) * s) - sinh (β * s) * sinh ((1 - β) * s) := by
    rw [← cosh_sub]; congr 1; ring
  have p3 : sinh s = sinh (β * s) * cosh ((1 - β) * s) + cosh (β * s) * sinh ((1 - β) * s) := by
    rw [← sinh_add]; congr 1; ring
  have p4 : sinh ((2 * β - 1) * s) =
      sinh (β * s) * cosh ((1 - β) * s) - cosh (β * s) * sinh ((1 - β) * s) := by
    rw [← sinh_sub]; congr 1; ring
  rw [p1, p2] at hcne
  rw [p1, p2, p3, p4]
  have ea : exp (β * s) = cosh (β * s) + sinh (β * s) := (cosh_add_sinh _).symm
  have eb : exp ((1 - β) * s) = cosh ((1 - β) * s) + sinh ((1 - β) * s) := (cosh_add_sinh _).symm
  have ia := cosh_sq (β * s); have ib := cosh_sq ((1 - β) * s)
  have sa := hsh β h0; have sb := hsh (1 - β) h1'
  rw [ea, eb]
  set ca := cosh (β * s); set sa' := sinh (β * s); set cb := cosh ((1 - β) * s)
  set sb' := sinh ((1 - β) * s)
  have hsq : ca * cb + sa' * sb' - (ca * cb - sa' * sb') = 2 * (sa' * sb') := by ring
  rw [hsq]
  have hab := mul_ne_zero sa sb
  have h2' : β * 2 - 1 ≠ 0 := by rwa [mul_comm]
  field_simp
  linear_combination (-2 * β * sb' * (cb + sb')) * ia + 2 * (1 - β) * sa' * (ca + sa') * ib

/-- `3 hs(X, X, Y)` in terms of the two-point kernel. -/
theorem hsL_self_left_eq (X Y : ℝ) : 3 * hsL β X X Y =
    (3 * (cubK β X X Y / metK β X Y) ^ 2 / 2 - (2 * β - 1) * (cubK β X X Y / metK β X Y)) / exp X -
      (cubK β Y Y X / metK β Y X) ^ 2 / exp Y := by
  have h := (metK_pos (β := β) X Y).ne'
  have e1 := exp_pos X; have e2 := exp_pos Y
  rw [hsL, curvK_comm₂₃ X Y X, curvK, curvK, cubK_self, metK_self, metK_comm Y X, metK_self,
    cubK_comm₁₂ Y X X, cubK_comm₂₃ X Y X]
  field_simp
  ring

/-- **The two-point form**: `hs(X, X, Y) = d²/24 e^{-Y} ψ((Y - X)/2)`. -/
theorem hsL_self_left (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) (X Y : ℝ) :
    hsL β X X Y = (2 * β - 1) ^ 2 / (24 * exp Y) * psi (qubitK (2 * β - 1)) ((Y - X) / 2) := by
  have h := hsL_self_left_eq (β := β) X Y
  rw [cubK_div_metK h0 h1 h2, cubK_div_metK h0 h1 h2,
    show (X - Y) / 2 = -((Y - X) / 2) by ring, qubitK_neg] at h
  have hX : exp Y = exp X * exp (2 * ((Y - X) / 2)) := by rw [← exp_add]; congr 1; ring
  have e1 := exp_pos X; have e2 := exp_pos (2 * ((Y - X) / 2))
  have h' : hsL β X X Y = (3 * hsL β X X Y) / 3 := by ring
  rw [h', h, psi, hX]
  field_simp
  ring

/-- **The two-point form on eigenvalues**: `hs(x, x, l) = d²/(24 l) ψ(½ log (l/x))`. -/
theorem wydHs_self_left (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) {x l : ℝ}
    (hl : 0 < l) : wydHs β x x l =
      (2 * β - 1) ^ 2 / (24 * l) * psi (qubitK (2 * β - 1)) ((log l - log x) / 2) := by
  rw [wydHs, hsL_self_left h0 h1 h2, exp_log hl]

/-! ### The curvature function is symmetric and smooth -/

theorem isCurvFun_wydHs (β : ℝ) : IsCurvFun (wydHs β) :=
  ⟨wydHs_comm₁₂, wydHs_comm₂₃, fun h1 h2 h3 n ↦ contDiffAt_wydHs h1 h2 h3 n⟩

/-! ### (63) -/

theorem psi_qubitK_abs (d : ℝ) : psi (qubitK |d|) = psi (qubitK d) := by
  rw [show qubitK |d| = qubitK d from funext (qubitK_abs d)]

/-- The derivative of `x ↦ hs(x, x, l)`. -/
theorem hasDerivAt_wydHs_self (β : ℝ) {x l : ℝ} (hx : 0 < x) (hl : 0 < l) :
    HasDerivAt (fun x ↦ wydHs β x x l) (2 * hsDeriv (wydHs β) x x l) x := by
  have := (isCurvFun_wydHs β).hasDerivAt_comp (hasDerivAt_id x) (hasDerivAt_id x)
    (hasDerivAt_const x l) hx hx hl
  exact this.congr_deriv (by simp; ring)

/-- `ψ` is differentiable, because `hs` is. -/
theorem hasDerivAt_psi (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) (s : ℝ) :
    HasDerivAt (psi (qubitK (2 * β - 1)))
      (-(96 / (2 * β - 1) ^ 2) * exp (-(2 * s)) *
        hsDeriv (wydHs β) (exp (-(2 * s))) (exp (-(2 * s))) 1) s := by
  have hx := exp_pos (-(2 * s))
  have hf : psi (qubitK (2 * β - 1)) = fun s ↦ 24 / (2 * β - 1) ^ 2 *
      wydHs β (exp (-(2 * s))) (exp (-(2 * s))) 1 := by
    funext s
    rw [wydHs_self_left h0 h1 h2 one_pos, log_one, log_exp]
    field_simp
    ring_nf
  rw [hf]
  have hd : HasDerivAt (fun s : ℝ ↦ exp (-(2 * s))) (exp (-(2 * s)) * (-2)) s := by
    have := (((hasDerivAt_id s).const_mul 2).neg).exp
    simpa using this
  have := ((hasDerivAt_wydHs_self β hx one_pos).comp s hd).const_mul (24 / (2 * β - 1) ^ 2)
  exact this.congr_deriv (by ring)

/-- **Dittmann's inequality (63) for the WYD metrics**, `β ∈ [-1, 2] \ {0, ½, 1}`, strictly. -/
theorem wyd_63 (hm : -1 ≤ β) (hM : β ≤ 2) (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0)
    {x y l : ℝ} (hx : 0 < x) (hxy : x < y) (hl : 0 < l) :
    0 < hsDeriv (wydHs β) x x l - hsDeriv (wydHs β) y y l := by
  have hy := hx.trans hxy
  set d := 2 * β - 1 with hd
  have hder : ∀ x, 0 < x → hsDeriv (wydHs β) x x l =
      -(d ^ 2 / (96 * l ^ 2)) *
        (exp (2 * ((log l - log x) / 2)) * deriv (psi (qubitK d)) ((log l - log x) / 2)) := by
    intro x hx
    have hs : HasDerivAt (fun x ↦ (log l - log x) / 2) (-x⁻¹ / 2) x :=
      ((hasDerivAt_log hx.ne').const_sub (log l)).div_const 2
    have hψ := (hasDerivAt_psi h0 h1 h2 ((log l - log x) / 2)).differentiableAt.hasDerivAt
    have h3 := (hψ.comp x hs).const_mul (d ^ 2 / (24 * l))
    have hfun : (fun x ↦ wydHs β x x l) =
        fun x ↦ d ^ 2 / (24 * l) * (psi (qubitK d) ∘ fun x ↦ (log l - log x) / 2) x :=
      funext fun x ↦ wydHs_self_left h0 h1 h2 hl
    have h4 := hasDerivAt_wydHs_self β hx hl
    rw [hfun] at h4
    have h5 := h4.unique h3
    have he : exp (2 * ((log l - log x) / 2)) = l / x := by
      rw [show 2 * ((log l - log x) / 2) = log l - log x by ring, exp_sub, exp_log hl, exp_log hx]
    rw [he]
    have : hsDeriv (wydHs β) x x l = (2 * hsDeriv (wydHs β) x x l) / 2 := by ring
    rw [this, h5]
    field_simp
    ring
  have hanti := WYD.Ineq63.wyd_ineq63 (d := |d|) (abs_pos.2 h2) (abs_le.2 ⟨by linarith, by linarith⟩)
    (fun h ↦ by
      rcases abs_eq (zero_le_one) |>.1 h with h | h
      · exact h1 (by linarith)
      · exact h0 (by linarith))
  rw [psi_qubitK_abs] at hanti
  have hlog : (log l - log y) / 2 < (log l - log x) / 2 := by
    have := log_lt_log hx hxy; linarith
  have := hanti hlog
  simp only at this
  rw [hder x hx, hder y hy]
  have hc : 0 < d ^ 2 / (96 * l ^ 2) := by positivity
  nlinarith

/-! ### (62) -/

section Qubit

variable {d : ℝ} {φ φ₁ : ℝ → ℝ}

/-- `φ₁ sinh - φ cosh > 0` for `s > 0`. -/
theorem W_pos (H : Data d φ φ₁) {s : ℝ} (hs : 0 < s) : 0 < φ₁ s * sinh s - φ s * cosh s :=
  Data.mono_of_deriv (f := fun t ↦ φ₁ t * sinh t - φ t * cosh t)
    (f' := fun t ↦ sinh t * (d ^ 2 * φ t + sinh t - φ t))
    (fun t ↦ (((H.h1 t).mul (hasDerivAt_sinh t)).sub ((H.h0 t).mul (hasDerivAt_cosh t))).congr_deriv
      (by ring)) (by simp [H.z0, H.z1])
    (fun t ht ↦ mul_pos (sinh_pos_iff.2 ht) (H.pos₂ t ht)) hs

/-- The qubit curvature function `(K cosh s + sinh s)² - 4 cosh² s`. -/
noncomputable def qubitG (K : ℝ → ℝ) (s : ℝ) : ℝ := (K s * cosh s + sinh s) ^ 2 - 4 * cosh s ^ 2

/-- The qubit curvature function is strictly decreasing in `s > 0`. -/
theorem hasDerivAt_qubitG (H : Data d φ φ₁) {s : ℝ} (hs : 0 < s) :
    ∃ g < 0, HasDerivAt (qubitG fun s ↦ φ s / φ₁ s) g s := by
  have hk := H.hk hs
  have hS := H.S_gt_one hs
  have hW := W_pos H hs
  have hφ₁ := H.pos s hs
  have hk0 := H.k_pos hs
  have hc := cosh_pos s
  have hsh := sinh_pos_iff.2 hs
  have hcs := sinh_lt_cosh s
  set k := WYD.Ineq63.k φ φ₁ s with hkdef
  set v := WYD.Ineq63.v d φ φ₁ s with hvdef
  have hJ : HasDerivAt (fun s ↦ φ s / φ₁ s * cosh s + sinh s) (v * cosh s + k * sinh s + cosh s) s :=
    (hk.mul (hasDerivAt_cosh s)).add (hasDerivAt_sinh s)
  refine ⟨_, ?_, (hJ.pow 2).sub (((hasDerivAt_cosh s).pow 2).const_mul 4)⟩
  have hω : 0 < sinh s - k * cosh s := by
    have : φ s = k * φ₁ s := by rw [hkdef, WYD.Ineq63.k, div_mul_cancel₀ _ hφ₁.ne']
    rw [this] at hW
    have : 0 < φ₁ s * (sinh s - k * cosh s) := by linarith
    exact (mul_pos_iff_of_pos_left hφ₁).1 this
  have hω' : 0 < cosh s - v * cosh s - k * sinh s := by
    have hv : v = 1 - k * WYD.Ineq63.S d φ φ₁ s := rfl
    rw [hv]
    have h : 0 < k * (WYD.Ineq63.S d φ φ₁ s * cosh s - sinh s) := mul_pos hk0 (by nlinarith)
    linarith
  have hJ0 : 0 < k * cosh s + sinh s := by positivity
  change (2 : ℕ) * (k * cosh s + sinh s) ^ (2 - 1) * (v * cosh s + k * sinh s + cosh s) -
    4 * ((2 : ℕ) * cosh s ^ (2 - 1) * sinh s) < 0
  norm_num
  nlinarith [mul_pos hω hc, mul_pos hJ0 hω']

end Qubit

/-- The qubit curvature: `hs(u, u, w) + hs(u, w, w) = d²/(6 (u + w)) (𝒢(s) + 1)`, `s = ½ log (w/u)`. -/
theorem wydHs_qubit (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) {u w : ℝ} (hu : 0 < u)
    (hw : 0 < w) : wydHs β u u w + wydHs β u w w =
      (2 * β - 1) ^ 2 / (6 * (u + w)) *
        (qubitG (qubitK (2 * β - 1)) ((log w - log u) / 2) + 1) := by
  rw [(isCurvFun_wydHs β).cyclic u w w, wydHs_self_left h0 h1 h2 hw, wydHs_self_left h0 h1 h2 hu,
    show (log u - log w) / 2 = -((log w - log u) / 2) by ring, psi, psi, qubitK_neg, qubitG]
  set s := (log w - log u) / 2 with hs
  set K := qubitK (2 * β - 1) s
  have hE : w = u * exp s ^ 2 := by
    rw [← exp_nat_mul, hs, show ((2 : ℕ) : ℝ) * ((log w - log u) / 2) = log w - log u by
      push_cast; ring, exp_sub, exp_log hw, exp_log hu]
    field_simp
  have e1 : exp (2 * s) = exp s ^ 2 := by rw [← exp_nat_mul]; norm_num
  have e2 : exp (2 * -s) = (exp s ^ 2)⁻¹ := by rw [mul_neg, exp_neg, e1]
  rw [e1, e2, cosh_eq, sinh_eq, exp_neg, hE]
  have := exp_pos s
  generalize exp s = E at *
  field_simp
  ring

/-- **Dittmann's inequality (62) for the WYD metrics, strict**, `β ∈ [-1, 2] \ {0, ½, 1}`. -/
theorem wyd_62 (hm : -1 ≤ β) (hM : β ≤ 2) (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < 2 * hsDeriv (wydHs β) x x y - hsDeriv (wydHs β) y x x - 2 * hsDeriv (wydHs β) y x y +
      hsDeriv (wydHs β) x y y := by
  have hy := hx.trans hxy
  have C := isCurvFun_wydHs β
  set d := 2 * β - 1 with hd
  have hd1 : |d| ≠ 1 := fun h ↦ by
    rcases abs_eq (zero_le_one) |>.1 h with h | h
    · exact h1 (by linarith)
    · exact h0 (by linarith)
  have hd3 : |d| ≤ 3 := abs_le.2 ⟨by linarith, by linarith⟩
  have hd0 : 0 < |d| := abs_pos.2 h2
  -- the curve
  have hu : HasDerivAt (fun t : ℝ ↦ x + t) 1 0 := (hasDerivAt_id 0).const_add x
  have hw : HasDerivAt (fun t : ℝ ↦ y - t) (-1) 0 := (hasDerivAt_id 0).const_sub y
  have hx' : 0 < x + (0 : ℝ) := by simpa
  have hy' : 0 < y - (0 : ℝ) := by simpa
  have hF := (C.hasDerivAt_comp hu hu hw hx' hx' hy').add (C.hasDerivAt_comp hu hw hw hx' hy' hy')
  -- the closed form along the curve
  have hne : 1 - |d| ^ 2 ≠ 0 := by
    intro h; apply hd1; nlinarith [mul_self_nonneg (|d| - 1)]
  have hK : qubitK d = fun s ↦ (sinh s - sinh (|d| * s) / |d|) / (1 - |d| ^ 2)
      / ((cosh s - cosh (|d| * s)) / (1 - |d| ^ 2)) := by
    funext s
    rw [← qubitK_abs, div_div_div_cancel_right₀ hne,
      show sinh s - sinh (|d| * s) / |d| = (|d| * sinh s - sinh (|d| * s)) / |d| by field_simp,
      div_div, qubitK]
  have hs0 : 0 < (log (y - 0) - log (x + 0)) / 2 := by
    have := log_lt_log hx hxy; simp only [sub_zero, add_zero]; linarith
  obtain ⟨g, hg, hG⟩ := hasDerivAt_qubitG (WYD.Ineq63.data_of_ne_one hd0 hd3 hd1) hs0
  rw [← hK] at hG
  have hs : HasDerivAt (fun t ↦ (log (y - t) - log (x + t)) / 2)
      ((-1 / (y - 0) - 1 / (x + 0)) / 2) 0 := ((hw.log hy'.ne').sub (hu.log hx'.ne')).div_const 2
  have hc := ((hG.comp (0 : ℝ) hs).add_const 1).const_mul (d ^ 2 / (6 * (x + y)))
  have hev : (fun t ↦ wydHs β (x + t) (x + t) (y - t) + wydHs β (x + t) (y - t) (y - t)) =ᶠ[𝓝 0]
      fun t ↦ d ^ 2 / (6 * (x + y)) *
        ((qubitG (qubitK d) ∘ fun t ↦ (log (y - t) - log (x + t)) / 2) t + 1) := by
    have a1 := hu.continuousAt.eventually (eventually_gt_nhds hx')
    have a2 := hw.continuousAt.eventually (eventually_gt_nhds hy')
    filter_upwards [a1, a2] with t h3 h4
    rw [wydHs_qubit h0 h1 h2 h3 h4, show x + t + (y - t) = x + y by ring]
    rfl
  have h := hF.unique (hc.congr_of_eventuallyEq hev)
  simp only [add_zero, sub_zero] at h
  have hpos : 0 < d ^ 2 / (6 * (x + y)) * (g * ((-1 / y - 1 / x) / 2)) := by
    have h3 : (-1 / y - 1 / x) / 2 < 0 := by
      have := one_div_pos.2 hx; have := one_div_pos.2 hy; rw [neg_div]; linarith
    have h4 : 0 < g * ((-1 / y - 1 / x) / 2) := mul_pos_of_neg_of_neg hg h3
    have : 0 < d ^ 2 := by positivity
    positivity
  rw [C.hsDeriv_comm₂₃ y x y]
  rw [C.hsDeriv_comm₂₃ y x y] at h
  linarith

end WYD
