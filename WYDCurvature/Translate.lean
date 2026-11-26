/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Hyperbolic
import WYDCurvature.Main

/-!
# (64) and (65) in the hyperbolic form

* `HypCond64 d`: `e^{-2a} ∂_a H - e^{-2b} ∂_b H ≥ 0` for `a < b` and `c ≠ a, b`;
* `HypCond65 d`: `∂_a² H - 2 ∂_a H ≤ 0` for pairwise distinct `a, b, c`.

They imply (64) and (65) for `hs_β`, `d = 2β - 1` (`ineq64_of_hyp`, `ineq65_of_hyp`), so the
conjecture for `β` follows from them (`wyd_curvature_lt_of_hyp`). These two statements about the
elementary function `hypH` are what the computer check certifies for every `d² ∈ [0, 9]`.
-/

open Set Filter Real
open scoped Topology

namespace WYD

/-- (64) in the hyperbolic form. -/
def HypCond64 (d : ℝ) : Prop := ∀ a b c : ℝ, a < b → c ≠ a → c ≠ b →
  0 ≤ exp (-2 * a) * deriv (fun s ↦ hypH d s b c) a - exp (-2 * b) * deriv (fun s ↦ hypH d a s c) b

/-- (65) in the hyperbolic form. -/
def HypCond65 (d : ℝ) : Prop := ∀ a b c : ℝ, a ≠ b → b ≠ c → c ≠ a →
  deriv (deriv fun s ↦ hypH d s b c) a - 2 * deriv (fun s ↦ hypH d s b c) a ≤ 0

/-! ### Regularity of `hs'` -/

section Regular

variable {hs : ℝ → ℝ → ℝ → ℝ}

theorem IsCurvFun.hsDeriv_eq (C : IsCurvFun hs) {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    hsDeriv hs x y z =
      fderiv ℝ (fun q : ℝ × ℝ × ℝ ↦ hs q.1 q.2.1 q.2.2) (x, y, z) (1, 0, 0) := by
  have hF := ((C.smooth (p := (x, y, z)) hx hy hz 1).differentiableAt one_ne_zero).hasFDerivAt
  have hc : HasDerivAt (fun u : ℝ ↦ (u, y, z)) ((1, 0, 0) : ℝ × ℝ × ℝ) x :=
    (hasDerivAt_id x).prodMk ((hasDerivAt_const x y).prodMk (hasDerivAt_const x z))
  exact (C.hasDerivAt_fst hx hy hz).unique (HasFDerivAt.comp_hasDerivAt
    (l := fun q : ℝ × ℝ × ℝ ↦ hs q.1 q.2.1 q.2.2) (f := fun u : ℝ ↦ (u, y, z)) x hF hc)

theorem IsCurvFun.contDiffAt_hsDeriv (C : IsCurvFun hs) {p : ℝ × ℝ × ℝ} (h1 : 0 < p.1)
    (h2 : 0 < p.2.1) (h3 : 0 < p.2.2) (n : ℕ) :
    ContDiffAt ℝ n (fun q : ℝ × ℝ × ℝ ↦ hsDeriv hs q.1 q.2.1 q.2.2) p := by
  have h : ContDiffAt ℝ n (fun q ↦
      fderiv ℝ (fun q : ℝ × ℝ × ℝ ↦ hs q.1 q.2.1 q.2.2) q (1, 0, 0)) p :=
    ((C.smooth h1 h2 h3 (n + 1)).fderiv_right (m := n) (by norm_cast)).clm_apply contDiffAt_const
  refine h.congr_of_eventuallyEq ?_
  have o1 := (continuous_fst (X := ℝ) (Y := ℝ × ℝ)).continuousAt.eventually (eventually_gt_nhds h1)
  have o2 := (continuous_fst.comp (continuous_snd (X := ℝ) (Y := ℝ × ℝ))).continuousAt.eventually
    (eventually_gt_nhds h2)
  have o3 := (continuous_snd.comp (continuous_snd (X := ℝ) (Y := ℝ × ℝ))).continuousAt.eventually
    (eventually_gt_nhds h3)
  filter_upwards [o1, o2, o3] with q hq1 hq2 hq3
  exact C.hsDeriv_eq hq1 hq2 hq3

/-- The second derivative in the first argument. -/
noncomputable def hsDeriv2 (hs : ℝ → ℝ → ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun q : ℝ × ℝ × ℝ ↦ hsDeriv hs q.1 q.2.1 q.2.2) p (1, 0, 0)

theorem IsCurvFun.hasDerivAt_hsDeriv (C : IsCurvFun hs) {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) : HasDerivAt (fun u ↦ hsDeriv hs u y z) (hsDeriv2 hs (x, y, z)) x := by
  have hF := ((C.contDiffAt_hsDeriv (p := (x, y, z)) hx hy hz 1).differentiableAt
    one_ne_zero).hasFDerivAt
  have hc : HasDerivAt (fun u : ℝ ↦ (u, y, z)) ((1, 0, 0) : ℝ × ℝ × ℝ) x :=
    (hasDerivAt_id x).prodMk ((hasDerivAt_const x y).prodMk (hasDerivAt_const x z))
  exact hF.comp_hasDerivAt x hc

theorem IsCurvFun.continuousAt_hsDeriv2 (C : IsCurvFun hs) {p : ℝ × ℝ × ℝ} (h1 : 0 < p.1)
    (h2 : 0 < p.2.1) (h3 : 0 < p.2.2) : ContinuousAt (hsDeriv2 hs) p :=
  (((C.contDiffAt_hsDeriv h1 h2 h3 1).fderiv_right (m := 0) (by norm_num)).clm_apply
    contDiffAt_const).continuousAt

end Regular

/-! ### The derivatives of `H` -/

variable {β : ℝ}

theorem hasDerivAt_exp_two (a : ℝ) : HasDerivAt (fun s : ℝ ↦ exp (2 * s)) (2 * exp (2 * a)) a := by
  have := ((hasDerivAt_id a).const_mul 2).exp
  simpa [mul_comm] using this

theorem hypH_eq (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) {a b c : ℝ} (hab : a ≠ b)
    (hbc : b ≠ c) (hca : c ≠ a) : hypH (2 * β - 1) a b c =
      ((2 * β - 1) ^ 2)⁻¹ * wydHs β (exp (2 * a)) (exp (2 * b)) (exp (2 * c)) := by
  rw [wydHs_eq_hypH h0 h1 h2 hab hbc hca]
  field_simp

theorem eventually_hypH_eq (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) {a b c : ℝ} (hab : a ≠ b)
    (hbc : b ≠ c) (hca : c ≠ a) : (fun s ↦ hypH (2 * β - 1) s b c) =ᶠ[𝓝 a]
      fun s ↦ ((2 * β - 1) ^ 2)⁻¹ * wydHs β (exp (2 * s)) (exp (2 * b)) (exp (2 * c)) := by
  filter_upwards [isOpen_ne.mem_nhds hab, isOpen_ne.mem_nhds hca.symm] with s hs hs'
  exact hypH_eq h0 h1 h2 hs hbc hs'.symm

theorem hasDerivAt_wydHs_exp (β a b c : ℝ) :
    HasDerivAt (fun s ↦ ((2 * β - 1) ^ 2)⁻¹ * wydHs β (exp (2 * s)) (exp (2 * b)) (exp (2 * c)))
      (((2 * β - 1) ^ 2)⁻¹ * (hsDeriv (wydHs β) (exp (2 * a)) (exp (2 * b)) (exp (2 * c)) *
        (2 * exp (2 * a)))) a :=
  (HasDerivAt.comp (h₂ := fun u ↦ wydHs β u (exp (2 * b)) (exp (2 * c)))
    (h := fun s ↦ exp (2 * s)) a ((isCurvFun_wydHs β).hasDerivAt_fst (exp_pos (2 * a))
      (exp_pos (2 * b)) (exp_pos (2 * c))) (hasDerivAt_exp_two a)).const_mul _

theorem deriv_hypH (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) {a b c : ℝ} (hab : a ≠ b)
    (hbc : b ≠ c) (hca : c ≠ a) : deriv (fun s ↦ hypH (2 * β - 1) s b c) a =
      ((2 * β - 1) ^ 2)⁻¹ * (hsDeriv (wydHs β) (exp (2 * a)) (exp (2 * b)) (exp (2 * c)) *
        (2 * exp (2 * a))) := by
  rw [(eventually_hypH_eq h0 h1 h2 hab hbc hca).deriv_eq]
  exact (hasDerivAt_wydHs_exp β a b c).deriv

theorem deriv_hypH_snd (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) {a b c : ℝ} (hab : a ≠ b)
    (hbc : b ≠ c) (hca : c ≠ a) : deriv (fun s ↦ hypH (2 * β - 1) a s c) b =
      ((2 * β - 1) ^ 2)⁻¹ * (hsDeriv (wydHs β) (exp (2 * b)) (exp (2 * a)) (exp (2 * c)) *
        (2 * exp (2 * b))) := by
  have hev : (fun s ↦ hypH (2 * β - 1) a s c) =ᶠ[𝓝 b]
      fun s ↦ ((2 * β - 1) ^ 2)⁻¹ * wydHs β (exp (2 * s)) (exp (2 * a)) (exp (2 * c)) := by
    filter_upwards [isOpen_ne.mem_nhds hab.symm, isOpen_ne.mem_nhds hbc] with s hs hs'
    rw [hypH_eq h0 h1 h2 hs.symm hs' hca, wydHs_comm₁₂]
  rw [hev.deriv_eq]
  exact (hasDerivAt_wydHs_exp β b a c).deriv

theorem deriv2_hypH (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) {a b c : ℝ} (hab : a ≠ b)
    (hbc : b ≠ c) (hca : c ≠ a) : deriv (deriv fun s ↦ hypH (2 * β - 1) s b c) a -
      2 * deriv (fun s ↦ hypH (2 * β - 1) s b c) a = ((2 * β - 1) ^ 2)⁻¹ *
        (hsDeriv2 (wydHs β) (exp (2 * a), exp (2 * b), exp (2 * c)) * (2 * exp (2 * a)) ^ 2) := by
  have hev : deriv (fun s ↦ hypH (2 * β - 1) s b c) =ᶠ[𝓝 a] fun s ↦ ((2 * β - 1) ^ 2)⁻¹ *
      (hsDeriv (wydHs β) (exp (2 * s)) (exp (2 * b)) (exp (2 * c)) * (2 * exp (2 * s))) := by
    filter_upwards [isOpen_ne.mem_nhds hab, isOpen_ne.mem_nhds hca.symm] with s hs hs'
    exact deriv_hypH h0 h1 h2 hs hbc hs'.symm
  have hd := ((HasDerivAt.comp (h₂ := fun u ↦ hsDeriv (wydHs β) u (exp (2 * b)) (exp (2 * c)))
    (h := fun s ↦ exp (2 * s)) a ((isCurvFun_wydHs β).hasDerivAt_hsDeriv (exp_pos (2 * a))
      (exp_pos (2 * b)) (exp_pos (2 * c))) (hasDerivAt_exp_two a)).mul
      ((hasDerivAt_exp_two a).const_mul 2)).const_mul (((2 * β - 1) ^ 2)⁻¹)
  have hd' : HasDerivAt (fun s ↦ ((2 * β - 1) ^ 2)⁻¹ *
      (hsDeriv (wydHs β) (exp (2 * s)) (exp (2 * b)) (exp (2 * c)) * (2 * exp (2 * s)))) _ a := hd
  rw [hev.deriv_eq, hd'.deriv, deriv_hypH h0 h1 h2 hab hbc hca]
  simp only [Function.comp_apply]
  ring

/-! ### The translation -/

theorem ineq64_of_hyp (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0)
    (H : HypCond64 (2 * β - 1)) : Ineq64 β := by
  have hd : 0 < ((2 * β - 1) ^ 2)⁻¹ := by positivity
  -- distinct arguments
  have key : ∀ x y l : ℝ, 0 < x → x < y → 0 < l → l ≠ x → l ≠ y →
      0 ≤ hsDeriv (wydHs β) x y l - hsDeriv (wydHs β) y x l := by
    intro x y l hx hxy hl hlx hly
    have hy := hx.trans hxy
    have e : ∀ z : ℝ, 0 < z → exp (2 * (log z / 2)) = z := fun z hz ↦ by
      rw [mul_div_cancel₀ _ two_ne_zero, exp_log hz]
    have ha : log x / 2 < log y / 2 := by have := log_lt_log hx hxy; linarith
    have hca : log l / 2 ≠ log x / 2 := fun h ↦ hlx (log_injOn_pos hl hx (by linarith))
    have hcb : log l / 2 ≠ log y / 2 := fun h ↦ hly (log_injOn_pos hl hy (by linarith))
    have h := H _ _ _ ha hca hcb
    rw [deriv_hypH h0 h1 h2 ha.ne hcb.symm hca, deriv_hypH_snd h0 h1 h2 ha.ne hcb.symm hca,
      neg_mul, neg_mul, exp_neg, exp_neg, e x hx, e y hy, e l hl] at h
    have h' : x⁻¹ * (((2 * β - 1) ^ 2)⁻¹ * (hsDeriv (wydHs β) x y l * (2 * x))) -
        y⁻¹ * (((2 * β - 1) ^ 2)⁻¹ * (hsDeriv (wydHs β) y x l * (2 * y))) =
        (2 * ((2 * β - 1) ^ 2)⁻¹) * (hsDeriv (wydHs β) x y l - hsDeriv (wydHs β) y x l) := by
      field_simp
    rw [h'] at h
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h
  intro x y l hx hxy hl
  have hy := hx.trans hxy
  have C := isCurvFun_wydHs β
  have hc : ∀ x y : ℝ, 0 < x → 0 < y → ContinuousAt (fun l ↦ hsDeriv (wydHs β) x y l) l :=
    fun x y hx hy ↦ (C.contDiffAt_hsDeriv (p := (x, y, l)) hx hy hl 0).continuousAt.comp
      (f := fun l : ℝ ↦ (x, y, l))
      (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id))
  have ht := (((hc x y hx hy).sub (hc y x hy hx)).tendsto).mono_left
    (nhdsWithin_le_nhds (s := {l}ᶜ))
  refine ge_of_tendsto ht ?_
  have hfin : ∀ᶠ l' in 𝓝[≠] l, l' ∉ ({x, y} : Set ℝ) :=
    nhdsNE_le_cofinite l ((Set.toFinite _).eventually_cofinite_notMem)
  filter_upwards [hfin, eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hl)] with l' h3 h4
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at h3
  exact key x y l' hx hxy h4 h3.1 h3.2

theorem ineq65_of_hyp (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0)
    (H : HypCond65 (2 * β - 1)) : Ineq65 β := by
  have C := isCurvFun_wydHs β
  have hd : 0 < ((2 * β - 1) ^ 2)⁻¹ := by positivity
  have key : ∀ x l m : ℝ, 0 < x → 0 < l → 0 < m → x ≠ l → l ≠ m → m ≠ x →
      hsDeriv2 (wydHs β) (x, l, m) ≤ 0 := by
    intro x l m hx hl hm hxl hlm hmx
    have e : ∀ z : ℝ, 0 < z → exp (2 * (log z / 2)) = z := fun z hz ↦ by
      rw [mul_div_cancel₀ _ two_ne_zero, exp_log hz]
    have i : ∀ z w : ℝ, 0 < z → 0 < w → z ≠ w → log z / 2 ≠ log w / 2 := fun z w hz hw hzw h ↦
      hzw (log_injOn_pos hz hw (by linarith))
    have h := H _ _ _ (i x l hx hl hxl) (i l m hl hm hlm) (i m x hm hx hmx)
    rw [deriv2_hypH h0 h1 h2 (i x l hx hl hxl) (i l m hl hm hlm) (i m x hm hx hmx), e x hx, e l hl,
      e m hm] at h
    by_contra hc
    push Not at hc
    have : 0 < ((2 * β - 1) ^ 2)⁻¹ * (hsDeriv2 (wydHs β) (x, l, m) * (2 * x) ^ 2) := by positivity
    linarith
  have key' : ∀ x l m : ℝ, 0 < x → 0 < l → 0 < m → hsDeriv2 (wydHs β) (x, l, m) ≤ 0 := by
    intro x l m hx hl hm
    have hp : ContinuousAt (fun t : ℝ ↦ ((x + t, l + 2 * t, m + 4 * t) : ℝ × ℝ × ℝ)) 0 := by fun_prop
    have hG : ContinuousAt (hsDeriv2 (wydHs β)) ((fun t : ℝ ↦
        ((x + t, l + 2 * t, m + 4 * t) : ℝ × ℝ × ℝ)) 0) := by
      refine C.continuousAt_hsDeriv2 ?_ ?_ ?_ <;> simpa
    have ht := (ContinuousAt.comp (f := fun t : ℝ ↦ ((x + t, l + 2 * t, m + 4 * t) : ℝ × ℝ × ℝ))
      (g := hsDeriv2 (wydHs β)) hG hp).tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    simp only [Function.comp_apply, add_zero, mul_zero] at ht
    refine le_of_tendsto ht ?_
    have hfin : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ∉ ({x - l, (l - m) / 2, (x - m) / 3} : Set ℝ) :=
      nhdsNE_le_cofinite 0 ((Set.toFinite _).eventually_cofinite_notMem)
    have p1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < x + t := eventually_nhdsWithin_of_eventually_nhds
      ((by fun_prop : ContinuousAt (fun t : ℝ ↦ x + t) 0).eventually (eventually_gt_nhds (by simpa)))
    have p2 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < l + 2 * t := eventually_nhdsWithin_of_eventually_nhds
      ((by fun_prop : ContinuousAt (fun t : ℝ ↦ l + 2 * t) 0).eventually
        (eventually_gt_nhds (by simpa)))
    have p3 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < m + 4 * t := eventually_nhdsWithin_of_eventually_nhds
      ((by fun_prop : ContinuousAt (fun t : ℝ ↦ m + 4 * t) 0).eventually
        (eventually_gt_nhds (by simpa)))
    filter_upwards [hfin, p1, p2, p3] with t h3 q1 q2 q3
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at h3
    refine key _ _ _ q1 q2 q3 (fun h ↦ h3.1 (by linarith)) (fun h ↦ h3.2.1 (by linarith))
      fun h ↦ h3.2.2 (by linarith)
  intro x y l m hx hxy hl hm
  have hanti : AntitoneOn (fun u ↦ hsDeriv (wydHs β) u l m) (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      (fun u hu ↦ (C.hasDerivAt_hsDeriv hu hl hm).continuousAt.continuousWithinAt)
      (fun u hu ↦ ?_) fun u hu ↦ ?_
    · rw [interior_Ioi] at hu
      exact (C.hasDerivAt_hsDeriv hu hl hm).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi] at hu
      rw [(C.hasDerivAt_hsDeriv hu hl hm).deriv]
      exact key' u l m hu hl hm
  have := hanti (mem_Ioi.2 hx) (mem_Ioi.2 (hx.trans hxy)) hxy.le
  simp only at this
  linarith

open scoped Matrix.Norms.L2Operator ComplexOrder in
open AlphaCurvature.Curvature AlphaCurvature.Quantum in
/-- **The strict form of Gibilisco–Isola's Conjecture 8.1, from two inequalities on an elementary
function**: let
`β ∈ [-1, 2] \ {0, ½, 1}`, `d = 2β - 1`, and suppose `H = hypH d` satisfies `HypCond64` and
`HypCond65`. Then the scalar curvature of the WYD metric strictly increases under mixing. -/
theorem wyd_curvature_lt_of_hyp (hm : -1 ≤ β) (hM : β ≤ 2) (h0 : β ≠ 0) (h1 : β ≠ 1)
    (h2 : 2 * β - 1 ≠ 0) (H64 : HypCond64 (2 * β - 1)) (H65 : HypCond65 (2 * β - 1))
    {d : Type*} [Fintype d] [DecidableEq d] {ρ σ : Matrix d d ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρt : ρ.trace = 1) (hσt : σ.trace = 1)
    (hmix : IsMajorizedBy (hρ.1.eigenvalues ∘ (Fintype.equivFin d).symm)
      (hσ.1.eigenvalues ∘ (Fintype.equivFin d).symm))
    (hne : ∀ τ : Equiv.Perm d, hρ.1.eigenvalues ∘ τ ≠ hσ.1.eigenvalues) :
    scalarCurvature (wydMetric β (tracelessHermitian d) σ) 0 <
      scalarCurvature (wydMetric β (tracelessHermitian d) ρ) 0 :=
  wyd_curvature_lt hm hM h0 h1 h2 (ineq64_of_hyp h0 h1 h2 H64) (ineq65_of_hyp h0 h1 h2 H65)
    hρ hσ hρt hσt hmix hne

end WYD

#print axioms WYD.wyd_curvature_lt_of_hyp
