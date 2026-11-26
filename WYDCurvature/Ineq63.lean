import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

open Filter Topology Set Real

namespace WYD63

/-- Barrier lemma: positive near `0⁺`, strictly increasing wherever it vanishes, hence `≥ 0`. -/
theorem barrier {f f' : ℝ → ℝ} (hf : ∀ s, 0 < s → HasDerivAt f (f' s) s)
    (h0 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < f s) (hb : ∀ s, 0 < s → f s = 0 → 0 < f' s)
    {s : ℝ} (hs : 0 < s) : 0 ≤ f s := by
  obtain ⟨a, ha, has, ha0⟩ : ∃ a, 0 < f a ∧ a < s ∧ 0 < a := by
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < s :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hs)
    obtain ⟨a, ⟨h2, h3⟩, h4⟩ := ((h0.and h1).and self_mem_nhdsWithin).exists
    exact ⟨a, h2, h3, h4⟩
  refine image_le_of_deriv_right_lt_deriv_boundary' (a := a) (b := s) (f := fun _ ↦ (0 : ℝ))
    (f' := fun _ ↦ 0) (B := f) (B' := f') continuousOn_const
    (fun x _ ↦ (hasDerivWithinAt_const _ _ _)) ha.le
    (fun x hx ↦ (hf x (ha0.trans_le hx.1)).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hf x (ha0.trans_le hx.1)).hasDerivWithinAt) ?_ ⟨has.le, le_rfl⟩
  intro x hx hx0
  exact hb x (ha0.trans_le hx.1) hx0.symm

/-- The data: `φ'' = D φ + sinh`, `φ(0) = φ'(0) = 0`, `D = d²`, `d ∈ [0, 3]`, and two positivity facts. -/
structure Data (d : ℝ) (φ φ₁ : ℝ → ℝ) : Prop where
  d0 : 0 ≤ d
  d3 : d ≤ 3
  h0 : ∀ s, HasDerivAt φ (φ₁ s) s
  h1 : ∀ s, HasDerivAt φ₁ (d ^ 2 * φ s + sinh s) s
  z0 : φ 0 = 0
  z1 : φ₁ 0 = 0
  pos : ∀ s, 0 < s → 0 < φ₁ s
  pos₂ : ∀ s, 0 < s → 0 < d ^ 2 * φ s + sinh s - φ s

variable {d : ℝ} {φ φ₁ : ℝ → ℝ}

/-- `φ₂ = φ''`. -/
noncomputable def phi2 (d : ℝ) (φ : ℝ → ℝ) (s : ℝ) : ℝ := d ^ 2 * φ s + sinh s
noncomputable def k (φ φ₁ : ℝ → ℝ) (s : ℝ) : ℝ := φ s / φ₁ s
noncomputable def S (d : ℝ) (φ φ₁ : ℝ → ℝ) (s : ℝ) : ℝ := phi2 d φ s / φ₁ s
noncomputable def v (d : ℝ) (φ φ₁ : ℝ → ℝ) (s : ℝ) : ℝ := 1 - k φ φ₁ s * S d φ φ₁ s
/-- `u = -k''`. -/
noncomputable def u (d : ℝ) (φ φ₁ : ℝ → ℝ) (s : ℝ) : ℝ :=
  v d φ φ₁ s * S d φ φ₁ s +
    k φ φ₁ s * ((1 + d ^ 2 - S d φ φ₁ s ^ 2 - d ^ 2 * k φ φ₁ s ^ 2) / 2)

namespace Data

variable (H : Data d φ φ₁)
include H

theorem cont0 : Continuous φ := continuous_iff_continuousAt.2 fun s ↦ (H.h0 s).continuousAt
theorem cont1 : Continuous φ₁ := continuous_iff_continuousAt.2 fun s ↦ (H.h1 s).continuousAt

omit H in
theorem mono_of_deriv {f f' : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (f' s) s) (hz : f 0 = 0)
    (hp : ∀ s, 0 < s → 0 < f' s) {s : ℝ} (hs : 0 < s) : 0 < f s := by
  have hm : StrictMonoOn f (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun x _ ↦ (hf x).continuousAt.continuousWithinAt) fun x hx ↦ ?_
    rw [interior_Ici] at hx
    rw [(hf x).deriv]; exact hp x hx
  have := hm self_mem_Ici (mem_Ici.2 hs.le) hs
  rwa [hz] at this

theorem phi_pos {s : ℝ} (hs : 0 < s) : 0 < φ s := mono_of_deriv H.h0 H.z0 H.pos hs

theorem phi2_pos {s : ℝ} (hs : 0 < s) : 0 < phi2 d φ s := by
  have := H.phi_pos hs; have := sinh_pos_iff.2 hs; unfold phi2; positivity

theorem h2 (s : ℝ) : HasDerivAt (phi2 d φ) (d ^ 2 * φ₁ s + cosh s) s :=
  ((H.h0 s).const_mul _).add (hasDerivAt_sinh s)

theorem z2 : phi2 d φ 0 = 0 := by simp [phi2, H.z0]

/-- First integral: `φ₂² - D φ₁² + φ₁² - D φ² = 2 φ₁ cosh`. -/
theorem integral (s : ℝ) : phi2 d φ s ^ 2 - d ^ 2 * φ₁ s ^ 2 + φ₁ s ^ 2 - d ^ 2 * φ s ^ 2
    = 2 * φ₁ s * cosh s := by
  have hd : ∀ t, HasDerivAt (fun t ↦ phi2 d φ t ^ 2 - d ^ 2 * φ₁ t ^ 2 + φ₁ t ^ 2 - d ^ 2 * φ t ^ 2
      - 2 * φ₁ t * cosh t) 0 t := by
    intro t
    have := ((((H.h2 t).pow 2).sub (((H.h1 t).pow 2).const_mul (d ^ 2))).add ((H.h1 t).pow 2)).sub
      (((H.h0 t).pow 2).const_mul (d ^ 2)) |>.sub (((H.h1 t).const_mul 2).mul (hasDerivAt_cosh t))
    refine this.congr_deriv ?_
    simp only [phi2]; push_cast; ring
  have hc := is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv) s 0
  simp only [H.z0, H.z1, H.z2] at hc
  linarith [hc]

theorem one_ne {s : ℝ} (hs : 0 < s) : φ₁ s ≠ 0 := (H.pos s hs).ne'

/-- `(S-1)² - D (1-k)² = 2 e^{-s}/φ₁` and `(S+1)² - D (1+k)² = 2 e^{s}/φ₁`. -/
theorem minus {s : ℝ} (hs : 0 < s) :
    (S d φ φ₁ s - 1) ^ 2 - d ^ 2 * (1 - k φ φ₁ s) ^ 2 = 2 * exp (-s) / φ₁ s := by
  have hne := H.one_ne hs; have hI := H.integral s
  have he : exp (-s) = cosh s - sinh s := by rw [cosh_sub_sinh]
  unfold S k; rw [he]; field_simp
  have : phi2 d φ s - d ^ 2 * φ s = sinh s := by simp [phi2]
  rw [← this]; linear_combination hI

theorem plus {s : ℝ} (hs : 0 < s) :
    (S d φ φ₁ s + 1) ^ 2 - d ^ 2 * (1 + k φ φ₁ s) ^ 2 = 2 * exp s / φ₁ s := by
  have hne := H.one_ne hs; have hI := H.integral s
  have he : exp s = cosh s + sinh s := by rw [cosh_add_sinh]
  unfold S k; rw [he]; field_simp
  have : phi2 d φ s - d ^ 2 * φ s = sinh s := by simp [phi2]
  rw [← this]; linear_combination hI

theorem hk {s : ℝ} (hs : 0 < s) : HasDerivAt (k φ φ₁) (v d φ φ₁ s) s := by
  have hne := H.one_ne hs
  refine ((H.h0 s).div (H.h1 s) hne).congr_deriv ?_
  unfold v k S phi2; field_simp

theorem hS {s : ℝ} (hs : 0 < s) : HasDerivAt (S d φ φ₁)
    ((1 + d ^ 2 - S d φ φ₁ s ^ 2 - d ^ 2 * k φ φ₁ s ^ 2) / 2) s := by
  have hne := H.one_ne hs; have hI := H.integral s
  refine ((H.h2 s).div (H.h1 s) hne).congr_deriv ?_
  have h3 : d ^ 2 * φ s + sinh s = phi2 d φ s := rfl
  rw [h3]; unfold k S; field_simp
  linear_combination (-1) * hI

theorem hv {s : ℝ} (hs : 0 < s) : HasDerivAt (v d φ φ₁) (-u d φ φ₁ s) s := by
  refine (((H.hk hs).mul (H.hS hs)).const_sub 1).congr_deriv ?_
  unfold u; ring

omit H in
theorem two_k_u (s : ℝ) : 2 * k φ φ₁ s * u d φ φ₁ s =
    4 * v d φ φ₁ s - 3 * v d φ φ₁ s ^ 2 - (1 - k φ φ₁ s ^ 2) * (1 - d ^ 2 * k φ φ₁ s ^ 2) := by
  unfold u v; ring

theorem hu {s : ℝ} (hs : 0 < s) : HasDerivAt (u d φ φ₁)
    (-2 * S d φ φ₁ s * u d φ φ₁ s + v d φ φ₁ s * (1 + d ^ 2 - 2 * d ^ 2 * k φ φ₁ s ^ 2)) s := by
  have hk := H.hk hs; have hS := H.hS hs; have hv := H.hv hs
  have := (hv.mul hS).add (hk.mul (((((hS.pow 2).const_sub (1 + d ^ 2))).sub
    ((hk.pow 2).const_mul (d ^ 2))).div_const 2))
  refine this.congr_deriv ?_
  simp only [u, v, Pi.pow_apply, Pi.sub_apply]; push_cast; ring

/-! ### Elementary positivity -/

theorem k_pos {s : ℝ} (hs : 0 < s) : 0 < k φ φ₁ s := div_pos (H.phi_pos hs) (H.pos s hs)
theorem S_pos {s : ℝ} (hs : 0 < s) : 0 < S d φ φ₁ s := div_pos (H.phi2_pos hs) (H.pos s hs)

theorem v_pos {s : ℝ} (hs : 0 < s) : 0 < v d φ φ₁ s := by
  -- `W = φ₁ sinh - φ cosh`, `W' = sinh (φ₂ - φ)`; `a = φ₁² - φ φ₂`, `a' = W`
  have hW : ∀ t, HasDerivAt (fun t ↦ φ₁ t * sinh t - φ t * cosh t)
      (sinh t * (d ^ 2 * φ t + sinh t - φ t)) t := fun t ↦
    (((H.h1 t).mul (hasDerivAt_sinh t)).sub ((H.h0 t).mul (hasDerivAt_cosh t))).congr_deriv (by ring)
  have hWp : ∀ t, 0 < t → 0 < φ₁ t * sinh t - φ t * cosh t := fun t ht ↦
    mono_of_deriv hW (by simp [H.z0, H.z1])
      (fun x hx ↦ mul_pos (sinh_pos_iff.2 hx) (H.pos₂ x hx)) ht
  have ha : ∀ t, HasDerivAt (fun t ↦ φ₁ t ^ 2 - φ t * phi2 d φ t)
      (φ₁ t * sinh t - φ t * cosh t) t := fun t ↦
    (((H.h1 t).pow 2).sub ((H.h0 t).mul (H.h2 t))).congr_deriv (by simp only [phi2]; push_cast; ring)
  have := mono_of_deriv ha (by simp [H.z0, H.z1]) hWp hs
  have hne := H.one_ne hs; have hp := H.pos s hs
  have : v d φ φ₁ s = (φ₁ s ^ 2 - φ s * phi2 d φ s) / φ₁ s ^ 2 := by
    unfold v k S; field_simp
  rw [this]; positivity

/-! ### Limits at `0⁺` -/

omit H in
theorem tend0 {f : ℝ → ℝ} (hf : ContinuousAt f 0) {a : ℝ} (h : f 0 = a) :
    Tendsto f (𝓝[>] 0) (𝓝 a) := h ▸ hf.tendsto.mono_left nhdsWithin_le_nhds

theorem lim_a : Tendsto (fun s ↦ φ₁ s / phi2 d φ s ^ 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have h3 : ContinuousAt (fun s ↦ 1 / (2 * (d ^ 2 * φ₁ s + cosh s))) 0 := by
    have : ContinuousAt (fun s ↦ 2 * (d ^ 2 * φ₁ s + cosh s)) 0 := by
      have := H.cont1; fun_prop
    exact continuousAt_const.div (f := fun _ ↦ (1 : ℝ)) (g := fun s ↦ 2 * (d ^ 2 * φ₁ s + cosh s))
      this (by simp [H.z1])
  refine HasDerivAt.lhopital_zero_right_on_Ioo (a := 0) (b := 1) one_pos
    (f' := fun s ↦ phi2 d φ s) (g' := fun s ↦ 2 * phi2 d φ s * (d ^ 2 * φ₁ s + cosh s))
    (fun x _ ↦ H.h1 x) (fun x _ ↦ ((H.h2 x).pow 2).congr_deriv (by push_cast; ring)) ?_ ?_ ?_ ?_
  · intro x hx
    have h1 := H.phi2_pos hx.1; have h2 := H.pos x hx.1; have h3 := cosh_pos x
    have : 0 < 2 * phi2 d φ x * (d ^ 2 * φ₁ x + cosh x) := by positivity
    exact this.ne'
  · exact tend0 H.cont1.continuousAt H.z1
  · exact tend0 (((H.h2 0).continuousAt).pow 2) (by simp [H.z2])
  · refine (tend0 h3 (a := 1 / 2) (by simp [H.z1])).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have h1 := H.phi2_pos hx; have h2 := H.pos x hx; have h3 := cosh_pos x
    have : 0 < d ^ 2 * φ₁ x + cosh x := by positivity
    field_simp

theorem lim_b : Tendsto (fun s ↦ φ s / (φ₁ s * phi2 d φ s)) (𝓝[>] 0) (𝓝 (1 / 3)) := by
  have hc3 : Tendsto (fun s ↦ d ^ 2 * φ₁ s + cosh s) (𝓝[>] 0) (𝓝 1) := by
    refine tend0 ?_ (by simp [H.z1])
    have := H.cont1; fun_prop
  refine HasDerivAt.lhopital_zero_right_on_Ioo (a := 0) (b := 1) one_pos
    (f' := φ₁) (g' := fun s ↦ phi2 d φ s ^ 2 + φ₁ s * (d ^ 2 * φ₁ s + cosh s))
    (fun x _ ↦ H.h0 x) (fun x _ ↦ ((H.h1 x).mul (H.h2 x)).congr_deriv (by simp only [phi2]; ring))
    ?_ ?_ ?_ ?_
  · intro x hx
    have h1 := H.phi2_pos hx.1; have h2 := H.pos x hx.1; have h3 := cosh_pos x
    have : 0 < phi2 d φ x ^ 2 + φ₁ x * (d ^ 2 * φ₁ x + cosh x) := by positivity
    exact this.ne'
  · exact tend0 H.cont0.continuousAt H.z0
  · exact tend0 (H.cont1.continuousAt.mul (H.h2 0).continuousAt) (by simp [H.z1])
  · have hl := H.lim_a.div ((tendsto_const_nhds (x := (1 : ℝ))).add (H.lim_a.mul hc3))
      (by norm_num)
    refine (hl.congr' ?_).trans (by norm_num)
    filter_upwards [self_mem_nhdsWithin] with x hx
    have h1 := H.phi2_pos hx; have h2 := H.pos x hx; have h3 := cosh_pos x
    have h4 : 0 < d ^ 2 * φ₁ x + cosh x := by positivity
    have h5 : phi2 d φ x ^ 2 + φ₁ x * (d ^ 2 * φ₁ x + cosh x) ≠ 0 := by positivity
    have h6 : 1 + φ₁ x / phi2 d φ x ^ 2 * (d ^ 2 * φ₁ x + cosh x) ≠ 0 := by positivity
    simp only [Pi.div_apply]
    field_simp

theorem lim_phi2 : Tendsto (phi2 d φ) (𝓝[>] 0) (𝓝 0) := tend0 (H.h2 0).continuousAt H.z2

theorem lim_k : Tendsto (k φ φ₁) (𝓝[>] 0) (𝓝 0) := by
  have := H.lim_b.mul H.lim_phi2
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have h1 := (H.phi2_pos hx).ne'; have h2 := H.one_ne hx
  unfold k; field_simp

theorem lim_v : Tendsto (v d φ φ₁) (𝓝[>] 0) (𝓝 (1 / 3)) := by
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub (H.lim_b.div H.lim_a (by norm_num))
  refine (this.congr' ?_).trans (by norm_num)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have h1 := (H.phi2_pos hx).ne'; have h2 := H.one_ne hx
  simp only [Pi.div_apply]
  unfold v k S; field_simp

theorem lim_iS : Tendsto (fun s ↦ φ₁ s / phi2 d φ s) (𝓝[>] 0) (𝓝 0) := by
  have := H.lim_a.mul H.lim_phi2
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have h1 := (H.phi2_pos hx).ne'
  field_simp

/-! ### `S > 1`, `k < 1`, `v < (1-k)(1-dk)` -/

theorem S_gt_one {s : ℝ} (hs : 0 < s) : 1 < S d φ φ₁ s := by
  have hne : ∀ t, 0 < t → S d φ φ₁ t - 1 ≠ 0 := by
    intro t ht h
    have h1 := H.minus ht; rw [h] at h1
    have h2 : 0 < 2 * exp (-t) / φ₁ t := by have := H.pos t ht; positivity
    nlinarith [sq_nonneg (d * (1 - k φ φ₁ t))]
  have hb := barrier (f := fun t ↦ S d φ φ₁ t - 1) (fun t ht ↦ (H.hS ht).sub_const 1) ?_
    (fun t ht h ↦ absurd h (hne t ht)) hs
  · exact lt_of_le_of_ne (by linarith) (fun h ↦ hne s hs (by rw [← h]; ring))
  · have h1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), φ₁ x / phi2 d φ x < 1 :=
      H.lim_iS.eventually (eventually_lt_nhds one_pos)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx hx0
    have hp := H.phi2_pos hx0; have hq := H.pos x hx0
    rw [div_lt_one hp] at hx
    have : 1 < S d φ φ₁ x := by unfold S; rwa [one_lt_div hq]
    linarith

theorem k_lt_one {s : ℝ} (hs : 0 < s) : k φ φ₁ s < 1 := by
  have h := mono_of_deriv (f := fun t ↦ φ₁ t - φ t)
    (f' := fun t ↦ d ^ 2 * φ t + sinh t - φ₁ t) (fun t ↦ (H.h1 t).sub (H.h0 t))
    (by simp [H.z0, H.z1]) (fun t ht ↦ ?_) hs
  · unfold k; rw [div_lt_one (H.pos s hs)]; linarith
  · have h1 := H.S_gt_one ht; unfold S at h1
    rw [one_lt_div (H.pos t ht)] at h1; unfold phi2 at h1; linarith

theorem v_lt {s : ℝ} (hs : 0 < s) :
    v d φ φ₁ s < (1 - k φ φ₁ s) * (1 - d * k φ φ₁ s) := by
  have h1 := H.minus hs; have hS := H.S_gt_one hs; have hk := H.k_lt_one hs; have hk0 := H.k_pos hs
  have h2 : 0 < 2 * exp (-s) / φ₁ s := by have := H.pos s hs; positivity
  have h3 : d * (1 - k φ φ₁ s) < S d φ φ₁ s - 1 := by
    refine lt_of_pow_lt_pow_left₀ 2 (by linarith) ?_
    rw [mul_pow]; linarith
  unfold v; nlinarith

theorem dk_lt_one {s : ℝ} (hs : 0 < s) : d * k φ φ₁ s < 1 := by
  have h1 := H.v_lt hs; have h2 := H.v_pos hs; have hk := H.k_lt_one hs
  by_contra h; push Not at h
  nlinarith

/-! ### `u ≥ 0`, `v ≤ 1/3` -/

theorem u_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ u d φ φ₁ s := by
  have hd : ∀ t, 0 < t → HasDerivAt (fun t ↦ u d φ φ₁ t * φ₁ t ^ 2)
      (φ₁ t ^ 2 * (v d φ φ₁ t * (1 + d ^ 2 - 2 * d ^ 2 * k φ φ₁ t ^ 2))) t := by
    intro t ht
    refine ((H.hu ht).mul ((H.h1 t).pow 2)).congr_deriv ?_
    have hne := H.one_ne ht
    have h3 : d ^ 2 * φ t + sinh t = S d φ φ₁ t * φ₁ t := by
      unfold S phi2; field_simp
    rw [h3]; simp only [Pi.pow_apply]; push_cast; ring
  have hnn : ∀ t, 0 < t →
      0 ≤ φ₁ t ^ 2 * (v d φ φ₁ t * (1 + d ^ 2 - 2 * d ^ 2 * k φ φ₁ t ^ 2)) := by
    intro t ht
    have h1 := H.k_lt_one ht; have h2 := H.dk_lt_one ht; have h3 := H.v_pos ht
    have h4 := H.k_pos ht; have h5 := H.d0
    have h6 : 0 ≤ d * k φ φ₁ t := by positivity
    have : 0 ≤ 1 + d ^ 2 - 2 * d ^ 2 * k φ φ₁ t ^ 2 := by
      nlinarith [mul_nonneg h6 h6, mul_nonneg h5 (mul_nonneg h5 h4.le), mul_nonneg h5 h5]
    positivity
  have hm : MonotoneOn (fun t ↦ u d φ φ₁ t * φ₁ t ^ 2) (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ ?_) fun x hx ↦ ?_
    · rw [interior_Ioi] at hx; exact (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi] at hx; rw [(hd x hx).deriv]; exact hnn x hx
  have hl : Tendsto (fun t ↦ u d φ φ₁ t * φ₁ t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have e1 := H.lim_k; have e2 := H.lim_phi2; have e3 := tend0 H.cont1.continuousAt H.z1
    have e4 := H.lim_v
    have := ((e4.mul (e3.mul e2)).add ((e1.mul ((((tendsto_const_nhds (x := 1 + d ^ 2)).mul
      (e3.pow 2)).sub (e2.pow 2)).sub (((e1.pow 2).const_mul (d ^ 2)).mul (e3.pow 2)))).div_const 2))
    refine (this.congr' ?_).trans (by norm_num)
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hne := H.one_ne hx
    have h3 : phi2 d φ x = S d φ φ₁ x * φ₁ x := by unfold S; field_simp
    rw [h3]; unfold u; ring
  have hle : (0 : ℝ) ≤ u d φ φ₁ s * φ₁ s ^ 2 := by
    refine le_of_tendsto hl ?_
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < s :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hs)
    filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
    exact hm ht0 hs ht.le
  have hp := H.pos s hs
  by_contra h; push Not at h
  nlinarith [mul_neg_of_neg_of_pos h (pow_pos hp 2)]

theorem v_le {s : ℝ} (hs : 0 < s) : v d φ φ₁ s ≤ 1 / 3 := by
  have hm : AntitoneOn (v d φ φ₁) (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      (fun x hx ↦ (H.hv hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ ?_) fun x hx ↦ ?_
    · rw [interior_Ioi] at hx; exact (H.hv hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi] at hx; rw [(H.hv hx).deriv]; linarith [H.u_nonneg hx]
  refine ge_of_tendsto H.lim_v ?_
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < s :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hs)
  filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
  exact hm ht0 hs ht.le

/-! ### The two barriers -/

theorem v_ge {s : ℝ} (hs : 0 < s) : (1 - 9 * k φ φ₁ s ^ 2) / 4 ≤ v d φ φ₁ s := by
  have hf : ∀ t, 0 < t → HasDerivAt (fun t ↦ v d φ φ₁ t - (1 - 9 * k φ φ₁ t ^ 2) / 4)
      (-u d φ φ₁ t + 9 / 2 * k φ φ₁ t * v d φ φ₁ t) t := fun t ht ↦
    ((H.hv ht).sub (((((H.hk ht).pow 2).const_mul 9).const_sub 1).div_const 4)).congr_deriv
      (by push_cast; ring)
  have h := barrier hf ?_ ?_ hs
  · linarith
  · have := H.lim_v.sub ((((H.lim_k.pow 2).const_mul 9).const_sub 1).div_const 4)
    refine this.eventually (eventually_gt_nhds (by norm_num))
  · intro t ht h0
    have hk0 := H.k_pos ht; have hk1 := H.k_lt_one ht; have hv := H.v_pos ht
    have h2 := two_k_u (d := d) (φ := φ) (φ₁ := φ₁) t
    have hv' : v d φ φ₁ t = (1 - 9 * k φ φ₁ t ^ 2) / 4 := by linarith
    have hd : d ^ 2 ≤ 9 := by have := H.d0; have := H.d3; nlinarith
    generalize k φ φ₁ t = κ at *; generalize u d φ φ₁ t = μ at *
    rw [hv'] at h2 hv ⊢
    have hκ : 9 * κ ^ 2 < 1 := by linarith
    have hX : (1 - κ ^ 2) * (1 - 9 * κ ^ 2) ≤ (1 - κ ^ 2) * (1 - d ^ 2 * κ ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (by nlinarith)
      nlinarith [sq_nonneg κ]
    have h3 : (1 - 9 * κ ^ 2) * (3 - 7 * κ ^ 2) / 16
        ≤ 2 * κ * (-μ + 9 / 2 * κ * ((1 - 9 * κ ^ 2) / 4)) := by nlinarith
    have h4 : 0 < (1 - 9 * κ ^ 2) * (3 - 7 * κ ^ 2) / 16 := by
      have : 0 < 1 - 9 * κ ^ 2 := by linarith
      have : 0 < 3 - 7 * κ ^ 2 := by nlinarith
      positivity
    have h5 := h4.trans_le h3
    exact (mul_pos_iff_of_pos_left (by positivity)).1 h5

theorem G_nonneg {s : ℝ} (hs : 0 < s) :
    (1 - k φ φ₁ s ^ 2) * (1 - d ^ 2 * k φ φ₁ s ^ 2) ≤
      2 * (1 + k φ φ₁ s) * v d φ φ₁ s + 6 * v d φ φ₁ s ^ 2 := by
  have hf : ∀ t, 0 < t → HasDerivAt (fun t ↦ 2 * (1 + k φ φ₁ t) * v d φ φ₁ t + 6 * v d φ φ₁ t ^ 2
        - (1 - k φ φ₁ t ^ 2) * (1 - d ^ 2 * k φ φ₁ t ^ 2))
      (2 * v d φ φ₁ t ^ 2 - 2 * (1 + k φ φ₁ t) * u d φ φ₁ t - 12 * v d φ φ₁ t * u d φ φ₁ t
        + 2 * k φ φ₁ t * v d φ φ₁ t * (1 + d ^ 2 - 2 * d ^ 2 * k φ φ₁ t ^ 2)) t := by
    intro t ht
    have hk := H.hk ht; have hv := H.hv ht
    have := (((hk.const_add 1).const_mul 2).mul hv).add ((hv.pow 2).const_mul 6) |>.sub
      ((((hk.pow 2)).const_sub 1).mul (((hk.pow 2).const_mul (d ^ 2)).const_sub 1))
    refine this.congr_deriv ?_
    simp only [Pi.pow_apply]; push_cast; ring
  have h := barrier hf ?_ ?_ hs
  · linarith
  · have := ((((H.lim_k.const_add 1).const_mul 2).mul H.lim_v).add ((H.lim_v.pow 2).const_mul 6)).sub
      (((H.lim_k.pow 2).const_sub 1).mul (((H.lim_k.pow 2).const_mul (d ^ 2)).const_sub 1))
    refine this.eventually (eventually_gt_nhds (by norm_num))
  · intro t ht h0
    have hk0 := H.k_pos ht; have hk1 := H.k_lt_one ht; have hv := H.v_pos ht
    have h2 := two_k_u (d := d) (φ := φ) (φ₁ := φ₁) t
    have hq := H.v_ge ht
    generalize k φ φ₁ t = κ at *; generalize u d φ φ₁ t = μ at *; generalize v d φ φ₁ t = ν at *
    have hb : 0 < -(1 - 3 * κ) * (7 - 5 * κ) * (1 + κ) + (42 - 30 * κ ^ 2) * ν := by
      rcases le_or_gt (1 / 3) κ with hκ | hκ
      · have h1 : 0 ≤ -(1 - 3 * κ) * (7 - 5 * κ) * (1 + κ) := by
          have : 0 ≤ -(1 - 3 * κ) := by linarith
          have : 0 ≤ 7 - 5 * κ := by linarith
          positivity
        have h3 : 0 < (42 - 30 * κ ^ 2) * ν := mul_pos (by nlinarith) hv
        linarith
      · have h1 : (42 - 30 * κ ^ 2) * ((1 - 9 * κ ^ 2) / 4) ≤ (42 - 30 * κ ^ 2) * ν :=
          mul_le_mul_of_nonneg_left hq (by nlinarith)
        have h3 : -(1 - 3 * κ) * (7 - 5 * κ) * (1 + κ) + (42 - 30 * κ ^ 2) * ((1 - 9 * κ ^ 2) / 4)
            = (1 - 3 * κ) * (7 + 59 * κ - 5 * κ ^ 2 - 45 * κ ^ 3) / 2 := by ring
        have h4 : 0 < (1 - 3 * κ) * (7 + 59 * κ - 5 * κ ^ 2 - 45 * κ ^ 3) / 2 := by
          have : 0 < 1 - 3 * κ := by linarith
          have : 0 < 7 + 59 * κ - 5 * κ ^ 2 - 45 * κ ^ 3 := by
            nlinarith [mul_pos hk0 hk0, mul_pos (mul_pos hk0 hk0) hk0,
              mul_pos hk0 (by linarith : 0 < 1 - 3 * κ),
              mul_pos (mul_pos hk0 hk0) (by linarith : 0 < 1 - 3 * κ)]
          positivity
        linarith
    have hid : κ * (1 - κ ^ 2) * (2 * ν ^ 2 - 2 * (1 + κ) * μ - 12 * ν * μ
        + 2 * κ * ν * (1 + d ^ 2 - 2 * d ^ 2 * κ ^ 2))
        = ν ^ 2 * (-(1 - 3 * κ) * (7 - 5 * κ) * (1 + κ) + (42 - 30 * κ ^ 2) * ν) := by
      linear_combination (-(1 - κ ^ 2) * (1 + κ + 6 * ν)) * h2
        - ((1 - κ ^ 2) * (1 + κ + 6 * ν) - 2 * ν * (1 - 2 * κ ^ 2)) * h0
    have hp : 0 < κ * (1 - κ ^ 2) := mul_pos hk0 (by nlinarith)
    have h5 : 0 < κ * (1 - κ ^ 2) * (2 * ν ^ 2 - 2 * (1 + κ) * μ - 12 * ν * μ
        + 2 * κ * ν * (1 + d ^ 2 - 2 * d ^ 2 * κ ^ 2)) := by rw [hid]; positivity
    exact (mul_pos_iff_of_pos_left hp).1 h5

/-! ### `u ≤ 2v` for `k > 1/3` -/

theorem C_nonneg {s : ℝ} (hs : 0 < s) (hk : 1 / 3 < k φ φ₁ s) :
    0 ≤ 3 * v d φ φ₁ s ^ 2 - 4 * (1 - k φ φ₁ s) * v d φ φ₁ s
      + (1 - k φ φ₁ s ^ 2) * (1 - d ^ 2 * k φ φ₁ s ^ 2) := by
  have hk1 := H.k_lt_one hs; have hv := H.v_pos hs; have hvl := H.v_lt hs
  have hdk := H.dk_lt_one hs; have hd0 := H.d0; have hd3 := H.d3; have hk0 := H.k_pos hs
  generalize k φ φ₁ s = κ at *; generalize v d φ φ₁ s = ν at *
  have hδ0 : 0 ≤ d * κ := by positivity
  rcases le_or_gt (1 / 3) (d * κ) with h | h
  · have h1 : 0 ≤ 1 - d + 2 * (d * κ) := by nlinarith
    have h2 : 3 * ν ^ 2 - 4 * (1 - κ) * ν + (1 - κ ^ 2) * (1 - d ^ 2 * κ ^ 2)
        = ((1 - κ) * (1 - d * κ) - ν) * (4 * (1 - κ) - 3 * (ν + (1 - κ) * (1 - d * κ)))
          + 2 * (1 - κ) * (1 - d * κ) * (κ * (1 - d + 2 * (d * κ))) := by ring
    rw [h2]
    have h3 : 0 ≤ (1 - κ) * (1 - d * κ) - ν := by linarith
    have h4 : 0 ≤ 4 * (1 - κ) - 3 * (ν + (1 - κ) * (1 - d * κ)) := by nlinarith
    have h5 : 0 ≤ 1 - κ := by linarith
    have h6 : 0 ≤ 1 - d * κ := by linarith
    positivity
  · have h1 : d ^ 2 * κ ^ 2 ≤ 1 / 9 := by
      have : d ^ 2 * κ ^ 2 = (d * κ) ^ 2 := by ring
      rw [this]; nlinarith
    have h2 : 3 * ν ^ 2 - 4 * (1 - κ) * ν + (1 - κ ^ 2) * (1 - d ^ 2 * κ ^ 2)
        = 3 * (ν - 2 / 3 * (1 - κ)) ^ 2
          + (1 - κ) * ((1 + κ) * (1 - d ^ 2 * κ ^ 2) - 4 / 3 * (1 - κ)) := by ring
    rw [h2]
    have h3 : 0 ≤ (1 + κ) * (1 - d ^ 2 * κ ^ 2) - 4 / 3 * (1 - κ) := by nlinarith
    have h4 : 0 ≤ 1 - κ := by linarith
    positivity

theorem u_le {s : ℝ} (hs : 0 < s) (hk : 1 / 3 < k φ φ₁ s) : u d φ φ₁ s ≤ 2 * v d φ φ₁ s := by
  have h := H.C_nonneg hs hk; have h2 := two_k_u (d := d) (φ := φ) (φ₁ := φ₁) s
  have hk0 := H.k_pos hs
  by_contra hc; push Not at hc
  nlinarith [mul_lt_mul_of_pos_left hc hk0]

/-! ### The main bound: `(1-k) v ≥ e^{-2s} (3k-1)(1+k)` for `k > 1/3` -/

theorem main_bound {s : ℝ} (hs : 0 < s) (hk : 1 / 3 < k φ φ₁ s) :
    exp (-2 * s) * ((3 * k φ φ₁ s - 1) * (1 + k φ φ₁ s)) ≤ (1 - k φ φ₁ s) * v d φ φ₁ s := by
  have hC := H.C_nonneg hs hk; have hG := H.G_nonneg hs
  have hk1 := H.k_lt_one hs; have hv := H.v_pos hs; have hvl := H.v_lt hs; have hv3 := H.v_le hs
  have hdk := H.dk_lt_one hs; have hd0 := H.d0; have hk0 := H.k_pos hs
  have hm := H.minus hs; have hp := H.plus hs; have hφ := H.pos s hs
  have hvS : v d φ φ₁ s = 1 - k φ φ₁ s * S d φ φ₁ s := rfl
  have hE : exp (-2 * s) * ((S d φ φ₁ s + 1) ^ 2 - d ^ 2 * (1 + k φ φ₁ s) ^ 2)
      = (S d φ φ₁ s - 1) ^ 2 - d ^ 2 * (1 - k φ φ₁ s) ^ 2 := by
    rw [hm, hp]
    have : exp (-s) = exp (-2 * s) * exp s := by rw [← exp_add]; ring_nf
    rw [this]; ring
  have hpp : 0 < (S d φ φ₁ s + 1) ^ 2 - d ^ 2 * (1 + k φ φ₁ s) ^ 2 := by
    rw [hp]; have := exp_pos s; positivity
  have hvk : v d φ φ₁ s ≤ 1 - k φ φ₁ s := by
    have : 0 ≤ d * k φ φ₁ s := by positivity
    nlinarith
  generalize k φ φ₁ s = κ at *; generalize v d φ φ₁ s = ν at *; generalize S d φ φ₁ s = σ at *
  generalize exp (-2 * s) = E at *
  -- the polynomial
  have hF : 0 ≤ (1 - κ) * ν * ((1 + κ - ν) ^ 2 - d ^ 2 * κ ^ 2 * (1 + κ) ^ 2)
      - (3 * κ - 1) * (1 + κ) * ((1 - κ - ν) ^ 2 - d ^ 2 * κ ^ 2 * (1 - κ) ^ 2) := by
    rcases le_or_gt 0 ((1 + κ) * ν - (3 * κ - 1) * (1 - κ)) with hA | hA
    · have hlow : 0 ≤ 2 * (3 * κ - 1) ^ 2 * (1 - κ) + 2 * κ * (5 - 7 * κ) * ν
          - (2 + 4 * κ) * ν ^ 2 := by
        rcases le_or_gt κ (1 / 2) with hh | hh
        · have e1 : 0 ≤ ν * (1 / 3 - ν) := mul_nonneg hv.le (by linarith)
          have e2 : 0 ≤ (1 / 3 - ν) * (2 * (3 * κ - 1) ^ 2 * (1 - κ)) :=
            mul_nonneg (by linarith) (mul_nonneg (by positivity) (by linarith))
          have e3 : 0 ≤ ν * (-18 * κ ^ 3 + 76 / 3 * κ ^ 2 - 100 / 9 * κ + 16 / 9) := by
            refine mul_nonneg hv.le ?_
            nlinarith [sq_nonneg (κ - 2 / 5), sq_nonneg (κ - 1 / 3),
              mul_nonneg (sub_nonneg.2 hk.le) (sub_nonneg.2 hh),
              mul_nonneg hk0.le (sq_nonneg (κ - 2 / 5))]
          have e4 : 0 ≤ (2 + 4 * κ) * (ν * (1 / 3 - ν)) := mul_nonneg (by linarith) e1
          nlinarith
        · have e1 : 0 ≤ ν * (1 - κ - ν) := mul_nonneg hv.le (by linarith)
          have e2 : 0 ≤ (2 + 4 * κ) * (ν * (1 - κ - ν)) := mul_nonneg (by linarith) e1
          have e3 : 2 * (3 * κ - 1) ^ 2 * (1 - κ) + 2 * κ * (5 - 7 * κ) * ν - (2 + 4 * κ) * ν ^ 2
              = 2 * (3 * κ - 1) ^ 2 * (1 - κ - ν) + ν * (4 * κ * (2 * κ - 1))
                + (2 + 4 * κ) * (ν * (1 - κ - ν)) := by ring
          rw [e3]
          have : 0 ≤ 1 - κ - ν := by linarith
          have : 0 ≤ 2 * κ - 1 := by linarith
          positivity
      have hid : (1 - κ) * ν * ((1 + κ - ν) ^ 2 - d ^ 2 * κ ^ 2 * (1 + κ) ^ 2)
          - (3 * κ - 1) * (1 + κ) * ((1 - κ - ν) ^ 2 - d ^ 2 * κ ^ 2 * (1 - κ) ^ 2)
          = ((1 + κ) * ν - (3 * κ - 1) * (1 - κ)) * (3 * ν ^ 2 - 4 * (1 - κ) * ν
              + (1 - κ ^ 2) * (1 - d ^ 2 * κ ^ 2))
            + ν * (2 * (3 * κ - 1) ^ 2 * (1 - κ) + 2 * κ * (5 - 7 * κ) * ν
              - (2 + 4 * κ) * ν ^ 2) := by ring
      rw [hid]; positivity
    · have hup : 0 ≤ 7 - 22 * κ + 19 * κ ^ 2 + (7 + 5 * κ) * ν := by
        have : 0 ≤ (7 + 5 * κ) * ν := by positivity
        nlinarith [sq_nonneg (19 * κ - 11)]
      have hid : (1 - κ) * ν * ((1 + κ - ν) ^ 2 - d ^ 2 * κ ^ 2 * (1 + κ) ^ 2)
          - (3 * κ - 1) * (1 + κ) * ((1 - κ - ν) ^ 2 - d ^ 2 * κ ^ 2 * (1 - κ) ^ 2)
          = -((1 + κ) * ν - (3 * κ - 1) * (1 - κ)) * (2 * (1 + κ) * ν + 6 * ν ^ 2
              - (1 - κ ^ 2) * (1 - d ^ 2 * κ ^ 2))
            + ν ^ 2 * (7 - 22 * κ + 19 * κ ^ 2 + (7 + 5 * κ) * ν) := by ring
      rw [hid]
      have h1 : 0 ≤ -((1 + κ) * ν - (3 * κ - 1) * (1 - κ)) := by linarith
      have h2 : 0 ≤ 2 * (1 + κ) * ν + 6 * ν ^ 2 - (1 - κ ^ 2) * (1 - d ^ 2 * κ ^ 2) := by linarith
      positivity
  have hF2 : 0 ≤ ((σ + 1) ^ 2 - d ^ 2 * (1 + κ) ^ 2)
      * ((1 - κ) * ν - E * ((3 * κ - 1) * (1 + κ))) := by
    have e : κ ^ 2 * (((σ + 1) ^ 2 - d ^ 2 * (1 + κ) ^ 2)
        * ((1 - κ) * ν - E * ((3 * κ - 1) * (1 + κ))))
        = (1 - κ) * ν * ((1 + κ - ν) ^ 2 - d ^ 2 * κ ^ 2 * (1 + κ) ^ 2)
      - (3 * κ - 1) * (1 + κ) * ((1 - κ - ν) ^ 2 - d ^ 2 * κ ^ 2 * (1 - κ) ^ 2) := by
      have : κ ^ 2 * (((σ + 1) ^ 2 - d ^ 2 * (1 + κ) ^ 2)
        * ((1 - κ) * ν - E * ((3 * κ - 1) * (1 + κ))))
        = κ ^ 2 * ((1 - κ) * ν * ((σ + 1) ^ 2 - d ^ 2 * (1 + κ) ^ 2)
          - (3 * κ - 1) * (1 + κ) * (E * ((σ + 1) ^ 2 - d ^ 2 * (1 + κ) ^ 2))) := by ring
      rw [this, hE, hvS]; ring
    rw [← e] at hF
    exact nonneg_of_mul_nonneg_right hF (by positivity)
  have := nonneg_of_mul_nonneg_right hF2 hpp
  linarith

/-! ### The two sides of (63) -/

theorem left_pos {s : ℝ} (hs : 0 < s) :
    0 < 8 * (1 - k φ φ₁ s) * v d φ φ₁ s + 4 * v d φ φ₁ s ^ 2 + 4 * (1 - k φ φ₁ s) * u d φ φ₁ s
      + exp (-2 * s) * (8 * (1 - 3 * k φ φ₁ s) * (1 + k φ φ₁ s)
        + 12 * (3 * k φ φ₁ s + 1) * v d φ φ₁ s + 2 * (3 * k φ φ₁ s + 1) * u d φ φ₁ s
        - 6 * v d φ φ₁ s ^ 2) := by
  have hk1 := H.k_lt_one hs; have hv := H.v_pos hs; have hv3 := H.v_le hs; have hk0 := H.k_pos hs
  have hu := H.u_nonneg hs; have hmb := H.main_bound hs
  have hE := exp_pos (-2 * s)
  generalize k φ φ₁ s = κ at *; generalize v d φ φ₁ s = ν at *; generalize u d φ φ₁ s = μ at *
  generalize exp (-2 * s) = E at *
  have h1 : 0 ≤ 1 - κ := by linarith
  have e0 : 0 ≤ 8 * (1 - κ) * ν + E * (8 * (1 - 3 * κ) * (1 + κ)) := by
    rcases le_or_gt κ (1 / 3) with h | h
    · have : 0 ≤ 1 - 3 * κ := by linarith
      positivity
    · nlinarith [hmb h]
  have e1 : 0 ≤ E * (12 * (3 * κ + 1) * ν - 6 * ν ^ 2) := by
    refine mul_nonneg hE.le ?_
    nlinarith [mul_pos hk0 hv]
  have e2 : 0 ≤ 4 * (1 - κ) * μ + E * (2 * (3 * κ + 1) * μ) := by positivity
  have e3 : 0 < 4 * ν ^ 2 := by positivity
  nlinarith

theorem right_pos {s : ℝ} (hs : 0 < s) :
    0 < 8 * (3 * k φ φ₁ s + 1) * (1 - k φ φ₁ s) + 12 * (1 - 3 * k φ φ₁ s) * v d φ φ₁ s
      - 6 * v d φ φ₁ s ^ 2 - 2 * (1 - 3 * k φ φ₁ s) * u d φ φ₁ s
      + exp (-2 * s) * (8 * (k φ φ₁ s + 1) * v d φ φ₁ s + 4 * v d φ φ₁ s ^ 2
        - 4 * (k φ φ₁ s + 1) * u d φ φ₁ s) := by
  have hk1 := H.k_lt_one hs; have hv := H.v_pos hs; have hv3 := H.v_le hs; have hk0 := H.k_pos hs
  have hu := H.u_nonneg hs; have hul := H.u_le hs; have hvl := H.v_lt hs
  have h2 := two_k_u (d := d) (φ := φ) (φ₁ := φ₁) s
  have hdk := H.dk_lt_one hs; have hd0 := H.d0; have hd3 := H.d3
  have hE := exp_pos (-2 * s)
  have hE1 : exp (-2 * s) ≤ 1 := by rw [exp_le_one_iff]; linarith
  have hvk : v d φ φ₁ s ≤ 1 - k φ φ₁ s := by
    have : 0 ≤ d * k φ φ₁ s := by positivity
    nlinarith
  generalize k φ φ₁ s = κ at *; generalize v d φ φ₁ s = ν at *; generalize u d φ φ₁ s = μ at *
  generalize exp (-2 * s) = E at *
  rcases le_or_gt κ (1 / 3) with h | h
  · -- `u ≤ κ (10 - 9 κ²)/2`
    have hd9 : d ^ 2 ≤ 9 := by nlinarith
    have hμ : μ ≤ κ * (10 - 9 * κ ^ 2) / 2 := by
      have e1 : 2 * κ * μ ≤ κ ^ 2 * (10 - 9 * κ ^ 2) := by
        have : 2 * κ * μ = (1 - ν) * (3 * ν - 1) + κ ^ 2 * (1 + d ^ 2 * (1 - κ ^ 2)) := by
          rw [h2]; ring
        rw [this]
        have e2 : (1 - ν) * (3 * ν - 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        have e3 : d ^ 2 * (1 - κ ^ 2) ≤ 9 * (1 - κ ^ 2) :=
          mul_le_mul_of_nonneg_right hd9 (by nlinarith)
        nlinarith [mul_le_mul_of_nonneg_left e3 (sq_nonneg κ)]
      by_contra hc; push Not at hc
      nlinarith [mul_lt_mul_of_pos_left hc hk0]
    have f0 : 0 < 8 * (3 * κ + 1) * (1 - κ) - 6 * ν ^ 2 - 2 * (1 - 3 * κ) * μ := by
      have e1 : 2 * (1 - 3 * κ) * μ ≤ 2 * (1 - 3 * κ) * (κ * (10 - 9 * κ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hμ (by linarith)
      have e2 : 6 * ν ^ 2 ≤ 2 / 3 := by nlinarith
      nlinarith [mul_pos hk0 hk0, mul_pos (mul_pos hk0 hk0) hk0,
        mul_nonneg hk0.le (by linarith : 0 ≤ 1 - 3 * κ),
        mul_nonneg (mul_pos hk0 hk0).le (by linarith : 0 ≤ 1 - 3 * κ)]
    have f1 : 0 < 8 * (3 * κ + 1) * (1 - κ) - 2 * ν ^ 2 + 8 * (κ + 1) * ν
        - 2 * (1 - 3 * κ) * μ - 4 * (κ + 1) * μ := by
      have e1 : (6 - 2 * κ) * μ ≤ (6 - 2 * κ) * (κ * (10 - 9 * κ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hμ (by linarith)
      have e2 : 0 ≤ 8 * (κ + 1) * ν - 2 * ν ^ 2 := by nlinarith [mul_pos hk0 hv]
      nlinarith [mul_pos hk0 hk0, mul_pos (mul_pos hk0 hk0) hk0,
        mul_nonneg hk0.le (by linarith : 0 ≤ 1 - 3 * κ),
        mul_nonneg (mul_pos hk0 hk0).le (by linarith : 0 ≤ 1 - 3 * κ)]
    have f2 : 0 ≤ 12 * (1 - 3 * κ) * ν := by
      have : 0 ≤ 1 - 3 * κ := by linarith
      positivity
    nlinarith [mul_nonneg (sub_nonneg.2 hE1) f0.le, mul_pos hE f1]
  · have hul := hul h
    have f1 : 0 ≤ E * (8 * (κ + 1) * ν + 4 * ν ^ 2 - 4 * (κ + 1) * μ) := by
      refine mul_nonneg hE.le ?_
      nlinarith [mul_le_mul_of_nonneg_left hul (by linarith : 0 ≤ κ + 1), sq_nonneg ν]
    have f2 : 0 ≤ 2 * (3 * κ - 1) * μ := by
      have : 0 ≤ 3 * κ - 1 := by linarith
      positivity
    have f3 : 12 * (3 * κ - 1) * ν ≤ 12 * (3 * κ - 1) * (1 - κ) :=
      mul_le_mul_of_nonneg_left hvk (by linarith)
    have f4 : 6 * ν ^ 2 ≤ 6 * (1 - κ) ^ 2 := by nlinarith
    have f5 : 0 < (1 - κ) * (14 - 6 * κ) := mul_pos (by linarith) (by linarith)
    nlinarith

end Data

/-! ### The target of (63) -/

/-- `2ψ' + ψ''` for `ψ = e^{2s}(K-1)(3K+1) - 2(K+1)²`, in terms of `E = e^{2s}, K, K', K''`. -/
def T (E K K₁ K₂ : ℝ) : ℝ :=
  8 * E * (3 * K ^ 2 - 2 * K - 1) + 6 * E * (6 * K - 2) * K₁ + E * (6 * K - 2) * K₂
    + 6 * E * K₁ ^ 2 - 8 * (K + 1) * K₁ - 4 * K₁ ^ 2 - 4 * (K + 1) * K₂

theorem Data.T_right (H : Data d φ φ₁) {s : ℝ} (hs : 0 < s) :
    T (exp (2 * s)) (k φ φ₁ s) (v d φ φ₁ s) (-u d φ φ₁ s) < 0 := by
  have h := H.right_pos hs
  have he : exp (2 * s) * exp (-2 * s) = 1 := by rw [← exp_add]; simp
  have hE := exp_pos (2 * s)
  have := mul_pos hE h
  unfold T
  generalize k φ φ₁ s = κ at *; generalize v d φ φ₁ s = ν at *; generalize u d φ φ₁ s = μ at *
  have e : exp (2 * s) * (8 * (3 * κ + 1) * (1 - κ) + 12 * (1 - 3 * κ) * ν - 6 * ν ^ 2
      - 2 * (1 - 3 * κ) * μ + exp (-2 * s) * (8 * (κ + 1) * ν + 4 * ν ^ 2 - 4 * (κ + 1) * μ))
      = exp (2 * s) * (8 * (3 * κ + 1) * (1 - κ) + 12 * (1 - 3 * κ) * ν - 6 * ν ^ 2
      - 2 * (1 - 3 * κ) * μ) + (8 * (κ + 1) * ν + 4 * ν ^ 2 - 4 * (κ + 1) * μ) := by
    linear_combination (8 * (κ + 1) * ν + 4 * ν ^ 2 - 4 * (κ + 1) * μ) * he
  rw [e] at this
  linarith

theorem Data.T_left (H : Data d φ φ₁) {s : ℝ} (hs : 0 < s) :
    T (exp (-2 * s)) (-k φ φ₁ s) (v d φ φ₁ s) (u d φ φ₁ s) < 0 := by
  have h := H.left_pos hs
  unfold T; linarith

/-! ### From the data to `(e^{2s} ψ')' < 0` on `ℝ` -/

/-- `K(s) = φ(s)/φ'(s)`, `ψ = e^{2s}(K-1)(3K+1) - 2(K+1)²`. -/
noncomputable def psi (K : ℝ → ℝ) (s : ℝ) : ℝ :=
  exp (2 * s) * (K s - 1) * (3 * K s + 1) - 2 * (K s + 1) ^ 2

/-- The derivative of `K`, extended to all of `ℝ`. -/
noncomputable def w (d : ℝ) (φ φ₁ : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s = 0 then 1 / 3 else v d φ φ₁ |s|

theorem Data.odd_phi (H : Data d φ φ₁) (hodd : ∀ s, φ (-s) = -φ s) (s : ℝ) : φ₁ (-s) = φ₁ s := by
  have h1 : HasDerivAt (fun t ↦ φ (-t)) (φ₁ (-s) * -1) s :=
    (H.h0 (-s)).comp s (hasDerivAt_neg s)
  have h2 : HasDerivAt (fun t ↦ φ (-t)) (-φ₁ s) s := by
    have : (fun t ↦ φ (-t)) = fun t ↦ -φ t := funext hodd
    rw [this]; exact (H.h0 s).neg
  linarith [h1.unique h2]

theorem Data.strictAnti (H : Data d φ φ₁) (hodd : ∀ s, φ (-s) = -φ s) :
    StrictAnti fun s ↦ exp (2 * s) * deriv (psi (fun s ↦ φ s / φ₁ s)) s := by
  set K : ℝ → ℝ := fun s ↦ φ s / φ₁ s with hKdef
  have hKk : ∀ s, K s = k φ φ₁ s := fun _ ↦ rfl
  have hKodd : ∀ s, K (-s) = -K s := by
    intro s; simp only [hKdef, hodd, H.odd_phi hodd, neg_div]
  have hK0 : K 0 = 0 := by simp [hKdef, H.z0]
  -- derivative of `K` off `0`
  have hKd : ∀ s, s ≠ 0 → HasDerivAt K (w d φ φ₁ s) s := by
    intro s hs
    rcases lt_or_gt_of_ne hs with h | h
    · have h1 := H.hk (neg_pos.2 h)
      have h2 : HasDerivAt (fun t ↦ -(k φ φ₁ (-t))) (-(v d φ φ₁ (-s) * -1)) s :=
        (h1.comp s (hasDerivAt_neg s)).neg
      have h3 : (fun t ↦ -(k φ φ₁ (-t))) = K := by
        funext t; rw [← hKk, hKodd]; ring
      rw [h3] at h2
      simpa [w, hs, abs_of_neg h] using h2
    · have h1 : HasDerivAt K (v d φ φ₁ s) s := H.hk h
      simpa [w, hs, abs_of_pos h] using h1
  have habs : Tendsto (fun s : ℝ ↦ |s|) (𝓝[≠] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ ↦ |s|) (𝓝 0) (𝓝 |0|) := continuous_abs.tendsto 0
      rw [abs_zero] at this; exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs using abs_pos.2 hs
  have hKc : ContinuousAt K 0 := by
    rw [continuousAt_iff_punctured_nhds, hK0]
    have h1 := (H.lim_k.comp habs)
    refine squeeze_zero_norm' (a := fun s ↦ k φ φ₁ |s|) ?_ h1
    refine Eventually.of_forall fun s ↦ ?_
    rcases le_total 0 s with h | h
    · rw [abs_of_nonneg h, hKk, Real.norm_eq_abs]
      rcases h.eq_or_lt with h0 | h0
      · rw [← h0]; simp [k, H.z0]
      · rw [abs_of_pos (H.k_pos h0)]
    · rw [abs_of_nonpos h, ← hKk, hKodd, Real.norm_eq_abs]
      rcases h.eq_or_lt with h0 | h0
      · rw [h0, hK0]; simp
      · have := H.k_pos (neg_pos.2 h0)
        rw [← hKk, hKodd] at this
        rw [abs_of_neg (by linarith)]
  have hwc : ContinuousAt (w d φ φ₁) 0 := by
    rw [continuousAt_iff_punctured_nhds]
    have h1 := H.lim_v.comp habs
    have h2 : w d φ φ₁ 0 = 1 / 3 := by simp [w]
    rw [h2]
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have : s ≠ 0 := hs
    simp [w, this]
  have hKd0 : HasDerivAt K (w d φ φ₁ 0) 0 :=
    hasDerivAt_of_hasDerivAt_of_ne (fun y hy ↦ hKd y hy) hKc hwc
  have hKall : ∀ s, HasDerivAt K (w d φ φ₁ s) s := fun s ↦ by
    rcases eq_or_ne s 0 with rfl | h
    · exact hKd0
    · exact hKd s h
  -- derivative of `ψ`
  have hψ : ∀ s, deriv (psi K) s = exp (2 * s) * (2 * (K s - 1) * (3 * K s + 1)
      + (6 * K s - 2) * w d φ φ₁ s) - 4 * (K s + 1) * w d φ φ₁ s := by
    intro s
    have hE : HasDerivAt (fun s : ℝ ↦ exp (2 * s)) (exp (2 * s) * 2) s := by
      simpa using ((hasDerivAt_id s).const_mul 2).exp
    have := ((hE.mul ((hKall s).sub_const 1)).mul (((hKall s).const_mul 3).add_const 1)).sub
      ((((hKall s).add_const 1).pow 2).const_mul 2)
    have h2 := this.deriv
    have h3 : psi K = ((fun s : ℝ ↦ exp (2 * s)) * fun x ↦ K x - 1) * (fun x ↦ 3 * K x + 1)
        - fun y ↦ 2 * ((fun x ↦ K x + 1) ^ 2) y := by
      funext x; simp [psi]
    rw [h3, h2]; simp; ring
  set W : ℝ → ℝ := fun s ↦ exp (2 * s) * (exp (2 * s) * (2 * (K s - 1) * (3 * K s + 1)
      + (6 * K s - 2) * w d φ φ₁ s) - 4 * (K s + 1) * w d φ φ₁ s) with hW
  have hWeq : (fun s ↦ exp (2 * s) * deriv (psi K) s) = W := by funext s; rw [hψ]
  rw [hWeq]
  -- `K''`
  set K₂ : ℝ → ℝ := fun s ↦ if 0 < s then -u d φ φ₁ s else u d φ φ₁ (-s) with hK2
  have hwd : ∀ s, s ≠ 0 → HasDerivAt (w d φ φ₁) (K₂ s) s := by
    intro s hs
    rcases lt_or_gt_of_ne hs with h | h
    · have h1 : HasDerivAt (fun t ↦ v d φ φ₁ (-t)) (-u d φ φ₁ (-s) * -1) s :=
        (H.hv (neg_pos.2 h)).comp s (hasDerivAt_neg s)
      have h2 : w d φ φ₁ =ᶠ[𝓝 s] fun t ↦ v d φ φ₁ (-t) := by
        filter_upwards [eventually_lt_nhds h] with t ht
        simp [w, ht.ne, abs_of_neg ht]
      refine (h1.congr_of_eventuallyEq h2).congr_deriv ?_
      simp [hK2, h.not_gt]
    · have h2 : w d φ φ₁ =ᶠ[𝓝 s] v d φ φ₁ := by
        filter_upwards [eventually_gt_nhds h] with t ht
        simp [w, ht.ne', abs_of_pos ht]
      refine ((H.hv h).congr_of_eventuallyEq h2).congr_deriv ?_
      simp [hK2, h]
  have hwcont : Continuous (w d φ φ₁) := continuous_iff_continuousAt.2 fun s ↦ by
    rcases eq_or_ne s 0 with rfl | h
    · exact hwc
    · exact (hwd s h).continuousAt
  have hKcont : Continuous K := continuous_iff_continuousAt.2 fun s ↦ (hKall s).continuousAt
  have hWc : Continuous W := by simp only [hW]; fun_prop
  have hWd : ∀ s, s ≠ 0 → HasDerivAt W (exp (2 * s) * T (exp (2 * s)) (K s) (w d φ φ₁ s) (K₂ s)) s := by
    intro s hs
    have hE : HasDerivAt (fun s : ℝ ↦ exp (2 * s)) (exp (2 * s) * 2) s := by
      simpa using ((hasDerivAt_id s).const_mul 2).exp
    have a := hKall s; have b := hwd s hs
    have := hE.mul ((hE.mul ((((a.sub_const 1).const_mul 2).mul ((a.const_mul 3).add_const 1)).add
      (((a.const_mul 6).sub_const 2).mul b))).sub (((a.add_const 1).const_mul 4).mul b))
    refine this.congr_deriv ?_
    simp only [T, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]; ring
  have hneg : ∀ s, s ≠ 0 → deriv W s < 0 := by
    intro s hs
    rw [(hWd s hs).deriv]
    refine mul_neg_of_pos_of_neg (exp_pos _) ?_
    rcases lt_or_gt_of_ne hs with h | h
    · have h1 := H.T_left (neg_pos.2 h)
      have e1 : K s = -k φ φ₁ (-s) := by rw [← hKk, hKodd]; ring
      have e2 : w d φ φ₁ s = v d φ φ₁ (-s) := by simp [w, hs, abs_of_neg h]
      have e3 : K₂ s = u d φ φ₁ (-s) := by simp [hK2, h.not_gt]
      rw [e1, e2, e3]
      have e4 : exp (2 * s) = exp (-2 * -s) := by ring_nf
      rw [e4]; exact h1
    · have h1 := H.T_right h
      have e2 : w d φ φ₁ s = v d φ φ₁ s := by simp [w, hs, abs_of_pos h]
      have e3 : K₂ s = -u d φ φ₁ s := by simp [hK2, h]
      rw [hKk, e2, e3]; exact h1
  have hL : StrictAntiOn W (Iic 0) := strictAntiOn_of_deriv_neg (convex_Iic 0) hWc.continuousOn
    fun x hx ↦ by rw [interior_Iic] at hx; exact hneg x hx.ne
  have hR : StrictAntiOn W (Ici 0) := strictAntiOn_of_deriv_neg (convex_Ici 0) hWc.continuousOn
    fun x hx ↦ by rw [interior_Ici] at hx; exact hneg x (ne_of_gt hx)
  exact hL.Iic_union_Ici hR

/-! ### The concrete functions -/

/-- `φ(s) = (sinh s - sinh(ds)/d)/(1 - d²)` satisfies the hypotheses, `0 < d ≤ 3`, `d ≠ 1`. -/
theorem data_of_ne_one {d : ℝ} (h0 : 0 < d) (h3 : d ≤ 3) (h1 : d ≠ 1) :
    Data d (fun s ↦ (sinh s - sinh (d * s) / d) / (1 - d ^ 2))
      (fun s ↦ (cosh s - cosh (d * s)) / (1 - d ^ 2)) := by
  have hne : 1 - d ^ 2 ≠ 0 := by
    intro h; apply h1; nlinarith [mul_self_nonneg (d - 1)]
  have hds : ∀ s, HasDerivAt (fun s : ℝ ↦ d * s) d s := fun s ↦ by
    simpa using (hasDerivAt_id s).const_mul d
  refine ⟨h0.le, h3, fun s ↦ ?_, fun s ↦ ?_, by simp, by simp, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · refine (((hasDerivAt_sinh s).sub (((hds s).sinh).div_const d)).div_const _).congr_deriv ?_
    field_simp
  · refine (((hasDerivAt_cosh s).sub ((hds s).cosh)).div_const _).congr_deriv ?_
    field_simp; ring
  · rcases lt_or_gt_of_ne h1 with h | h
    · have hc : cosh (d * s) < cosh s := by
        rw [cosh_lt_cosh, abs_of_pos (by positivity), abs_of_pos hs]; nlinarith
      exact div_pos (by linarith) (by nlinarith)
    · have hc : cosh s < cosh (d * s) := by
        rw [cosh_lt_cosh, abs_of_pos (by positivity : 0 < d * s), abs_of_pos hs]; nlinarith
      exact div_pos_of_neg_of_neg (by linarith) (by nlinarith)
  · have : d ^ 2 * ((sinh s - sinh (d * s) / d) / (1 - d ^ 2)) + sinh s
        - (sinh s - sinh (d * s) / d) / (1 - d ^ 2) = sinh (d * s) / d := by
      field_simp; ring
    rw [this]
    exact div_pos (sinh_pos_iff.2 (by positivity)) h0

/-- The case `d = 1` (Kubo–Mori): `φ(s) = (s cosh s - sinh s)/2`. -/
theorem data_one : Data 1 (fun s ↦ (s * cosh s - sinh s) / 2) (fun s ↦ s * sinh s / 2) := by
  refine ⟨zero_le_one, by norm_num, fun s ↦ ?_, fun s ↦ ?_, by simp, by simp, fun s hs ↦ ?_,
    fun s hs ↦ ?_⟩
  · refine ((((hasDerivAt_id s).mul (hasDerivAt_cosh s)).sub (hasDerivAt_sinh s)).div_const 2).congr_deriv ?_
    simp
  · refine (((hasDerivAt_id s).mul (hasDerivAt_sinh s)).div_const 2).congr_deriv ?_
    simp; ring
  · have := sinh_pos_iff.2 hs; positivity
  · have := sinh_pos_iff.2 hs; linarith

/-- The qubit kernel of the WYD metric with `d = 2β - 1`. -/
noncomputable def qubitK (d s : ℝ) : ℝ :=
  (d * sinh s - sinh (d * s)) / (d * (cosh s - cosh (d * s)))

/-- **Dittmann's inequality (63) for the WYD metrics**, in the one-variable form
`(e^{2s} ψ'(s))' < 0` for every `s`: for `d = 2β - 1`, `0 < d ≤ 3`, `d ≠ 1`, the function
`e^{2s} ψ'` is strictly decreasing on `ℝ`, with `ψ = e^{2s}(K-1)(3K+1) - 2(K+1)²`. -/
theorem wyd_ineq63 {d : ℝ} (h0 : 0 < d) (h3 : d ≤ 3) (h1 : d ≠ 1) :
    StrictAnti fun s ↦ exp (2 * s) * deriv (psi (qubitK d)) s := by
  have hne : 1 - d ^ 2 ≠ 0 := by
    intro h; apply h1; nlinarith [mul_self_nonneg (d - 1)]
  have hK : qubitK d = fun s ↦ (sinh s - sinh (d * s) / d) / (1 - d ^ 2)
      / ((cosh s - cosh (d * s)) / (1 - d ^ 2)) := by
    funext s
    unfold qubitK
    rw [div_div_div_cancel_right₀ hne]
    rw [show sinh s - sinh (d * s) / d = (d * sinh s - sinh (d * s)) / d by field_simp, div_div]
  rw [hK]
  exact (data_of_ne_one h0 h3 h1).strictAnti fun s ↦ by simp [mul_neg, sinh_neg]; ring

/-- The Kubo–Mori case `d = 1`, `K = coth s - 1/s`. -/
theorem bkm_ineq63 : StrictAnti fun s ↦
    exp (2 * s) * deriv (psi fun s ↦ (s * cosh s - sinh s) / 2 / (s * sinh s / 2)) s :=
  data_one.strictAnti fun s ↦ by simp; ring

end WYD63

