import WYDCurvature.OpMono
import WYDCurvature.Literal

/-!
# Gibilisco–Isola Theorem 6.1

`f_p` (Definition 6.1, `WYD.Literal.fGI`) is operator monotone iff `p ∈ (-∞, -1] ∪ [1/2, ∞)`
(Hasegawa; Hasegawa–Petz).

*If.* With `a_s(x) = 1 - s + s x` and `L r x = ∫₀¹ a_s(x)^{r-1} ds`,
* for `p ≥ 1`, `β = 1/p ∈ (0, 1]`: `1/f_p = L β · L (1-β) = ∫∫ (a_s^{1-β} a_u^β)⁻¹`;
* for `p ≤ -1`, `γ = -1/p ∈ (0, 1]`: `1/f_p = x^{-γ} L (γ+1) · L γ = ∫∫ ((x/a_s)^γ a_u^{1-γ})⁻¹`;
* for `1/2 ≤ p < 1`: `f_p = f_{p̃}` with `p̃ = p/(p-1) ≤ -1`.
Each integrand is the inverse of a geometric mean of operator monotone functions, so the harmonic
average is operator monotone (`WYD.OpMono.mono_inv_integral`).

*Only if.* For `p ∈ (0, 1/2)`, `f_p(x) → 0` as `x → ∞` while `f_p(1) = 1`; `p ∈ (-1, 0)` reduces
to it by `f_p = f_{p̃}`; `f_0` is `0` off `x = 1`. So `1 × 1` matrices already fail.
-/

namespace WYD.Theorem61

open Set MeasureTheory Filter Topology unitInterval Function WYD.OpMono WYD.Literal

/-! ### The scalar integrals -/

/-- `∫₀¹ (1 - s + s x)^{r-1} ds`, in closed form. -/
noncomputable def L (r x : ℝ) : ℝ :=
  if x = 1 then 1 else if r = 0 then Real.log x / (x - 1) else (x ^ r - 1) / (r * (x - 1))

theorem affine_pos {s x : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hx : 0 < x) : 0 < 1 - s + s * x := by
  rcases le_total x 1 with h | h
  · nlinarith [hs.1, hs.2]
  · nlinarith [hs.1, hs.2]

theorem integral_affine_rpow {x : ℝ} (hx : 0 < x) (r : ℝ) :
    ∫ s in (0 : ℝ)..1, (1 - s + s * x) ^ (r - 1) = L r x := by
  by_cases hx1 : x = 1
  · subst hx1; simp [L]
  have hc : x - 1 ≠ 0 := sub_ne_zero.2 hx1
  have h0 : (0 : ℝ) ∉ uIcc 1 x := notMem_uIcc_of_lt one_pos hx
  have e : ∀ s : ℝ, (1 - s + s * x) ^ (r - 1) = ((x - 1) * s + 1) ^ (r - 1) := fun s => by
    rw [show 1 - s + s * x = (x - 1) * s + 1 by ring]
  simp_rw [e]
  rw [intervalIntegral.integral_comp_mul_add (fun y : ℝ => y ^ (r - 1)) hc 1, mul_zero, zero_add,
    mul_one, sub_add_cancel, L]
  simp only [hx1, ↓reduceIte]
  by_cases hr : r = 0
  · subst hr
    simp only [zero_sub, Real.rpow_neg_one, ↓reduceIte]
    rw [integral_inv h0, div_one, smul_eq_mul, inv_mul_eq_div]
  · simp only [hr, ↓reduceIte]
    rw [integral_rpow (Or.inr ⟨by intro h; apply hr; linarith, h0⟩), sub_add_cancel,
      Real.one_rpow, smul_eq_mul]
    field_simp

theorem rpow_ne_one {x r : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) (hr : r ≠ 0) : x ^ r ≠ 1 := by
  intro h
  have := congrArg Real.log h
  rw [Real.log_rpow hx, Real.log_one] at this
  rcases mul_eq_zero.1 this with h' | h'
  · exact hr h'
  · rcases Real.log_eq_zero.1 h' with h'' | h'' | h''
    · exact hx.ne' h''
    · exact hx1 h''
    · linarith

/-! ### The kernels -/

/-- The kernel for `p = 1/β ≥ 1`: `(a_s^{1-β} a_u^β)⁻¹`. -/
noncomputable def kβ (β : ℝ) (ω : I × I) (x : ℝ) : ℝ :=
  ((1 - (ω.1 : ℝ) + ω.1 * x) ^ (1 - β) * (1 - (ω.2 : ℝ) + ω.2 * x) ^ β)⁻¹

/-- The kernel for `p = -1/γ ≤ -1`: `((x/a_s)^γ a_u^{1-γ})⁻¹`, with `x/a_s = (s + (1-s)/x)⁻¹`. -/
noncomputable def kγ (γ : ℝ) (ω : I × I) (x : ℝ) : ℝ :=
  (((ω.1 : ℝ) + (1 - ω.1) * x⁻¹)⁻¹ ^ (1 - (1 - γ)) * (1 - (ω.2 : ℝ) + ω.2 * x) ^ (1 - γ))⁻¹

theorem shifted_pos {s x : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hx : 0 < x) : 0 < s + (1 - s) * x⁻¹ := by
  rcases eq_or_lt_of_le hs.1 with h | h
  · subst h; simpa using hx
  · have := mul_nonneg (sub_nonneg.2 hs.2) (inv_pos.2 hx).le
    linarith

theorem kβ_eq {β x : ℝ} (hx : 0 < x) (ω : I × I) :
    kβ β ω x = (1 - (ω.1 : ℝ) + ω.1 * x) ^ (β - 1) * (1 - (ω.2 : ℝ) + ω.2 * x) ^ ((1 - β) - 1) := by
  have ha := affine_pos ω.1.2 hx
  have hb := affine_pos ω.2.2 hx
  rw [kβ, mul_inv, ← Real.rpow_neg ha.le, ← Real.rpow_neg hb.le, show -(1 - β) = β - 1 by ring,
    show -β = (1 - β) - 1 by ring]

theorem kγ_eq {γ x : ℝ} (hx : 0 < x) (ω : I × I) :
    kγ γ ω x = x ^ (-γ) * (1 - (ω.1 : ℝ) + ω.1 * x) ^ ((γ + 1) - 1) *
      (1 - (ω.2 : ℝ) + ω.2 * x) ^ (γ - 1) := by
  have ha := affine_pos ω.1.2 hx
  have hb := affine_pos ω.2.2 hx
  have e : ((ω.1 : ℝ) + (1 - ω.1) * x⁻¹)⁻¹ = x / (1 - (ω.1 : ℝ) + ω.1 * x) := by
    have := ha.ne'
    have := hx.ne'
    rw [show (ω.1 : ℝ) + (1 - ω.1) * x⁻¹ = (1 - (ω.1 : ℝ) + ω.1 * x) / x by field_simp; ring,
      inv_div]
  rw [kγ, e, show 1 - (1 - γ) = γ by ring, show (γ + 1) - 1 = γ by ring,
    Real.div_rpow hx.le ha.le, show γ - 1 = -(1 - γ) by ring, Real.rpow_neg hb.le,
    Real.rpow_neg hx.le]
  have : 0 < x ^ γ := Real.rpow_pos_of_pos hx γ
  have : 0 < (1 - (ω.1 : ℝ) + ω.1 * x) ^ γ := Real.rpow_pos_of_pos ha γ
  have : 0 < (1 - (ω.2 : ℝ) + ω.2 * x) ^ (1 - γ) := Real.rpow_pos_of_pos hb _
  field_simp

theorem integral_kβ {β x : ℝ} (hx : 0 < x) : ∫ ω, kβ β ω x = L β x * L (1 - β) x := by
  rw [← integral_affine_rpow hx, ← integral_affine_rpow hx, ← integral_prod_unitInterval]
  exact integral_congr_ae (ae_of_all _ fun ω => kβ_eq hx ω)

theorem integral_kγ {γ x : ℝ} (hx : 0 < x) :
    ∫ ω, kγ γ ω x = x ^ (-γ) * L (γ + 1) x * L γ x := by
  rw [← integral_affine_rpow hx, ← integral_affine_rpow hx, mul_assoc,
    ← integral_prod_unitInterval, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun ω => by dsimp only; rw [kγ_eq hx ω]; ring)

/-! ### `f_p` as a harmonic average -/

theorem fGI_eq_kβ {β : ℝ} (hβ : β ∈ Ioc (0 : ℝ) 1) {x : ℝ} (hx : 0 < x) :
    fGI (1 / β) x = (∫ ω, kβ β ω x)⁻¹ := by
  rw [integral_kβ hx]
  by_cases hx1 : x = 1
  · simp [fGI, L, hx1]
  have hc : x - 1 ≠ 0 := sub_ne_zero.2 hx1
  have hl : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx hx1
  rcases eq_or_lt_of_le hβ.2 with h1 | h1
  · subst h1
    simp only [div_one, sub_self, L, hx1, one_ne_zero, ↓reduceIte, Real.rpow_one,
      one_mul, div_self hc, fGI]
    rw [inv_div]
  have hβ0 : β ≠ 0 := hβ.1.ne'
  have hβ1 : 1 - β ≠ 0 := by linarith
  have hp1 : 1 / β ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hβ0] at h; linarith
  have h1p : 1 / (1 / β) = β := one_div_one_div β
  have hcp : 1 / conj (1 / β) = 1 - β := by
    unfold conj; field_simp
  have hpc : 1 / (1 / β * conj (1 / β)) = β * (1 - β) := by
    unfold conj
    have : (1 / β - 1) ≠ 0 := by
      intro h; apply hp1; linarith
    field_simp
  have e1 := rpow_ne_one hx hx1 hβ0
  have e2 := rpow_ne_one hx hx1 hβ1
  simp only [fGI, hx1, hp1, L, hβ0, hβ1, ↓reduceIte]
  rw [h1p, hcp, hpc]
  have : x ^ β - 1 ≠ 0 := sub_ne_zero.2 e1
  have : x ^ (1 - β) - 1 ≠ 0 := sub_ne_zero.2 e2
  field_simp

theorem fGI_eq_kγ {γ : ℝ} (hγ : γ ∈ Ioc (0 : ℝ) 1) {x : ℝ} (hx : 0 < x) :
    fGI (-1 / γ) x = (∫ ω, kγ γ ω x)⁻¹ := by
  rw [integral_kγ hx]
  by_cases hx1 : x = 1
  · simp [fGI, L, hx1]
  have hγ0 : γ ≠ 0 := hγ.1.ne'
  have hγ1 : γ + 1 ≠ 0 := by linarith [hγ.1]
  have hp1 : -1 / γ ≠ 1 := by
    have : -1 / γ < 0 := div_neg_of_neg_of_pos (by norm_num) hγ.1
    linarith
  have h1p : 1 / (-1 / γ) = -γ := by field_simp
  have hcp : 1 / conj (-1 / γ) = γ + 1 := by
    unfold conj
    have : -1 / γ - 1 ≠ 0 := by
      have : -1 / γ < 0 := div_neg_of_neg_of_pos (by norm_num) hγ.1
      linarith
    field_simp
    ring
  have hpc : 1 / (-1 / γ * conj (-1 / γ)) = -(γ * (γ + 1)) := by
    unfold conj
    have : -1 / γ - 1 ≠ 0 := by
      have : -1 / γ < 0 := div_neg_of_neg_of_pos (by norm_num) hγ.1
      linarith
    field_simp
    ring
  have e1 := rpow_ne_one hx hx1 hγ0
  have e2 := rpow_ne_one hx hx1 hγ1
  have hxγ : 0 < x ^ γ := Real.rpow_pos_of_pos hx γ
  simp only [fGI, hx1, hp1, L, hγ0, hγ1, ↓reduceIte]
  rw [h1p, hcp, hpc, Real.rpow_neg hx.le]
  have : x ^ γ - 1 ≠ 0 := sub_ne_zero.2 e1
  have : x ^ (γ + 1) - 1 ≠ 0 := sub_ne_zero.2 e2
  have : (x ^ γ)⁻¹ - 1 ≠ 0 := by
    exact sub_ne_zero.2 fun h => e1 (inv_eq_one.1 h)
  field_simp
  ring

/-! ### The kernels are operator antitone -/

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem good_affine {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Good (fun x => 1 - s + s * x) :=
  ⟨by fun_prop, fun _ hx => affine_pos hs hx⟩

theorem mono_affine {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Mono A (fun x => 1 - s + s * x) :=
  mono_id.affine continuousOn_id (1 - s) hs.1

theorem continuousOn_shifted (s : ℝ) : ContinuousOn (fun x : ℝ => s + (1 - s) * x⁻¹) (Ioi 0) :=
  continuousOn_const.add (continuousOn_const.mul (continuousOn_id.inv₀ fun _ hx => ne_of_gt hx))

theorem good_shifted {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Good (fun x => (s + (1 - s) * x⁻¹)⁻¹) :=
  Good.inv ⟨continuousOn_shifted s, fun _ hx => shifted_pos hs hx⟩

theorem mono_shifted {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Mono A (fun x => (s + (1 - s) * x⁻¹)⁻¹) :=
  (anti_inv.affine (continuousOn_id.inv₀ fun _ hx => ne_of_gt hx) s (sub_nonneg.2 hs.2)).inv
    ⟨continuousOn_shifted s, fun _ hx => shifted_pos hs hx⟩

theorem anti_kβ {β : ℝ} (hβ : β ∈ Ioc (0 : ℝ) 1) (ω : I × I) : Anti A (kβ β ω) :=
  (Mono.gmean (mono_affine ω.1.2) (mono_affine ω.2.2) (good_affine ω.1.2) (good_affine ω.2.2)
    ⟨hβ.1.le, hβ.2⟩).inv ((good_affine ω.1.2).gmean (good_affine ω.2.2) β)

theorem anti_kγ {γ : ℝ} (hγ : γ ∈ Ioc (0 : ℝ) 1) (ω : I × I) : Anti A (kγ γ ω) :=
  (Mono.gmean (mono_shifted ω.1.2) (mono_affine ω.2.2) (good_shifted ω.1.2) (good_affine ω.2.2)
    (t := 1 - γ) ⟨by linarith [hγ.2], by linarith [hγ.1]⟩).inv
    ((good_shifted ω.1.2).gmean (good_affine ω.2.2) (1 - γ))

end CStar

theorem continuousOn_kβ (β : ℝ) : ContinuousOn (uncurry (kβ β)) (univ ×ˢ Ioi 0) := by
  have h1 : ∀ q ∈ (univ ×ˢ Ioi 0 : Set ((I × I) × ℝ)), 0 < 1 - (q.1.1 : ℝ) + q.1.1 * q.2 :=
    fun q hq => affine_pos q.1.1.2 hq.2
  have h2 : ∀ q ∈ (univ ×ˢ Ioi 0 : Set ((I × I) × ℝ)), 0 < 1 - (q.1.2 : ℝ) + q.1.2 * q.2 :=
    fun q hq => affine_pos q.1.2.2 hq.2
  show ContinuousOn (fun q : (I × I) × ℝ =>
    ((1 - (q.1.1 : ℝ) + q.1.1 * q.2) ^ (1 - β) * (1 - (q.1.2 : ℝ) + q.1.2 * q.2) ^ β)⁻¹) _
  refine ContinuousOn.inv₀ (ContinuousOn.mul ?_ ?_) fun q hq => ?_
  · exact (Continuous.continuousOn (by fun_prop)).rpow_const fun q hq => Or.inl (h1 q hq).ne'
  · exact (Continuous.continuousOn (by fun_prop)).rpow_const fun q hq => Or.inl (h2 q hq).ne'
  · exact (mul_pos (Real.rpow_pos_of_pos (h1 q hq) _) (Real.rpow_pos_of_pos (h2 q hq) _)).ne'

theorem continuousOn_kγ (γ : ℝ) : ContinuousOn (uncurry (kγ γ)) (univ ×ˢ Ioi 0) := by
  have h1 : ∀ q ∈ (univ ×ˢ Ioi 0 : Set ((I × I) × ℝ)), 0 < (q.1.1 : ℝ) + (1 - q.1.1) * q.2⁻¹ :=
    fun q hq => shifted_pos q.1.1.2 hq.2
  have h2 : ∀ q ∈ (univ ×ˢ Ioi 0 : Set ((I × I) × ℝ)), 0 < 1 - (q.1.2 : ℝ) + q.1.2 * q.2 :=
    fun q hq => affine_pos q.1.2.2 hq.2
  have hinv : ContinuousOn (fun q : (I × I) × ℝ => q.2⁻¹) (univ ×ˢ Ioi 0) :=
    continuous_snd.continuousOn.inv₀ fun q hq => (show (0 : ℝ) < q.2 from hq.2).ne'
  have hc : ContinuousOn (fun q : (I × I) × ℝ => (q.1.1 : ℝ) + (1 - q.1.1) * q.2⁻¹)
      (univ ×ˢ Ioi 0) := by
    have h0 : Continuous (fun q : (I × I) × ℝ => (q.1.1 : ℝ)) := by fun_prop
    exact h0.continuousOn.add ((continuous_const.sub h0).continuousOn.mul hinv)
  show ContinuousOn (fun q : (I × I) × ℝ =>
    (((q.1.1 : ℝ) + (1 - q.1.1) * q.2⁻¹)⁻¹ ^ (1 - (1 - γ)) *
      (1 - (q.1.2 : ℝ) + q.1.2 * q.2) ^ (1 - γ))⁻¹) _
  refine ContinuousOn.inv₀ (ContinuousOn.mul ?_ ?_) fun q hq => ?_
  · exact (hc.inv₀ fun q hq => (h1 q hq).ne').rpow_const
      fun q hq => Or.inl (inv_pos.2 (h1 q hq)).ne'
  · exact (Continuous.continuousOn (by fun_prop)).rpow_const fun q hq => Or.inl (h2 q hq).ne'
  · exact (mul_pos (Real.rpow_pos_of_pos (inv_pos.2 (h1 q hq)) _)
      (Real.rpow_pos_of_pos (h2 q hq) _)).ne'

theorem kβ_pos (β : ℝ) (ω : I × I) {x : ℝ} (hx : 0 < x) : 0 < kβ β ω x :=
  inv_pos.2 (mul_pos (Real.rpow_pos_of_pos (affine_pos ω.1.2 hx) _)
    (Real.rpow_pos_of_pos (affine_pos ω.2.2 hx) _))

theorem kγ_pos (γ : ℝ) (ω : I × I) {x : ℝ} (hx : 0 < x) : 0 < kγ γ ω x :=
  inv_pos.2 (mul_pos (Real.rpow_pos_of_pos (inv_pos.2 (shifted_pos ω.1.2 hx)) _)
    (Real.rpow_pos_of_pos (affine_pos ω.2.2 hx) _))

/-! ### The "if" direction, in any unital C⋆-algebra -/

theorem fGI_pos {p : ℝ} (hp : p ≤ -1 ∨ 1 / 2 ≤ p) {x : ℝ} (hx : 0 < x) : 0 < fGI p x := by
  have caseβ : ∀ q : ℝ, 1 ≤ q → 0 < fGI q x := fun q hq => by
    have hβ : 1 / q ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, by rw [div_le_one (by linarith)]; exact hq⟩
    rw [← one_div_one_div q, fGI_eq_kβ hβ hx]
    exact inv_pos.2 (integral_pos (continuousOn_kβ _) (fun ω _ hx => kβ_pos _ ω hx) hx)
  have caseγ : ∀ q : ℝ, q ≤ -1 → 0 < fGI q x := fun q hq => by
    have hγ : -1 / q ∈ Ioc (0 : ℝ) 1 :=
      ⟨div_pos_of_neg_of_neg (by norm_num) (by linarith), by
        rw [div_le_one_of_neg (by linarith)]; exact hq⟩
    rw [show q = -1 / (-1 / q) by field_simp, fGI_eq_kγ hγ hx]
    exact inv_pos.2 (integral_pos (continuousOn_kγ _) (fun ω _ hx => kγ_pos _ ω hx) hx)
  rcases hp with hp | hp
  · exact caseγ p hp
  rcases le_or_gt 1 p with h1 | h1
  · exact caseβ p h1
  have h0 : p ≠ 0 := by linarith
  have hne : p ≠ 1 := h1.ne
  rw [← fGI_conj h0 hne x]
  refine caseγ _ ?_
  unfold conj
  rw [div_le_iff_of_neg (by linarith)]
  linarith

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem mono_fGI {p : ℝ} (hp : p ≤ -1 ∨ 1 / 2 ≤ p) : Mono A (fGI p) := by
  have caseβ : ∀ q : ℝ, 1 ≤ q → Mono A (fGI q) := fun q hq => by
    have hβ : 1 / q ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, by rw [div_le_one (by linarith)]; exact hq⟩
    refine (mono_inv_integral (continuousOn_kβ (1 / q)) (fun ω _ hx => kβ_pos _ ω hx)
      (anti_kβ hβ)).congr fun x hx => ?_
    dsimp only
    rw [← fGI_eq_kβ hβ hx, one_div_one_div]
  have caseγ : ∀ q : ℝ, q ≤ -1 → Mono A (fGI q) := fun q hq => by
    have hγ : -1 / q ∈ Ioc (0 : ℝ) 1 :=
      ⟨div_pos_of_neg_of_neg (by norm_num) (by linarith), by
        rw [div_le_one_of_neg (by linarith)]; exact hq⟩
    refine (mono_inv_integral (continuousOn_kγ (-1 / q)) (fun ω _ hx => kγ_pos _ ω hx)
      (anti_kγ hγ)).congr fun x hx => ?_
    dsimp only
    rw [← fGI_eq_kγ hγ hx, show -1 / (-1 / q) = q by field_simp]
  rcases hp with hp | hp
  · exact caseγ p hp
  rcases le_or_gt 1 p with h1 | h1
  · exact caseβ p h1
  have h0 : p ≠ 0 := by linarith
  refine (caseγ (conj p) ?_).congr fun x _ => fGI_conj h0 h1.ne x
  unfold conj
  rw [div_le_iff_of_neg (by linarith)]
  linarith

end CStar

/-! ### The "only if" direction -/

theorem fGI_one (p : ℝ) : fGI p 1 = 1 := by simp [fGI]

theorem fGI_one_div {β : ℝ} (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) {x : ℝ} (hx1 : x ≠ 1) :
    fGI (1 / β) x = β * (1 - β) * ((x - 1) ^ 2 / ((x ^ β - 1) * (x ^ (1 - β) - 1))) := by
  have hp1 : 1 / β ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hβ0] at h; exact hβ1 h.symm
  have hβ1' : 1 - β ≠ 0 := sub_ne_zero.2 (Ne.symm hβ1)
  have h1p : 1 / (1 / β) = β := one_div_one_div β
  have hcp : 1 / conj (1 / β) = 1 - β := by
    unfold conj; field_simp
  have hpc : 1 / (1 / β * conj (1 / β)) = β * (1 - β) := by
    unfold conj
    have : (1 / β - 1) ≠ 0 := by
      intro h; apply hp1; linarith
    field_simp
  simp only [fGI, hx1, hp1, ↓reduceIte]
  rw [h1p, hcp, hpc]

/-- For `β > 2`, `f_{1/β}(x) → 0` as `x → ∞`, so `f_{1/β}(x) < 1 = f_{1/β}(1)` for some `x > 1`. -/
theorem exists_fGI_lt_one {β : ℝ} (hβ : 2 < β) : ∃ x, 1 < x ∧ fGI (1 / β) x < 1 := by
  set h : ℝ → ℝ := fun x => β * (β - 1) * (1 - x⁻¹) ^ 2 * x ^ (-(β - 2)) /
    ((1 - x ^ (-β)) * (1 - x ^ (-(β - 1)))) with hh
  have ht : Tendsto h atTop (𝓝 0) := by
    have t1 := tendsto_inv_atTop_zero (𝕜 := ℝ)
    have t2 := tendsto_rpow_neg_atTop (show 0 < β - 2 by linarith)
    have t3 := tendsto_rpow_neg_atTop (show 0 < β by linarith)
    have t4 := tendsto_rpow_neg_atTop (show 0 < β - 1 by linarith)
    have := ((tendsto_const_nhds (x := β * (β - 1))).mul
      ((tendsto_const_nhds (x := (1 : ℝ)).sub t1).pow 2)).mul t2 |>.div
      ((tendsto_const_nhds (x := (1 : ℝ)).sub t3).mul (tendsto_const_nhds (x := (1 : ℝ)).sub t4))
      (by norm_num)
    convert this using 2
    norm_num
  obtain ⟨x, hlt, hx1⟩ := ((ht.eventually (eventually_lt_nhds one_pos)).and
    (eventually_gt_atTop 1)).exists
  refine ⟨x, hx1, ?_⟩
  have hx : 0 < x := by linarith
  rw [fGI_one_div (by linarith) (by linarith) hx1.ne']
  convert hlt using 1
  have e1 := rpow_ne_one hx hx1.ne' (show β ≠ 0 by linarith)
  have e2 := rpow_ne_one hx hx1.ne' (show β - 1 ≠ 0 by linarith)
  have hxβ : 0 < x ^ β := Real.rpow_pos_of_pos hx β
  rw [hh]
  dsimp only
  rw [Real.rpow_neg hx.le, Real.rpow_neg hx.le, Real.rpow_neg hx.le, Real.rpow_sub hx,
    Real.rpow_sub hx, Real.rpow_sub hx, Real.rpow_one, Real.rpow_two]
  have : x ^ β - 1 ≠ 0 := sub_ne_zero.2 e1
  have : x ^ β - x ≠ 0 := by
    intro h; apply e2; rw [Real.rpow_sub_one hx.ne', sub_eq_zero.1 h, div_self hx.ne']
  have : x / x ^ β - 1 ≠ 0 := by
    intro h; apply this; field_simp at h; linarith
  have hne : x - x ^ β ≠ 0 := by
    intro h; apply this; field_simp; linarith
  field_simp
  ring

theorem exists_not_mono {p : ℝ} (h1 : -1 < p) (h2 : p < 1 / 2) : ∃ x, 1 < x ∧ fGI p x < fGI p 1 := by
  rw [fGI_one]
  have pos : ∀ q : ℝ, 0 < q → q < 1 / 2 → ∃ x, 1 < x ∧ fGI q x < 1 := fun q hq0 hq => by
    have := exists_fGI_lt_one (β := 1 / q) (by rw [lt_div_iff₀ hq0]; linarith)
    rwa [one_div_one_div] at this
  rcases lt_trichotomy p 0 with hp | hp | hp
  · obtain ⟨x, hx, hlt⟩ := pos (conj p) (by unfold conj; exact div_pos_of_neg_of_neg hp (by linarith))
      (by unfold conj; rw [div_lt_iff_of_neg (by linarith)]; linarith)
    exact ⟨x, hx, by rwa [fGI_conj hp.ne (by linarith)] at hlt⟩
  · subst hp
    exact ⟨2, by norm_num, by simp [fGI, conj]⟩
  · exact pos p hp h2

/-! ### Normalized and symmetric -/

/-- `f_p` is symmetric, `f(x) = x f(1/x)`, for every `p` (it rests on `1/p + 1/p̃ = 1`). -/
theorem fGI_symm (p : ℝ) {x : ℝ} (hx : 0 < x) : fGI p x = x * fGI p x⁻¹ := by
  by_cases hx1 : x = 1
  · subst hx1; simp [fGI]
  have hxi1 : x⁻¹ ≠ 1 := fun h => hx1 (inv_eq_one.1 h)
  have hc : x - 1 ≠ 0 := sub_ne_zero.2 hx1
  have hl : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx hx1
  by_cases hp1 : p = 1
  · subst hp1
    simp only [fGI, hx1, hxi1, ↓reduceIte, Real.log_inv]
    field_simp
    ring
  by_cases hp0 : p = 0
  · subst hp0; simp [fGI, conj, hx1]
  have ha : 1 / p ≠ 0 := one_div_ne_zero hp0
  have hcp : conj p ≠ 0 := by
    unfold conj; exact div_ne_zero hp0 (sub_ne_zero.2 hp1)
  have hb : 1 / conj p ≠ 0 := one_div_ne_zero hcp
  have hab := one_div_add_one_div_conj hp0 hp1
  have e1 := rpow_ne_one hx hx1 ha
  have e2 := rpow_ne_one hx hx1 hb
  have hxab : x ^ (1 / p) * x ^ (1 / conj p) = x := by
    rw [← Real.rpow_add hx, hab, Real.rpow_one]
  have : 0 < x ^ (1 / p) := Real.rpow_pos_of_pos hx _
  have : 0 < x ^ (1 / conj p) := Real.rpow_pos_of_pos hx _
  have : x ^ (1 / p) - 1 ≠ 0 := sub_ne_zero.2 e1
  have : x ^ (1 / conj p) - 1 ≠ 0 := sub_ne_zero.2 e2
  simp only [fGI, hx1, hxi1, hp1, ↓reduceIte]
  rw [Real.inv_rpow hx.le, Real.inv_rpow hx.le]
  have : (x ^ (1 / p))⁻¹ - 1 ≠ 0 := sub_ne_zero.2 fun h => e1 (inv_eq_one.1 h)
  have : (x ^ (1 / conj p))⁻¹ - 1 ≠ 0 := sub_ne_zero.2 fun h => e2 (inv_eq_one.1 h)
  generalize 1 / (p * conj p) = c
  generalize x ^ (1 / p) = a at *
  generalize x ^ (1 / conj p) = b at *
  subst hxab
  field_simp
  ring

/-! ### Theorem 6.1 -/

open scoped ComplexOrder

/-- Operator monotone in the sense of Gibilisco–Isola (Section 5): for all `n` and `n × n` matrices
`0 ≤ A ≤ B`, `0 ≤ f(A) ≤ f(B)`. As `f` is a function on `(0, ∞)`, `A` is taken positive definite. -/
def OperatorMonotone (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), A.PosDef → (B - A).PosSemidef →
    (cfc f A).PosSemidef ∧ (cfc f B - cfc f A).PosSemidef

/-- GI's convention after Section 5: "operator monotone" means normalized (`f(1) = 1`), symmetric
(`f(x) = x f(1/x)`) operator monotone. -/
def NSOperatorMonotone (f : ℝ → ℝ) : Prop :=
  OperatorMonotone f ∧ f 1 = 1 ∧ ∀ x, 0 < x → f x = x * f x⁻¹

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- Theorem 6.1 with plain operator monotonicity. `fGI 0` (GI leave `f_0` undefined) is the junk
value `1` at `x = 1` and `0` elsewhere, also the pointwise limit of `f_p` as `p → 0`; `p = 0` is
outside the range either way. -/
theorem operatorMonotone_fGI_iff (p : ℝ) : OperatorMonotone (fGI p) ↔ p ≤ -1 ∨ 1 / 2 ≤ p := by
  constructor
  · intro hmono
    by_contra hp
    simp only [not_or, not_le] at hp
    obtain ⟨x, hx, hlt⟩ := exists_not_mono hp.1 hp.2
    let M := Matrix (Fin 1) (Fin 1) ℂ
    have hA : (algebraMap ℝ M 1).PosDef := by
      rw [map_one]; exact Matrix.PosDef.one
    have hAB : (algebraMap ℝ M x - algebraMap ℝ M 1).PosSemidef := by
      rw [← map_sub, Matrix.algebraMap_eq_diagonal, Matrix.posSemidef_diagonal_iff]
      intro i
      show (0 : ℂ) ≤ ((x - 1 : ℝ) : ℂ)
      exact Complex.zero_le_real.2 (by linarith)
    have h := (hmono 1 _ _ hA hAB).2
    rw [cfc_algebraMap, cfc_algebraMap, ← map_sub, Matrix.algebraMap_eq_diagonal,
      Matrix.posSemidef_diagonal_iff] at h
    have h0 := h 0
    simp only [Pi.algebraMap_apply, Complex.coe_algebraMap, Complex.zero_le_real] at h0
    linarith
  · intro hp n A B hA hAB
    have hX : IsStrictlyPositive A :=
      IsStrictlyPositive.iff_of_unital.2 ⟨Matrix.nonneg_iff_posSemidef.2 hA.posSemidef, hA.isUnit⟩
    refine ⟨Matrix.nonneg_iff_posSemidef.1 (cfc_nonneg fun x hx => (fGI_pos hp ?_).le),
      Matrix.le_iff.1 (mono_fGI hp hX (Matrix.le_iff.2 hAB))⟩
    exact hX.spectrum_pos hx

/-- **Theorem 6.1** (Hasegawa; Hasegawa–Petz), in GI's sense of "operator monotone" (normalized,
symmetric). `f_p` is operator monotone iff `p ∈ (-∞, -1] ∪ [1/2, ∞)`. (GI also list `p = ∞`, where
`f_∞ = f_1`.) -/
theorem theorem61 (p : ℝ) : NSOperatorMonotone (fGI p) ↔ p ≤ -1 ∨ 1 / 2 ≤ p := by
  rw [NSOperatorMonotone, ← operatorMonotone_fGI_iff p]
  exact ⟨fun h => h.1, fun h => ⟨h, fGI_one p, fun _ hx => fGI_symm p hx⟩⟩

end WYD.Theorem61
