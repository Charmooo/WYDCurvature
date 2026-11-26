/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.ForMathlib.Majorization
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Dittmann's reduction for a general curvature function

`PetzCurvature/Dittmann/Mixing.lean` with the Kubo–Mori function replaced by any symmetric
smooth function `hs` on the positive octant (`IsCurvFun hs`).
-/

open Finset Filter Topology

namespace WYD

/-- A symmetric function on the positive octant, smooth there. -/
structure IsCurvFun (hs : ℝ → ℝ → ℝ → ℝ) : Prop where
  comm₁₂ : ∀ x y z, hs x y z = hs y x z
  comm₂₃ : ∀ x y z, hs x y z = hs x z y
  smooth : ∀ {p : ℝ × ℝ × ℝ}, 0 < p.1 → 0 < p.2.1 → 0 < p.2.2 → ∀ n : ℕ,
    ContDiffAt ℝ n (fun q : ℝ × ℝ × ℝ ↦ hs q.1 q.2.1 q.2.2) p

theorem sum_cyclic {d : Type*} [Fintype d] {M : Type*} [AddCommMonoid M] (g : d → d → d → M) :
    ∑ i, ∑ j, ∑ k, g j k i = ∑ i, ∑ j, ∑ k, g i j k := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]

variable {hs : ℝ → ℝ → ℝ → ℝ}

theorem IsCurvFun.cyclic (C : IsCurvFun hs) (x y z : ℝ) : hs x y z = hs y z x := by
  rw [C.comm₁₂, C.comm₂₃]

theorem IsCurvFun.comp (C : IsCurvFun hs) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g h : E → ℝ} {x₀ : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f x₀) (hg : ContDiffAt ℝ n g x₀)
    (hh : ContDiffAt ℝ n h x₀) (hf0 : 0 < f x₀) (hg0 : 0 < g x₀) (hh0 : 0 < h x₀) :
    ContDiffAt ℝ n (fun x ↦ hs (f x) (g x) (h x)) x₀ :=
  ContDiffAt.comp (g := fun q : ℝ × ℝ × ℝ ↦ hs q.1 q.2.1 q.2.2)
    (f := fun x ↦ (f x, g x, h x)) x₀
    (C.smooth (p := (f x₀, g x₀, h x₀)) hf0 hg0 hh0 n) (hf.prodMk (hg.prodMk hh))

/-! ### The first partial derivative and the chain rule -/

/-- `hs′(x, y, z)`: the partial derivative of `hs` in its first argument. -/
noncomputable def hsDeriv (hs : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun u ↦ hs u y z) x

/-- The partial derivative of `hs` in the first argument, as a derivative. -/
theorem IsCurvFun.hasDerivAt_fst (C : IsCurvFun hs) {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    HasDerivAt (fun u ↦ hs u y z) (hsDeriv hs x y z) x :=
  ((C.comp (n := 1) contDiffAt_id contDiffAt_const contDiffAt_const hx hy
    hz).differentiableAt one_ne_zero).hasDerivAt

/-- The chain rule for `hs`: `d/dt hs(u, v, w) = hs′(u, v, w) u′ + hs′(v, u, w) v′ +
hs′(w, u, v) w′`. -/
theorem IsCurvFun.hasDerivAt_comp (C : IsCurvFun hs) {u v w : ℝ → ℝ} {u' v' w' t : ℝ} (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) (hu0 : 0 < u t) (hv0 : 0 < v t)
    (hw0 : 0 < w t) :
    HasDerivAt (fun s ↦ hs (u s) (v s) (w s))
      (hsDeriv hs (u t) (v t) (w t) * u' + hsDeriv hs (v t) (u t) (w t) * v' +
        hsDeriv hs (w t) (u t) (v t) * w') t := by
  set F : ℝ × ℝ × ℝ → ℝ := fun q ↦ hs q.1 q.2.1 q.2.2
  set p : ℝ × ℝ × ℝ := (u t, v t, w t)
  have hF : HasFDerivAt F (fderiv ℝ F p) p :=
    ((C.smooth (p := p) hu0 hv0 hw0 1).differentiableAt one_ne_zero).hasFDerivAt
  have hc : HasDerivAt (fun s ↦ (u s, v s, w s)) (u', v', w') t := hu.prodMk (hv.prodMk hw)
  have line : ∀ (e : ℝ × ℝ × ℝ) (c' : ℝ),
      HasDerivAt (fun r : ℝ ↦ F (p + r • e)) c' 0 → fderiv ℝ F p e = c' := by
    intro e c' h
    have hl : HasDerivAt (fun r : ℝ ↦ p + r • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add p
    exact (hF.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hl (by simp)).unique h
  have e1 : fderiv ℝ F p (1, 0, 0) = hsDeriv hs (u t) (v t) (w t) := by
    refine line _ _ ?_
    have h0 := HasDerivAt.comp_const_add (u t) 0 (by simpa using C.hasDerivAt_fst hu0 hv0 hw0)
    have hfun : (fun r : ℝ ↦ F (p + r • ((1, 0, 0) : ℝ × ℝ × ℝ))) =
        fun r ↦ hs (u t + r) (v t) (w t) := by
      funext r
      simp [F, p]
    rw [hfun]
    exact h0
  have e2 : fderiv ℝ F p (0, 1, 0) = hsDeriv hs (v t) (u t) (w t) := by
    refine line _ _ ?_
    have h0 := HasDerivAt.comp_const_add (v t) 0 (by simpa using C.hasDerivAt_fst hv0 hu0 hw0)
    have hfun : (fun r : ℝ ↦ F (p + r • ((0, 1, 0) : ℝ × ℝ × ℝ))) =
        fun r ↦ hs (v t + r) (u t) (w t) := by
      funext r
      simp only [F, p, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, mul_zero, add_zero]
      exact C.comm₁₂ _ _ _
    rw [hfun]
    exact h0
  have e3 : fderiv ℝ F p (0, 0, 1) = hsDeriv hs (w t) (u t) (v t) := by
    refine line _ _ ?_
    have h0 := HasDerivAt.comp_const_add (w t) 0 (by simpa using C.hasDerivAt_fst hw0 hu0 hv0)
    have hfun : (fun r : ℝ ↦ F (p + r • ((0, 0, 1) : ℝ × ℝ × ℝ))) =
        fun r ↦ hs (w t + r) (u t) (v t) := by
      funext r
      simp only [F, p, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, mul_zero, add_zero]
      exact (C.cyclic _ _ _).trans (C.cyclic _ _ _)
    rw [hfun]
    exact h0
  have hsplit : ((u', v', w') : ℝ × ℝ × ℝ) =
      u' • ((1, 0, 0) : ℝ × ℝ × ℝ) + v' • ((0, 1, 0) : ℝ × ℝ × ℝ) +
        w' • ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    ext <;> simp
  have := hF.comp_hasDerivAt t hc
  rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul, e1, e2, e3] at this
  simp only [smul_eq_mul] at this
  rw [show hsDeriv hs (u t) (v t) (w t) * u' + hsDeriv hs (v t) (u t) (w t) * v' +
      hsDeriv hs (w t) (u t) (v t) * w' = u' * hsDeriv hs (u t) (v t) (w t) +
        v' * hsDeriv hs (v t) (u t) (w t) + w' * hsDeriv hs (w t) (u t) (v t) by ring]
  exact this

theorem IsCurvFun.hsDeriv_comm₂₃ (C : IsCurvFun hs) (x y z : ℝ) : hsDeriv hs x y z = hsDeriv hs x z y := by
  simp only [hsDeriv, C.comm₂₃ _ y z]

/-! ### Dittmann's inequalities and the gradient of the curvature sum -/

/-- **Dittmann's inequalities (62)–(65)** (the conclusion of his Lemma 4), for all positive
`x < y`, `λ`, `µ`, with `hs′` the partial derivative in the first argument. Dittmann derives them
from the concavity of `hs` along the segments from `(x, x, y)`, `(x, x, λ)`, `(x, y, λ)`,
`(x, λ, µ)` to `(y, y, x)`, `(y, y, λ)`, `(y, x, λ)`, `(y, λ, µ)`. -/
structure DittmannInequalities (hs : ℝ → ℝ → ℝ → ℝ) : Prop where
  ineq62 : ∀ x y : ℝ, 0 < x → x < y → 0 ≤ 2 * hsDeriv hs x x y - hsDeriv hs y x x -
    2 * hsDeriv hs y x y + hsDeriv hs x y y
  ineq63 : ∀ x y l : ℝ, 0 < x → x < y → 0 < l → 0 ≤ hsDeriv hs x x l - hsDeriv hs y y l
  ineq64 : ∀ x y l : ℝ, 0 < x → x < y → 0 < l → 0 ≤ hsDeriv hs x y l - hsDeriv hs y x l
  ineq65 : ∀ x y l m : ℝ, 0 < x → x < y → 0 < l → 0 < m →
    0 ≤ hsDeriv hs x l m - hsDeriv hs y l m

variable {ι : Type*} [Fintype ι]

/-- The eigenvalue part of Dittmann's formula (58):
`∑_{(i, j, k)} hs(lᵢ, lⱼ, lₖ) - ∑ᵢ hs(lᵢ, lᵢ, lᵢ)`. -/
noncomputable def curvSum (hs : ℝ → ℝ → ℝ → ℝ) (l : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, hs (l i) (l j) (l k) - ∑ i, hs (l i) (l i) (l i)

/-- The partial derivative of `curvSum hs` in `lₐ`: `3 (∑ⱼₖ hs′(lₐ, lⱼ, lₖ) - hs′(lₐ, lₐ, lₐ))`. -/
noncomputable def curvGrad (hs : ℝ → ℝ → ℝ → ℝ) (l : ι → ℝ) (a : ι) : ℝ :=
  3 * (∑ j, ∑ k, hsDeriv hs (l a) (l j) (l k) - hsDeriv hs (l a) (l a) (l a))

/-- The derivative of `curvSum hs` along a curve of positive vectors. -/
theorem IsCurvFun.hasDerivAt_curvSum (C : IsCurvFun hs) {L : ℝ → ι → ℝ} {L' : ι → ℝ} {t : ℝ}
    (hL : ∀ i, HasDerivAt (fun s ↦ L s i) (L' i) t) (hpos : ∀ i, 0 < L t i) :
    HasDerivAt (fun s ↦ curvSum hs (L s)) (∑ a, curvGrad hs (L t) a * L' a) t := by
  have h3 := fun i j k ↦ C.hasDerivAt_comp (hL i) (hL j) (hL k) (hpos i) (hpos j) (hpos k)
  have hd := fun i ↦ C.hasDerivAt_comp (hL i) (hL i) (hL i) (hpos i) (hpos i) (hpos i)
  have H := (HasDerivAt.fun_sum (u := univ) fun i _ ↦ HasDerivAt.fun_sum (u := univ) fun j _ ↦
    HasDerivAt.fun_sum (u := univ) fun k _ ↦ h3 i j k).sub
      (HasDerivAt.fun_sum (u := univ) fun i _ ↦ hd i)
  refine H.congr_deriv ?_
  have c2 : ∑ i, ∑ j, ∑ k, hsDeriv hs (L t j) (L t i) (L t k) * L' j =
      ∑ i, ∑ j, ∑ k, hsDeriv hs (L t i) (L t j) (L t k) * L' i := Finset.sum_comm
  have c3 : ∑ i, ∑ j, ∑ k, hsDeriv hs (L t k) (L t i) (L t j) * L' k =
      ∑ i, ∑ j, ∑ k, hsDeriv hs (L t i) (L t j) (L t k) * L' i :=
    (sum_cyclic fun a b c ↦ hsDeriv hs (L t c) (L t a) (L t b) * L' c).symm
  have hg : ∑ a, curvGrad hs (L t) a * L' a =
      3 * ∑ i, ∑ j, ∑ k, hsDeriv hs (L t i) (L t j) (L t k) * L' i -
        3 * ∑ i, hsDeriv hs (L t i) (L t i) (L t i) * L' i := by
    simp only [curvGrad, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  simp only [Finset.sum_add_distrib]
  rw [c2, c3, hg]
  ring

section Split

variable [DecidableEq ι] {a b : ι}

omit [Fintype ι] in
theorem sum_split_two {M : Type*} [AddCommMonoid M] [Fintype ι] (hab : a ≠ b) (f : ι → M) :
    ∑ j, f j = f a + f b + ∑ j ∈ (univ.erase a).erase b, f j := by
  rw [← Finset.add_sum_erase univ f (mem_univ a),
    ← Finset.add_sum_erase (univ.erase a) f (mem_erase.mpr ⟨hab.symm, mem_univ b⟩), add_assoc]

omit [Fintype ι] in
theorem sum_sum_split_two [Fintype ι] (hab : a ≠ b) (f : ι → ι → ℝ) :
    ∑ j, ∑ k, f j k = f a a + f a b + f b a + f b b +
      ∑ r ∈ (univ.erase a).erase b, (f a r + f r a + f b r + f r b) +
        ∑ j ∈ (univ.erase a).erase b, ∑ k ∈ (univ.erase a).erase b, f j k := by
  rw [sum_split_two hab]
  simp only [sum_split_two hab (f _), Finset.sum_add_distrib]
  ring

end Split

/-- **Dittmann's identity**: the expansion of `⅓ (∂ₐ - ∂_b) curvSum hs` in Dittmann's proof of
Theorem 3, in four groups of terms: the pair `a, b` alone (the expression of (62)), one other
index (those of (63) and (64)), and two other indices (that of (65)). -/
theorem IsCurvFun.curvGrad_sub_curvGrad (C : IsCurvFun hs) [DecidableEq ι] (l : ι → ℝ) {a b : ι} (hne : a ≠ b) :
    curvGrad hs l a - curvGrad hs l b = 3 *
      ((2 * hsDeriv hs (l a) (l a) (l b) - hsDeriv hs (l b) (l a) (l a) -
        2 * hsDeriv hs (l b) (l a) (l b) + hsDeriv hs (l a) (l b) (l b)) +
      2 * ∑ r ∈ (univ.erase a).erase b,
        ((hsDeriv hs (l a) (l a) (l r) - hsDeriv hs (l b) (l b) (l r)) +
          (hsDeriv hs (l a) (l b) (l r) - hsDeriv hs (l b) (l a) (l r))) +
      ∑ j ∈ (univ.erase a).erase b, ∑ k ∈ (univ.erase a).erase b,
        (hsDeriv hs (l a) (l j) (l k) - hsDeriv hs (l b) (l j) (l k))) := by
  have s₁ : ∀ u v, ∑ r ∈ (univ.erase a).erase b, hsDeriv hs (l u) (l r) (l v) =
      ∑ r ∈ (univ.erase a).erase b, hsDeriv hs (l u) (l v) (l r) :=
    fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ C.hsDeriv_comm₂₃ _ _ _
  simp only [curvGrad]
  rw [sum_sum_split_two hne (fun j k ↦ hsDeriv hs (l a) (l j) (l k)),
    sum_sum_split_two hne (fun j k ↦ hsDeriv hs (l b) (l j) (l k))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [s₁ a a, s₁ a b, s₁ b a, s₁ b b, C.hsDeriv_comm₂₃ (l a) (l b) (l a),
    C.hsDeriv_comm₂₃ (l b) (l b) (l a)]
  ring

/-- Under (63)–(65), the terms of Dittmann's identity other than that of (62) are nonnegative:
`3 E₆₂ ≤ ∂ₐ curvSum hs - ∂_b curvSum hs` for `lₐ < l_b`, with `E₆₂` the expression of (62). -/
theorem IsCurvFun.le_curvGrad_sub_curvGrad (C : IsCurvFun hs) (H : DittmannInequalities hs) {l : ι → ℝ} (hl : ∀ i, 0 < l i)
    {a b : ι} (hab : l a < l b) :
    3 * (2 * hsDeriv hs (l a) (l a) (l b) - hsDeriv hs (l b) (l a) (l a) -
      2 * hsDeriv hs (l b) (l a) (l b) + hsDeriv hs (l a) (l b) (l b)) ≤
        curvGrad hs l a - curvGrad hs l b := by
  classical
  rw [C.curvGrad_sub_curvGrad l fun h ↦ hab.ne (congrArg l h)]
  have hR : 0 ≤ ∑ r ∈ (univ.erase a).erase b,
      ((hsDeriv hs (l a) (l a) (l r) - hsDeriv hs (l b) (l b) (l r)) +
        (hsDeriv hs (l a) (l b) (l r) - hsDeriv hs (l b) (l a) (l r))) :=
    Finset.sum_nonneg fun r _ ↦ add_nonneg (H.ineq63 _ _ _ (hl a) hab (hl r))
      (H.ineq64 _ _ _ (hl a) hab (hl r))
  have hRR : 0 ≤ ∑ j ∈ (univ.erase a).erase b, ∑ k ∈ (univ.erase a).erase b,
      (hsDeriv hs (l a) (l j) (l k) - hsDeriv hs (l b) (l j) (l k)) :=
    Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun k _ ↦
      H.ineq65 _ _ _ _ (hl a) hab (hl j) (hl k)
  linarith

/-- **Dittmann's identity, as a sign**: under (62)–(65), if `lₐ < l_b` then
`∂_b curvSum hs ≤ ∂ₐ curvSum hs`, i.e. moving weight from `l_b` to `lₐ` (mixing) does not decrease
the curvature. The identity is the expansion of `⅓ (∂ₐ - ∂_b) curvSum hs` in Dittmann's proof of
Theorem 3 (`curvGrad_sub_curvGrad`). Its four groups of terms (the pair `a, b` alone, one other
index, two other indices) are signed by (62), by (63) and (64), and by (65). -/
theorem IsCurvFun.curvGrad_le (C : IsCurvFun hs) (H : DittmannInequalities hs) {l : ι → ℝ}
    (hl : ∀ i, 0 < l i) {a b : ι} (hab : l a < l b) : curvGrad hs l b ≤ curvGrad hs l a := by
  have h := C.le_curvGrad_sub_curvGrad H hl hab
  have e62 := H.ineq62 _ _ (hl a) hab
  linarith

/-- **Dittmann's identity, as a strict sign**: under (62)–(65), with (62) strict, if `lₐ < l_b`
then `∂_b curvSum hs < ∂ₐ curvSum hs`. Only (62) needs to be strict: its term is present for every pair
`a, b`, while the others need further indices. -/
theorem IsCurvFun.curvGrad_lt (C : IsCurvFun hs) (H : DittmannInequalities hs)
    (H62 : ∀ x y : ℝ, 0 < x → x < y → 0 < 2 * hsDeriv hs x x y - hsDeriv hs y x x -
      2 * hsDeriv hs y x y + hsDeriv hs x y y)
    {l : ι → ℝ} (hl : ∀ i, 0 < l i) {a b : ι} (hab : l a < l b) :
    curvGrad hs l b < curvGrad hs l a := by
  have h := C.le_curvGrad_sub_curvGrad H hl hab
  have e62 := H62 _ _ (hl a) hab
  linarith

/-- `∂ₐ curvSum hs` depends on `a` only through `lₐ`. -/
theorem curvGrad_congr {l : ι → ℝ} {a b : ι} (h : l a = l b) : curvGrad hs l a = curvGrad hs l b := by
  simp only [curvGrad, h]

/-- `curvSum hs` is invariant under relabeling. -/
theorem curvSum_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (l : ι → ℝ) :
    curvSum hs (l ∘ e) = curvSum hs l := by
  simp only [curvSum, Function.comp_apply]
  congr 1
  · rw [← e.sum_comp (fun i ↦ ∑ j, ∑ k, hs (l i) (l j) (l k))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← e.sum_comp (fun j ↦ ∑ k, hs (l (e i)) (l j) (l k))]
    exact Finset.sum_congr rfl fun j _ ↦ e.sum_comp (fun k ↦ hs (l (e i)) (l (e j)) (l k))
  · exact e.sum_comp (fun i ↦ hs (l i) (l i) (l i))

/-! ### Theorem 3 -/

/-- **Under (62)–(65), `curvSum hs` increases under mixing**: if `x` is majorized by `y` (both
positive), then `curvSum hs y ≤ curvSum hs x`. -/
theorem IsCurvFun.curvSum_le_of_isMajorizedBy (C : IsCurvFun hs) (H : DittmannInequalities hs) {n : ℕ} {x y : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y) :
    curvSum hs y ≤ curvSum hs x := by
  refine le_of_isMajorizedBy (U := {z | ∀ i, 0 < z i}) (grad := curvGrad hs) ?_ ?_ ?_ ?_ hx hy hxy
  · intro z hz w hw a b ha hb hab i
    have := hz i
    have := hw i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | rfl
    · positivity
    · simp only [zero_mul, zero_add] at hab ⊢
      rw [hab, one_mul]
      exact hw i
  · intro z hz σ
    exact ⟨fun i ↦ hz (σ i), curvSum_comp_equiv σ z⟩
  · intro z hz v
    have h := C.hasDerivAt_curvSum (L := fun s ↦ z + s • v) (L' := v) (t := 0)
      (fun i ↦ by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (z i))
      (fun i ↦ by simpa using hz i)
    simpa using h
  · intro z hz hmono a b hab
    rcases (hmono hab).lt_or_eq with h | h
    · exact C.curvGrad_le H hz h
    · exact (curvGrad_congr h).ge

/-- Under (62)–(65), with (62) strict: if `x` is majorized by `y` and the sorted vectors differ, then
`curvSum hs y < curvSum hs x`. -/
theorem IsCurvFun.curvSum_lt_of_isMajorizedBy (C : IsCurvFun hs) (H : DittmannInequalities hs)
    (H62 : ∀ x y : ℝ, 0 < x → x < y → 0 < 2 * hsDeriv hs x x y - hsDeriv hs y x x -
      2 * hsDeriv hs y x y + hsDeriv hs x y y)
    {n : ℕ} {x y : Fin n → ℝ} (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : IsMajorizedBy x y)
    (hne : Majorization.sortInc x ≠ Majorization.sortInc y) : curvSum hs y < curvSum hs x := by
  refine lt_of_isMajorizedBy (U := {z | ∀ i, 0 < z i}) (grad := curvGrad hs) ?_ ?_ ?_ ?_
    (fun z hz _ a b hab ↦ C.curvGrad_lt H H62 hz hab) hx hy hxy hne
  · intro z hz w hw a b ha hb hab i
    have := hz i
    have := hw i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.lt_or_eq with ha' | rfl
    · positivity
    · simp only [zero_mul, zero_add] at hab ⊢
      rw [hab, one_mul]
      exact hw i
  · intro z hz σ
    exact ⟨fun i ↦ hz (σ i), curvSum_comp_equiv σ z⟩
  · intro z hz v
    have h := C.hasDerivAt_curvSum (L := fun s ↦ z + s • v) (L' := v) (t := 0)
      (fun i ↦ by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (z i))
      (fun i ↦ by simpa using hz i)
    simpa using h
  · intro z hz hmono a b hab
    rcases (hmono hab).lt_or_eq with h | h
    · exact C.curvGrad_le H hz h
    · exact (curvGrad_congr h).ge


end WYD
