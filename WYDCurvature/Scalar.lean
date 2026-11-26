/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Curvature
import WYDCurvature.Reduction

/-!
# The closed form of the WYD scalar curvature

`scalarCurvature_wydMetric_diagonal`: at a diagonal state of `n` levels
`S = ∑ᵢⱼₖ hs_β(lᵢ, lⱼ, lₖ) - ∑ᵢ hs_β(lᵢ, lᵢ, lᵢ) + (n² - 1)(n² - 2)/4`;
`scalarCurvature_wydMetric`: the same at any faithful state, in the eigenvalues.
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set
open AlphaCurvature AlphaCurvature.Curvature AlphaCurvature.Quantum

namespace WYD

variable {d : Type*} [Fintype d] [DecidableEq d] {β : ℝ} {l : d → ℝ}

/-! ### The metric -/

/-- The metric at a diagonal state, in logarithmic coordinates. -/
theorem wydMetric_diag (hl : ∀ i, 0 < l i) (h0 : β ≠ 0) (h1 : β ≠ 1)
    (u w : tracelessHermitian d) :
    wydMetric β (tracelessHermitian d) (diagS l) 0 u w = mform (lm β l) (lX l u) (lX l w) := by
  rw [wydMetric, pullback_apply, fderiv_wydChart_diag hl, fderiv_wydChart_diag hl,
    wydPairing_lA h0 h1, mform_comm lm_comm (lX l w)]
  ring

theorem lX_injective (hl : ∀ i, 0 < l i) {w : tracelessHermitian d} (h : lX l w = 0) : w = 0 := by
  apply Subtype.ext
  ext i j
  rw [← e1_mul_lX hl, h]
  simp

omit [DecidableEq d] in
theorem mform_self_pos {Y : Matrix d d ℂ} (hY : Y.IsHermitian) (h : Y ≠ 0) :
    0 < mform (lm β l) Y Y := by
  obtain ⟨i, j, hij⟩ : ∃ i j, Y i j ≠ 0 := by
    by_contra! h'
    exact h (Matrix.ext h')
  have ht : ∀ i j, lm β l i j * (Y i j * Y j i).re = lm β l i j * Complex.normSq (Y i j) := by
    intro i j
    rw [← hY.apply j i, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  rw [mform_apply]
  simp only [ht]
  refine Finset.sum_pos' (fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (lm_pos i j).le (Complex.normSq_nonneg _)) ⟨i, Finset.mem_univ _, ?_⟩
  exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (lm_pos i j).le (Complex.normSq_nonneg _))
    ⟨j, Finset.mem_univ _, mul_pos (lm_pos i j) (Complex.normSq_pos.2 hij)⟩

theorem wydMetric_diag_self_pos (hl : ∀ i, 0 < l i) (h0 : β ≠ 0) (h1 : β ≠ 1)
    {u : tracelessHermitian d} (hu : u ≠ 0) :
    0 < wydMetric β (tracelessHermitian d) (diagS l) 0 u u := by
  rw [wydMetric_diag hl h0 h1]
  exact mform_self_pos (lX_isHermitian hl u) fun h ↦ hu (lX_injective hl h)

theorem wydMetric_comm (ρ : Matrix d d ℂ) (z u w : tracelessHermitian d) :
    wydMetric β (tracelessHermitian d) ρ z u w = wydMetric β (tracelessHermitian d) ρ z w u :=
  pullback_const_comm (wydPairing_comm β) z u w

/-! ### The frame -/

theorem lX_sum {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (b : ι → tracelessHermitian d) : lX l (∑ i, c i • b i) = ∑ i, c i • lX l (b i) := by
  simp only [lX, map_sum, map_smul]

/-- Every Hermitian matrix orthogonal to `1` is `lX` of a tangent vector. -/
theorem exists_lX_eq (hl : ∀ i, 0 < l i) {Y : Matrix d d ℂ} (hY : Y.IsHermitian)
    (h : mform (lm β l) Y 1 = 0) : ∃ w, lX l w = Y := by
  set v : Matrix d d ℂ := Matrix.of fun i j ↦
    (e1 (Real.log (l i)) (Real.log (l j)) : ℂ) * Y i j with hv
  have hvH : v.IsHermitian := Matrix.IsHermitian.ext fun i j ↦ by
    rw [hv, Matrix.of_apply, Matrix.of_apply, star_mul', hY.apply, e1_comm]
    simp
  have hvt : v.trace = 0 := by
    have hd : ∀ i, v i i = ((l i * (Y i i).re : ℝ) : ℂ) := fun i ↦ by
      have hre : Y i i = ((Y i i).re : ℂ) := by
        have := hY.apply i i
        rw [Complex.star_def, Complex.conj_eq_iff_re] at this
        exact this.symm
      rw [hv, Matrix.of_apply, e1_self, Real.exp_log (hl i)]
      conv_lhs => rw [hre]
      push_cast
      rfl
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, hd, ← Complex.ofReal_sum]
    rw [← mform_one (β := β) hl, h, Complex.ofReal_zero]
  refine ⟨⟨v, mem_tracelessHermitian.2 ⟨hvH, hvt⟩⟩, ?_⟩
  ext i j
  have he : (e1 (Real.log (l i)) (Real.log (l j)) : ℂ) ≠ 0 := by
    exact_mod_cast (e1_pos _ _).ne'
  apply mul_left_cancel₀ he
  rw [e1_mul_lX hl]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The frame of Hermitian matrices: the unit normal `1` and a tangent basis. -/
noncomputable def frame (l : d → ℝ) (b : ι → tracelessHermitian d) (o : Option ι) : Matrix d d ℂ :=
  o.elim 1 fun i ↦ lX l (b i)

theorem isFrame_frame (hl : ∀ i, 0 < l i) (htr : ∑ i, l i = 1) (h0 : β ≠ 0) (h1 : β ≠ 1)
    (b : Module.Basis ι ℝ (tracelessHermitian d))
    (hb : ∀ i j, wydMetric β (tracelessHermitian d) (diagS l) 0 (b i) (b j) =
      if i = j then 1 else 0) : IsFrame (lm β l) (frame l b) := by
  constructor
  · rintro (_ | i)
    · exact Matrix.isHermitian_one
    · exact lX_isHermitian hl _
  · intro Y hY
    set t := mform (lm β l) Y 1 with ht
    have hY' : (Y - t • (1 : Matrix d d ℂ)).IsHermitian :=
      mem_hermitian.1 ((hermitian d).sub_mem (mem_hermitian.2 hY)
        ((hermitian d).smul_mem t (mem_hermitian.2 Matrix.isHermitian_one)))
    obtain ⟨w, hw⟩ := exists_lX_eq (β := β) hl hY' (by
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, mform_one_one hl htr,
        smul_eq_mul, mul_one, ← ht, sub_self])
    have hc : ∀ i, b.repr w i = mform (lm β l) (lX l (b i)) Y := fun i ↦ by
      rw [repr_eq_of_orthonormal (G := wydMetric β (tracelessHermitian d) (diagS l)) (x := 0) b hb,
        wydMetric_diag hl h0 h1, hw, map_sub, map_smul, mform_lX_one hl, smul_zero, sub_zero]
    have hsum : lX l w = ∑ i, mform (lm β l) (lX l (b i)) Y • lX l (b i) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [lX_sum]
      simp only [hc]
    rw [Fintype.sum_option]
    simp only [frame, Option.elim]
    rw [← hsum, hw, mform_comm lm_comm, ← ht]
    abel

/-- The frame has `n²` members. -/
theorem card_frame (hl : ∀ i, 0 < l i) (htr : ∑ i, l i = 1) (h0 : β ≠ 0) (h1 : β ≠ 1)
    (b : Module.Basis ι ℝ (tracelessHermitian d))
    (hb : ∀ i j, wydMetric β (tracelessHermitian d) (diagS l) 0 (b i) (b j) =
      if i = j then 1 else 0) : (Fintype.card ι : ℝ) = (Fintype.card d : ℝ) ^ 2 - 1 := by
  have F := isFrame_frame hl htr h0 h1 b hb
  have hone : ∀ o, mform (lm β l) (frame l b o) (frame l b o) = 1 := by
    rintro (_ | i)
    · exact mform_one_one hl htr
    · have := hb i i
      rw [wydMetric_diag hl h0 h1] at this
      exact this.trans (by simp)
  have h2 : ∑ o, mform (lm β l) (frame l b o) (frame l b o) = (Fintype.card d : ℝ) ^ 2 := by
    simp only [mform_apply]
    rw [Finset.sum_comm]
    have hi : ∀ i : d, ∑ o, ∑ j, lm β l i j * (frame l b o i j * frame l b o j i).re =
        (Fintype.card d : ℝ) := by
      intro i
      rw [Finset.sum_comm]
      have : ∀ j : d, ∑ o, lm β l i j * (frame l b o i j * frame l b o j i).re = 1 := fun j ↦ by
        rw [← Finset.mul_sum, ← Complex.re_sum, F.completeness lm_comm lm_pos i j i j]
        simp only [and_self, ite_true, Complex.ofReal_re]
        exact mul_inv_cancel₀ (lm_pos i j).ne'
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sq]
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_option, nsmul_eq_mul,
    mul_one] at h2
  push_cast at h2
  linarith

/-! ### The sum over the tangent basis and over the frame -/

omit [DecidableEq d] in
theorem mform_lN_symm {X Y Z : Matrix d d ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hZ : Z.IsHermitian) :
    mform (lm β l) (lN β l X Y) Z = mform (lm β l) (lN β l X Z) Y := by
  apply Complex.ofReal_injective
  rw [lN, lN, mform_kerMat lC_comm₁₂ lC_comm₂₃ lm_pos hX hY hZ,
    mform_kerMat lC_comm₁₂ lC_comm₂₃ lm_pos hX hZ hY]
  have hc := triSum_cyclic (M := fun i j k ↦ (lC β l i j k : ℂ))
    (fun i j k ↦ by rw [lC_comm₂₃, lC_comm₁₂, lC_comm₂₃])
  rw [hc Z Y X, hc Y Z X, add_comm]

theorem sum_frame_eq (hl : ∀ i, 0 < l i) (htr : ∑ i, l i = 1) (h0 : β ≠ 0) (h1 : β ≠ 1)
    (b : Module.Basis ι ℝ (tracelessHermitian d))
    (hb : ∀ i j, wydMetric β (tracelessHermitian d) (diagS l) 0 (b i) (b j) =
      if i = j then 1 else 0) :
    ∑ i, ∑ j, mform (lm β l) (lN β l (lX l (b i)) (lX l (b j))) (lN β l (lX l (b i)) (lX l (b j))) -
        ∑ i, ∑ j, mform (lm β l) (lN β l (lX l (b i)) (lX l (b i)))
          (lN β l (lX l (b j)) (lX l (b j))) =
      ∑ o, ∑ o', mform (lm β l) (lN β l (frame l b o) (frame l b o'))
          (lN β l (frame l b o) (frame l b o')) -
        ∑ o, ∑ o', mform (lm β l) (lN β l (frame l b o) (frame l b o))
          (lN β l (frame l b o') (frame l b o')) := by
  have hX := fun i ↦ lX_isHermitian hl (b i)
  have hXX : ∀ i, mform (lm β l) (lX l (b i)) (lX l (b i)) = 1 := fun i ↦ by
    rw [← wydMetric_diag hl h0 h1, hb]; simp
  have hcomm : ∀ Y Z, lN β l Y Z = lN β l Z Y := fun Y Z ↦ kerMat_comm _ _ _
  have hN1 : ∀ i, mform (lm β l) (lN β l (lX l (b i)) (lX l (b i))) 1 = 2 * β - 1 := fun i ↦ by
    rw [mform_lN_symm (hX i) (hX i) Matrix.isHermitian_one, hcomm, lN_one, map_smul,
      LinearMap.smul_apply, hXX, smul_eq_mul, mul_one]
  simp only [Fintype.sum_option, frame, Option.elim]
  simp only [hcomm _ 1, lN_one, map_smul, LinearMap.smul_apply, smul_eq_mul, hXX,
    mform_one_one hl htr, hN1, mform_comm lm_comm 1 (lN _ _ _ _), Finset.sum_add_distrib]
  ring_nf

/-- **The closed form at a diagonal state.** -/
theorem scalarCurvature_wydMetric_diagonal (hl : ∀ i, 0 < l i) (htr : ∑ i, l i = 1) (h0 : β ≠ 0)
    (h1 : β ≠ 1) :
    scalarCurvature (wydMetric β (tracelessHermitian d) (diagS l)) 0 =
      curvSum (wydHs β) l +
        ((Fintype.card d : ℝ) ^ 2 - 1) * ((Fintype.card d : ℝ) ^ 2 - 2) / 4 := by
  have hD := posDef_diagonal_ofReal hl
  have hpos : ∀ u : tracelessHermitian d, u ≠ 0 →
      0 < wydMetric β (tracelessHermitian d) (diagS l) 0 u u :=
    fun u hu ↦ wydMetric_diag_self_pos hl h0 h1 hu
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (wydMetric β (tracelessHermitian d) (diagS l) 0)
    (wydMetric_comm _ 0) hpos
  have F := isFrame_frame hl htr h0 h1 b hb
  have hcard := card_frame hl htr h0 h1 b hb
  have hS := scalarCurvature_of_split (φ := wydChart β (tracelessHermitian d) (diagS l))
    (B := wydPairing β) (x := 0) (contDiffAt_wydChart hD 3) (wydPairing_comm β)
    (LinearMap.BilinForm.isInvertible_of_pos hpos) b hb
    (fun Y Z ↦ mform (lm β l) Y Z) (lX l) (lΓ β l) (fun v w ↦ lN β l (lX l v) (lX l w)) 1
    (fun u w ↦ wydMetric_diag hl h0 h1 u w)
    (fun v w v' w' ↦ by
      rw [fderiv_fderiv_wydChart_diag hl, fderiv_fderiv_wydChart_diag hl, wydPairing_lA h0 h1,
        split_left hl, split_right hl, split_left hl, split_right hl]
      have c1 := mform_comm (lm_comm (β := β) (l := l)) (lΓ β l v' w') (lΓ β l v w)
      have c2 := mform_comm (lm_comm (β := β) (l := l)) (lN β l (lX l v') (lX l w')) (lΓ β l v w)
      have c3 := mform_comm (lm_comm (β := β) (l := l)) (lN β l (lX l v') (lX l w'))
        (lN β l (lX l v) (lX l w))
      have c4 := mform_comm (lm_comm (β := β) (l := l)) (lΓ β l v' w') (lN β l (lX l v) (lX l w))
      simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, c1, c2, c3, c4]
      ring)
    (fun v w u ↦ by
      rw [fderiv_fderiv_wydChart_diag hl, fderiv_wydChart_diag hl, wydPairing_lA h0 h1,
        split_left hl, split_right hl, mform_comm lm_comm (lX l u)]
      simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun v w ↦ mform_lΓ_one hl v w)
    (fun v w v' w' ↦ by
      rw [F.parseval lm_comm (lΓ_isHermitian hl v w), Fintype.sum_option]
      rfl)
  rw [← wydMetric] at hS
  rw [hS, sum_frame_eq hl htr h0 h1 b hb, hcard]
  simp only [lN]
  rw [sum_frame F lm_comm lm_pos lC_comm₁₂ lC_comm₂₃]
  have e1 : curvSum (wydHs β) l = ∑ i, ∑ j, ∑ k, curvK β (Real.log (l i)) (Real.log (l j))
      (Real.log (l k)) - ∑ i, curvK β (Real.log (l i)) (Real.log (l i)) (Real.log (l i)) := by
    rw [curvSum]
    simp only [wydHs, hsL]
    congr 1
    · simp only [← Finset.sum_div, Finset.sum_add_distrib]
      have k1 := sum_cyclic fun i j k ↦ curvK β (Real.log (l i)) (Real.log (l j)) (Real.log (l k))
      have k2 := sum_cyclic fun i j k ↦ curvK β (Real.log (l k)) (Real.log (l i)) (Real.log (l j))
      rw [k1, ← k2]
      ring
    · exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e2 : ∑ i, curvK β (Real.log (l i)) (Real.log (l i)) (Real.log (l i)) =
      -(∑ i, lC β l i i i ^ 2 * (lm β l i i)⁻¹ ^ 3) / 2 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := (lm_pos (β := β) (l := l) i i).ne'
    rw [curvK, lC]
    rw [lm] at this ⊢
    field_simp
    ring
  have e3 : ∑ i, ∑ j, ∑ k, curvK β (Real.log (l i)) (Real.log (l j)) (Real.log (l k)) =
      (∑ i, ∑ j, ∑ k, lC β l i j k ^ 2 *
        ((lm β l i j)⁻¹ * (lm β l j k)⁻¹ * (lm β l k i)⁻¹)) / 2 -
      ∑ j, (∑ i, lC β l i j j * (lm β l i j)⁻¹) ^ 2 * (lm β l j j)⁻¹ := by
    simp only [curvK, Finset.sum_sub_distrib]
    congr 1
    · simp only [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
        Finset.sum_congr rfl fun k _ ↦ ?_
      have a1 := (lm_pos (β := β) (l := l) i j).ne'
      have a2 := (lm_pos (β := β) (l := l) j k).ne'
      have a3 := (lm_pos (β := β) (l := l) k i).ne'
      simp only [lC, lm] at *
      field_simp
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have a1 := (lm_pos (β := β) (l := l) i j).ne'
      have a2 := (lm_pos (β := β) (l := l) i k).ne'
      have a3 := (lm_pos (β := β) (l := l) i i).ne'
      rw [lm_comm j i, lm_comm k i, ← lC_comm₁₂ j i i, lC_comm₂₃ i i j, ← lC_comm₁₂ k i i,
        lC_comm₂₃ i i k]
      simp only [lC, lm] at *
      field_simp
  rw [e1, e2, e3]
  ring

end WYD
