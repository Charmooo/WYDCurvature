/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Curvature.Triples

/-!
# Contractions of a symmetric cubic kernel in a frame

For a symmetric real tensor `C` and a symmetric positive weight `m`, the bilinear map
`N(X, Y)ᵢⱼ = ∑ₖ (Cᵢₖⱼ/mᵢⱼ)(Xᵢₖ Yₖⱼ + Yᵢₖ Xₖⱼ)` has `⟨N(X, Y), Z⟩ = C(Y, X, Z) + C(Y, Z, X)` (cyclic
triple sums), and its contractions in an orthonormal frame are explicit sums over the indices.
-/

open Finset Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace WYD

variable {d : Type*} [Fintype d]

/-- The bilinear map of a kernel: `∑ₖ qᵢₖⱼ (Xᵢₖ Yₖⱼ + Yᵢₖ Xₖⱼ)`. -/
noncomputable def kerMat (q : d → d → d → ℝ) (X Y : Matrix d d ℂ) : Matrix d d ℂ :=
  Matrix.of fun i j ↦ ∑ k, (q i k j : ℂ) * (X i k * Y k j + Y i k * X k j)

theorem kerMat_apply (q : d → d → d → ℝ) (X Y : Matrix d d ℂ) (i j : d) :
    kerMat q X Y i j = ∑ k, (q i k j : ℂ) * (X i k * Y k j + Y i k * X k j) := rfl

theorem kerMat_comm (q : d → d → d → ℝ) (X Y : Matrix d d ℂ) : kerMat q X Y = kerMat q Y X := by
  ext i j
  simp only [kerMat_apply, add_comm]

theorem kerMat_isHermitian {q : d → d → d → ℝ} (hq : ∀ i k j, q i k j = q j k i)
    {X Y : Matrix d d ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (kerMat q X Y).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j ↦ ?_
  simp only [kerMat_apply, star_sum, star_mul', star_add, hX.apply, hY.apply, Complex.star_def,
    Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hq]
  ring

variable {C : d → d → d → ℝ} {m : d → d → ℝ}

/-- `⟨N(X, Y), Z⟩` as cyclic triple sums. -/
theorem mform_kerMat (hC₁ : ∀ i j k, C j i k = C i j k) (hC₂ : ∀ i j k, C i k j = C i j k)
    (hpos : ∀ i j, 0 < m i j) {X Y Z : Matrix d d ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hZ : Z.IsHermitian) :
    ((mform m (kerMat (fun i k j ↦ C i k j / m i j) X Y) Z : ℝ) : ℂ) =
      triSum (fun i j k ↦ (C i j k : ℂ)) Y X Z + triSum (fun i j k ↦ (C i j k : ℂ)) Y Z X := by
  have hs : star (triSum (fun i j k ↦ (C i j k : ℂ)) Y X Z) =
      triSum (fun i j k ↦ (C i j k : ℂ)) Y Z X :=
    star_triSum (fun _ _ _ ↦ Complex.conj_ofReal _) (fun i j k ↦ by rw [hC₁]) hY hX hZ
  have hcyc : triSum (fun i j k ↦ (C i j k : ℂ)) Y Z X =
      triSum (fun i j k ↦ (C i j k : ℂ)) X Y Z :=
    triSum_cyclic (fun i j k ↦ by rw [hC₂, hC₁, hC₂]) X Y Z
  have hre : mform m (kerMat (fun i k j ↦ C i k j / m i j) X Y) Z =
      (triSum (fun i j k ↦ (C i j k : ℂ)) X Y Z).re +
        (triSum (fun i j k ↦ (C i j k : ℂ)) Y X Z).re := by
    rw [mform_apply]
    simp only [triSum, Complex.re_sum, ← Finset.sum_add_distrib, kerMat_apply, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have hm := (hpos i j).ne'
    rw [mul_assoc, Complex.re_ofReal_mul, mul_assoc, mul_assoc, mul_assoc, mul_assoc,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, add_mul, Complex.add_re, mul_assoc, mul_assoc]
    field_simp
  rw [hre, ← hcyc, ← hs, Complex.star_def, Complex.conj_re, Complex.add_conj]
  push_cast
  ring

variable [DecidableEq d] {κ : Type*} [Fintype κ] {e : κ → Matrix d d ℂ}

/-- `∑ ⟨N(eₐ, e_b), e_c⟩²`. -/
theorem sum_mform_sq (F : IsFrame m e) (hm : ∀ i j, m i j = m j i) (hpos : ∀ i j, 0 < m i j)
    (hC₁ : ∀ i j k, C j i k = C i j k) (hC₂ : ∀ i j k, C i k j = C i j k) :
    ∑ a, ∑ b, ∑ c, mform m (kerMat (fun i k j ↦ C i k j / m i j) (e a) (e b)) (e c) ^ 2 =
      2 * ∑ i, C i i i ^ 2 * (m i i)⁻¹ ^ 3 +
        2 * ∑ i, ∑ j, ∑ k, C i j k ^ 2 * ((m i j)⁻¹ * (m j k)⁻¹ * (m k i)⁻¹) := by
  have hK := F.completeness hm hpos
  apply Complex.ofReal_injective
  push_cast
  simp only [mform_kerMat hC₁ hC₂ hpos (F.herm _) (F.herm _) (F.herm _)]
  have h : ∀ X Y : ℂ, (X + Y) ^ 2 = X ^ 2 + Y ^ 2 + 2 * (X * Y) := fun _ _ ↦ by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_triSum_sq hK, sum_triSum_sq' hK, sum_triSum_mul_triSum hK, ← two_mul]
  refine congrArg₂ (· + ·) (congrArg (2 * ·) ?_) (congrArg (2 * ·) ?_)
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Complex.ofReal_inv]
    ring
  · refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hC₁ i j k]
    simp only [Complex.ofReal_inv]
    ring

/-- `∑_c (∑ₐ ⟨N(eₐ, eₐ), e_c⟩)²`. -/
theorem sum_sum_mform_sq (F : IsFrame m e) (hm : ∀ i j, m i j = m j i) (hpos : ∀ i j, 0 < m i j)
    (hC₁ : ∀ i j k, C j i k = C i j k) (hC₂ : ∀ i j k, C i k j = C i j k) :
    ∑ c, (∑ a, mform m (kerMat (fun i k j ↦ C i k j / m i j) (e a) (e a)) (e c)) ^ 2 =
      4 * ∑ j, (∑ i, C i j j * (m i j)⁻¹) ^ 2 * (m j j)⁻¹ := by
  have hK := F.completeness hm hpos
  simp only [Complex.ofReal_inv] at hK
  apply Complex.ofReal_injective
  push_cast
  simp only [mform_kerMat hC₁ hC₂ hpos (F.herm _) (F.herm _) (F.herm _), Finset.sum_add_distrib,
    sum_triSum_self_left hK, sum_triSum_self_right hK]
  have hτ : ∀ Z : Matrix d d ℂ, ∑ i, ∑ j, (C i j i : ℂ) * Z i i * ((m i j : ℂ))⁻¹ +
      ∑ i, ∑ j, (C i j j : ℂ) * Z j j * ((m i j : ℂ))⁻¹ =
      ∑ j, (2 * ∑ i, (C i j j : ℂ) * ((m i j : ℂ))⁻¹) * Z j j := by
    intro Z
    rw [Finset.sum_comm (f := fun i j ↦ (C i j j : ℂ) * Z j j * ((m i j : ℂ))⁻¹),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hC₁ j i j, hC₂, hm j i]
    ring
  simp only [hτ, sum_sq_sum_diag hK, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.mul_sum]
  ring

/-- **The contraction** `∑ₐ_b (|N(eₐ, e_b)|² - ⟨N(eₐ, eₐ), N(e_b, e_b)⟩)`. -/
theorem sum_frame (F : IsFrame m e) (hm : ∀ i j, m i j = m j i) (hpos : ∀ i j, 0 < m i j)
    (hC₁ : ∀ i j k, C j i k = C i j k) (hC₂ : ∀ i j k, C i k j = C i j k) :
    ∑ a, ∑ b, mform m (kerMat (fun i k j ↦ C i k j / m i j) (e a) (e b))
        (kerMat (fun i k j ↦ C i k j / m i j) (e a) (e b)) -
      ∑ a, ∑ b, mform m (kerMat (fun i k j ↦ C i k j / m i j) (e a) (e a))
        (kerMat (fun i k j ↦ C i k j / m i j) (e b) (e b)) =
      2 * ∑ i, C i i i ^ 2 * (m i i)⁻¹ ^ 3 +
        2 * ∑ i, ∑ j, ∑ k, C i j k ^ 2 * ((m i j)⁻¹ * (m j k)⁻¹ * (m k i)⁻¹) -
      4 * ∑ j, (∑ i, C i j j * (m i j)⁻¹) ^ 2 * (m j j)⁻¹ := by
  have hH : ∀ a b, (kerMat (fun i k j ↦ C i k j / m i j) (e a) (e b)).IsHermitian := fun a b ↦
    kerMat_isHermitian (fun i k j ↦ by rw [hm j i, ← hC₁ j k i, hC₂, hC₁ , hC₂, hC₁]) (F.herm a) (F.herm b)
  rw [← sum_mform_sq F hm hpos hC₁ hC₂, ← sum_sum_mform_sq F hm hpos hC₁ hC₂]
  congr 1
  · refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    rw [F.parseval hm (hH a b)]
    simp only [sq]
  · have : ∀ a b, mform m (kerMat (fun i k j ↦ C i k j / m i j) (e a) (e a))
        (kerMat (fun i k j ↦ C i k j / m i j) (e b) (e b)) = _ := fun a b ↦
      F.parseval hm (hH a a) _
    simp only [this, sq, Finset.sum_mul_sum]
    have hc : ∀ f : κ → κ → κ → ℝ, ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := fun f ↦ by
      rw [Finset.sum_comm (f := fun c a ↦ ∑ b, f a b c)]
      exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
    exact hc _

end WYD
