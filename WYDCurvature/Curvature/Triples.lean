/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.Quantum.Hypersurface
import WYDCurvature.Dittmann.Reduction

/-!
# Triple sums and the completeness kernel

The contraction lemmas of `PetzCurvature/KuboMori/ScalarCurvature.lean`, and the completeness
kernel of `PetzCurvature/KuboMori/Chart.lean` for a general weighted form `∑ mᵢⱼ Re (Xᵢⱼ Yⱼᵢ)`.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder
open Finset Matrix
open AlphaCurvature.Quantum

namespace WYD

variable {d : Type*} [Fintype d]

/-- The cyclic triple sum `∑ᵢⱼₖ Mᵢⱼₖ Aᵢⱼ Zⱼₖ Bₖᵢ`. -/
def triSum (M : d → d → d → ℂ) (A Z B : Matrix d d ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, M i j k * A i j * Z j k * B k i

/-! ### Contractions with a completeness kernel -/

section Kernel

variable [DecidableEq d] {ι : Type*} [Fintype ι] {e : ι → Matrix d d ℂ} {c : d → d → ℂ}

/-- The cross term of `|T|²`: the three kernels leave all three indices free. -/
theorem sum_triSum_mul_triSum
    (hK : ∀ p q r s, ∑ a, e a p q * e a s r = if p = r ∧ q = s then c r s else 0)
    (M : d → d → d → ℂ) :
    ∑ a, ∑ b, ∑ c', triSum M (e b) (e a) (e c') * triSum M (e b) (e c') (e a) =
      ∑ i, ∑ j, ∑ k, M i j k * M j i k * c j k * c i j * c k i := by
  simp only [triSum, Finset.sum_mul_sum]
  simp only [Finset.sum_comm (s := (univ : Finset ι)) (t := (univ : Finset d))]
  have h : ∀ (a b c' : ι) (i j k i' j' k' : d),
      M i j k * e b i j * e a j k * e c' k i * (M i' j' k' * e b i' j' * e c' j' k' * e a k' i') =
      M i j k * M i' j' k' * (e a j k * e a k' i') * (e b i j * e b i' j') *
        (e c' k i * e c' j' k') := fun _ _ _ _ _ _ _ _ _ ↦ by ring
  simp only [h, ← Finset.mul_sum, ← Finset.sum_mul, hK]
  simp [ite_and, mul_ite, ite_mul]

/-- The square term of `|T|²`: the three kernels force all six indices to coincide. -/
theorem sum_triSum_sq
    (hK : ∀ p q r s, ∑ a, e a p q * e a s r = if p = r ∧ q = s then c r s else 0)
    (M : d → d → d → ℂ) :
    ∑ a, ∑ b, ∑ c', triSum M (e b) (e a) (e c') ^ 2 =
      ∑ i, M i i i * M i i i * c i i * c i i * c i i := by
  simp only [triSum, sq, Finset.sum_mul_sum]
  simp only [Finset.sum_comm (s := (univ : Finset ι)) (t := (univ : Finset d))]
  have h : ∀ (a b c' : ι) (i j k i' j' k' : d),
      M i j k * e b i j * e a j k * e c' k i * (M i' j' k' * e b i' j' * e a j' k' * e c' k' i') =
      M i j k * M i' j' k' * (e a j k * e a j' k') * (e b i j * e b i' j') *
        (e c' k i * e c' k' i') := fun _ _ _ _ _ _ _ _ _ ↦ by ring
  simp only [h, ← Finset.mul_sum, ← Finset.sum_mul, hK]
  simp [ite_and, mul_ite, ite_mul]

/-- The other square term of `|T|²`. -/
theorem sum_triSum_sq'
    (hK : ∀ p q r s, ∑ a, e a p q * e a s r = if p = r ∧ q = s then c r s else 0)
    (M : d → d → d → ℂ) :
    ∑ a, ∑ b, ∑ c', triSum M (e b) (e c') (e a) ^ 2 =
      ∑ i, M i i i * M i i i * c i i * c i i * c i i := by
  simp only [triSum, sq, Finset.sum_mul_sum]
  simp only [Finset.sum_comm (s := (univ : Finset ι)) (t := (univ : Finset d))]
  have h : ∀ (a b c' : ι) (i j k i' j' k' : d),
      M i j k * e b i j * e c' j k * e a k i * (M i' j' k' * e b i' j' * e c' j' k' * e a k' i') =
      M i j k * M i' j' k' * (e a k i * e a k' i') * (e b i j * e b i' j') *
        (e c' j k * e c' j' k') := fun _ _ _ _ _ _ _ _ _ ↦ by ring
  simp only [h, ← Finset.mul_sum, ← Finset.sum_mul, hK]
  simp [ite_and, mul_ite, ite_mul]

/-- The trace of `T` in its outer slots. -/
theorem sum_triSum_self_left
    (hK : ∀ p q r s, ∑ a, e a p q * e a s r = if p = r ∧ q = s then c r s else 0)
    (M : d → d → d → ℂ) (Z : Matrix d d ℂ) :
    ∑ b, triSum M (e b) Z (e b) = ∑ i, ∑ j, M i j j * Z j j * c i j := by
  simp only [triSum, Finset.sum_comm (s := (univ : Finset ι)) (t := (univ : Finset d))]
  have h : ∀ (b : ι) (i j k : d),
      M i j k * e b i j * Z j k * e b k i = M i j k * Z j k * (e b i j * e b k i) :=
    fun _ _ _ _ ↦ by ring
  simp only [h, ← Finset.mul_sum, hK]
  simp [mul_ite]

/-- The trace of `T` in its first two slots. -/
theorem sum_triSum_self_right
    (hK : ∀ p q r s, ∑ a, e a p q * e a s r = if p = r ∧ q = s then c r s else 0)
    (M : d → d → d → ℂ) (Z : Matrix d d ℂ) :
    ∑ b, triSum M (e b) (e b) Z = ∑ i, ∑ j, M i j i * Z i i * c i j := by
  simp only [triSum, Finset.sum_comm (s := (univ : Finset ι)) (t := (univ : Finset d))]
  have h : ∀ (b : ι) (i j k : d),
      M i j k * e b i j * e b j k * Z k i = M i j k * Z k i * (e b i j * e b j k) :=
    fun _ _ _ _ ↦ by ring
  simp only [h, ← Finset.mul_sum, hK]
  simp [mul_ite]

/-- The kernel on the diagonal entries. -/
theorem sum_sq_sum_diag
    (hK : ∀ p q r s, ∑ a, e a p q * e a s r = if p = r ∧ q = s then c r s else 0)
    (w : d → ℂ) :
    ∑ a, (∑ j, w j * e a j j) ^ 2 = ∑ j, w j ^ 2 * c j j := by
  simp only [sq, Finset.sum_mul_sum,
    Finset.sum_comm (s := (univ : Finset ι)) (t := (univ : Finset d))]
  have h : ∀ (a : ι) (i j : d), w i * e a i i * (w j * e a j j) =
      w i * w j * (e a i i * e a j j) := fun _ _ _ ↦ by ring
  simp only [h, ← Finset.mul_sum, hK]
  simp [mul_ite]

end Kernel

/-! ### The BKM derivative as a cyclic sum -/


/-- For Hermitian arguments and a real coefficient tensor symmetric in its first two indices,
`C(A, B, Z)` is the conjugate of `C(A, Z, B)`. -/
theorem star_triSum {M : d → d → d → ℂ} (hM : ∀ i j k, star (M i j k) = M i j k)
    (hM' : ∀ i j k, M j i k = M i j k) {A Z B : Matrix d d ℂ} (hA : A.IsHermitian)
    (hZ : Z.IsHermitian) (hB : B.IsHermitian) : star (triSum M A Z B) = triSum M A B Z := by
  simp only [triSum, star_sum, star_mul', hM, hA.apply, hZ.apply, hB.apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← hM' i j k]
  ring

/-- The cyclic invariance of the triple sum, for a cyclic coefficient tensor. -/
theorem triSum_cyclic {M : d → d → d → ℂ} (hM : ∀ i j k, M j k i = M i j k) (A B C : Matrix d d ℂ) :
    triSum M B C A = triSum M A B C := by
  simp only [triSum]
  rw [← sum_cyclic fun i j k ↦ M i j k * B i j * C j k * A k i]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hM]
  ring

/-! ### The weighted form -/

/-- The weighted form `∑ᵢⱼ mᵢⱼ Re (Xᵢⱼ Yⱼᵢ)`. -/
noncomputable def mform (m : d → d → ℝ) : Matrix d d ℂ →ₗ[ℝ] Matrix d d ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y ↦ ∑ i, ∑ j, m i j * (X i j * Y j i).re)
    (fun X X' Y ↦ by
      simp only [Matrix.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib])
    (fun c X Y ↦ by
      simp only [Matrix.smul_apply, Complex.real_smul, mul_assoc, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Complex.re_ofReal_mul]
      ring)
    (fun X Y Y' ↦ by
      simp only [Matrix.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib])
    (fun c X Y ↦ by
      simp only [Matrix.smul_apply, Complex.real_smul, mul_left_comm _ (c : ℂ),
        Complex.re_ofReal_mul, smul_eq_mul, Finset.mul_sum, mul_left_comm _ c])

theorem mform_apply (m : d → d → ℝ) (X Y : Matrix d d ℂ) :
    mform m X Y = ∑ i, ∑ j, m i j * (X i j * Y j i).re := rfl

theorem mform_comm {m : d → d → ℝ} (hm : ∀ i j, m i j = m j i) (X Y : Matrix d d ℂ) :
    mform m X Y = mform m Y X := by
  rw [mform_apply, mform_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hm j i, mul_comm (X j i)]

variable [DecidableEq d]

theorem mform_single_add {m : d → d → ℝ} (hm : ∀ i j, m i j = m j i) {E : Matrix d d ℂ}
    (hE : E.IsHermitian) (r s : d) :
    mform m E (single r s 1 + single s r 1) = 2 * m r s * (E r s).re := by
  rw [mform_apply]
  simp only [Matrix.add_apply, Matrix.single_apply, mul_add, Complex.add_re, mul_ite, mul_one,
    mul_zero, ite_and, apply_ite Complex.re, Complex.zero_re, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← hE.apply s r, Complex.star_def, Complex.conj_re, hm s r]
  ring

theorem mform_single_sub {m : d → d → ℝ} (hm : ∀ i j, m i j = m j i) {E : Matrix d d ℂ}
    (hE : E.IsHermitian) (r s : d) :
    mform m E (single r s Complex.I - single s r Complex.I) = 2 * m r s * (E r s).im := by
  rw [mform_apply]
  simp only [Matrix.sub_apply, Matrix.single_apply, mul_sub, Complex.sub_re, mul_ite,
    mul_zero, ite_and, apply_ite Complex.re, Complex.zero_re, Complex.mul_I_re,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← hE.apply s r, Complex.star_def, Complex.conj_im, hm s r]
  ring

/-- A family of Hermitian matrices in which every Hermitian matrix expands by its coefficients in
the weighted form. -/
structure IsFrame {κ : Type*} [Fintype κ] (m : d → d → ℝ) (e : κ → Matrix d d ℂ) : Prop where
  herm : ∀ a, (e a).IsHermitian
  expand : ∀ X : Matrix d d ℂ, X.IsHermitian → X = ∑ a, mform m (e a) X • e a

variable {κ : Type*} [Fintype κ] {m : d → d → ℝ} {e : κ → Matrix d d ℂ}

omit [DecidableEq d] in
theorem IsFrame.apply (F : IsFrame m e) {X : Matrix d d ℂ} (hX : X.IsHermitian) (p q : d) :
    X p q = ∑ a, (mform m (e a) X : ℂ) * e a p q := by
  have := congrArg (fun Y : Matrix d d ℂ ↦ Y p q) (F.expand X hX)
  simpa only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul] using this

omit [DecidableEq d] in
/-- Parseval's identity. -/
theorem IsFrame.parseval (F : IsFrame m e) (hs : ∀ i j, m i j = m j i) {X : Matrix d d ℂ}
    (hX : X.IsHermitian) (Y : Matrix d d ℂ) :
    mform m X Y = ∑ a, mform m X (e a) * mform m Y (e a) := by
  conv_lhs => rw [F.expand X hX]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mform_comm hs (e a) X, mform_comm hs (e a) Y]

/-- **The completeness kernel** `∑ₐ (eₐ)ₚq (eₐ)ₛᵣ = δₚᵣ δqₛ / mᵣₛ`. -/
theorem IsFrame.completeness (F : IsFrame m e) (hs : ∀ i j, m i j = m j i) (hpos : ∀ i j, 0 < m i j)
    (p q r s : d) :
    ∑ a, e a p q * e a s r = if p = r ∧ q = s then (((m r s)⁻¹ : ℝ) : ℂ) else 0 := by
  have hm : (m r s : ℂ) ≠ 0 := by exact_mod_cast (hpos r s).ne'
  have hE : ∀ a, (e a).IsHermitian := F.herm
  have hX1 : (single r s 1 + single s r 1 : Matrix d d ℂ).IsHermitian := by
    simp [IsHermitian, conjTranspose_single, add_comm]
  have hX2 : (single r s Complex.I - single s r Complex.I : Matrix d d ℂ).IsHermitian := by
    rw [IsHermitian, conjTranspose_sub, conjTranspose_single, conjTranspose_single,
      Complex.star_def, Complex.conj_I, ← Matrix.single_neg, ← Matrix.single_neg]
    abel
  have h1 : (single r s 1 + single s r 1 : Matrix d d ℂ) p q =
      ∑ a, ((2 * m r s * (e a r s).re : ℝ) : ℂ) * e a p q := by
    rw [F.apply hX1]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [mform_single_add hs (hE a)]
  have h2 : (single r s Complex.I - single s r Complex.I : Matrix d d ℂ) p q =
      ∑ a, ((2 * m r s * (e a r s).im : ℝ) : ℂ) * e a p q := by
    rw [F.apply hX2]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [mform_single_sub hs (hE a)]
  have hconj : ∀ a, e a s r =
      ((e a r s).re : ℂ) - ((e a r s).im : ℂ) * Complex.I :=
    fun a ↦ by
      rw [← (hE a).apply s r]
      apply Complex.ext <;> simp
  have key : ∑ a, e a p q * e a s r =
      ((single r s 1 + single s r 1 : Matrix d d ℂ) p q -
        Complex.I * (single r s Complex.I - single s r Complex.I : Matrix d d ℂ) p q) /
          (2 * m r s) := by
    rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hconj a]
    field_simp
    push_cast
    ring_nf
  rw [key]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply]
  by_cases h1 : r = p ∧ s = q
  · obtain ⟨rfl, rfl⟩ := h1
    by_cases h2 : s = r
    · subst h2
      simp only [and_self, ite_true]
      push_cast
      field_simp
      ring
    · simp only [and_self, ite_true, h2, Ne.symm h2, ite_false]
      push_cast
      field_simp
      linear_combination (-1 : ℂ) * Complex.I_sq
  · have h1' : ¬(p = r ∧ q = s) := fun h ↦ h1 ⟨h.1.symm, h.2.symm⟩
    simp only [h1, h1', ite_false, zero_add, zero_sub]
    by_cases h2 : s = p ∧ r = q
    · simp only [h2, and_self, ite_true]
      rw [div_eq_zero_iff]
      left
      linear_combination Complex.I_sq
    · simp [h2]


end WYD
