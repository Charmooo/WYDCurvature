/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Petz.KuboMori.Chart

/-!
# The scalar curvature of the BKM metric at a diagonal state

The second half of Dittmann's Theorem 2: the scalar curvature of the BKM metric at a
diagonal positive matrix `ρ = diag(l)`, as an explicit sum over triples of eigenvalues, and in
Dittmann's form (58) with his function `hs` (61).

The scalar curvature is `¼ (|T|² - |τ|²)` in any `G_ρ`-orthonormal basis `e` of the Hermitian
matrices (`scalarCurvature_bkmChart_eq_contr`), with `T = DG_ρ`. For Hermitian arguments
`T(Z, A, B) = -(C(A, Z, B) + C(A, B, Z))`, where `C` is the cyclic triple sum with coefficients
`m(lᵢ, lⱼ, lₖ)` and `C(A, B, Z)` is the conjugate of `C(A, Z, B)`. Expanding the squares, every
sum over the basis is a product of copies of the completeness kernel
`∑ₐ (eₐ)ₚq (eₐ)ₛᵣ = δₚᵣ δqₛ / m(lₚ, lq)` (`sum_mul_of_orthonormal`), which collapses the index
sums. No basis is ever written down.

Dittmann writes (58) with a summand `d` of his own (57). The summand `K` here is a different
function with the same cyclic symmetrization `hs`. Since a sum over all triples does not see a
cyclic relabeling, only `hs` matters, and Theorem 2 is stated with `hs` in place of his `d`.

## Main definitions

* `PetzCurvature.triSum M A Z B`: the cyclic triple sum `∑ᵢⱼₖ Mᵢⱼₖ Aᵢⱼ Zⱼₖ Bₖᵢ`.
* `PetzCurvature.bkmCoeff l`: the coefficient tensor `m(lᵢ, lⱼ, lₖ)`.
* `PetzCurvature.bkmSummand x y z`: the summand
  `K = m(x, y, z)² / (2 m(x, y) m(y, z) m(z, x)) - x m(x, x, y) m(x, x, z) / (m(x, y) m(x, z))`.
* `PetzCurvature.bkmHs`: its cyclic symmetrization `hs`, defined at every positive
  argument; `PetzCurvature.dittmannHs`: Dittmann's closed form (61) in logarithms.
* `PetzCurvature.unitaryConjL`, `PetzCurvature.tracelessConj`: conjugation
  `A ↦ U A U*` by a unitary, on all matrices and on the traceless Hermitian ones.

## Main statements

* `PetzCurvature.sum_triSum_mul_triSum`, `PetzCurvature.sum_triSum_sq`,
  `PetzCurvature.sum_triSum_self_left`, …: contractions of cyclic sums with any family
  `e` satisfying a completeness relation `∑ₐ (eₐ)ₚq (eₐ)ₛᵣ = δₚᵣ δqₛ cₚq`.
* `PetzCurvature.fderiv_bkmForm_diagonal_eq_triSum`: `DG = -(C(A, Z, B) + C(A, B, Z))`.
* `PetzCurvature.bkmContrT_diagonal`, `PetzCurvature.bkmContrTau_diagonal`: `|T|²`
  and `|τ|²` in closed form; `τ(Z) = -2 ∑ⱼ wⱼ Zⱼⱼ`, `wⱼ = ∑ᵢ m(lᵢ, lⱼ, lⱼ) / m(lᵢ, lⱼ)`.
* `PetzCurvature.scalarCurvature_bkmChart_hermitian_eq`: on all Hermitian directions,
  `S = ∑_{[n]³} K(lᵢ, lⱼ, lₖ) + ∑ᵢ 1/(8 lᵢ)`.
* `PetzCurvature.scalarCurvature_bkmChart_tracelessHermitian_eq_sum`: on the density
  matrices, `S = ∑_{[n]³} K(lᵢ, lⱼ, lₖ) + ∑ᵢ 1/(8 lᵢ) + (n² - 1)(n² - 2)/4`.
* `PetzCurvature.bkmHs_eq_dittmannHs`, `PetzCurvature.bkmHs_self`: the cyclic
  symmetrization `hs` of `K` is Dittmann's closed form (61) at pairwise distinct arguments, and
  `hs(x, x, x) = -1/(8x)`.
* `PetzCurvature.scalarCurvature_bkmChart_tracelessHermitian_eq_hs`: **Dittmann's
  Theorem 2**, `S = ∑_{[n]³} hs(lᵢ, lⱼ, lₖ) - ∑ᵢ hs(lᵢ, lᵢ, lᵢ) + (n² - 1)(n² - 2)/4`.
* `PetzCurvature.continuousAt_bkmHs`, `PetzCurvature.tendsto_dittmannHs`: `hs` is
  continuous on the positive octant, hence the continuous extension of (61) to coincident
  arguments, as Dittmann reads it.
* `PetzCurvature.bkmForm_unitaryConjL`, `PetzCurvature.bkmChart_unitaryConjL`,
  `PetzCurvature.scalarCurvature_bkmChart_unitaryConjL`: the BKM form, its chart and its
  scalar curvature are invariant under unitary conjugation.
* `PetzCurvature.scalarCurvature_bkmChart_eq_hs`: **Dittmann's Theorem 2 at every
  faithful state**, in terms of the eigenvalues of `ρ`.

## References

* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]

-/

open scoped Matrix.Norms.L2Operator ComplexOrder
open Finset Matrix
open PetzCurvature.Curvature

namespace PetzCurvature

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

section Diagonal

/-- The coefficient tensor `m(lᵢ, lⱼ, lₖ)` of the BKM derivative at `diag(l)`. -/
noncomputable def bkmCoeff (l : d → ℝ) (i j k : d) : ℂ :=
  (bkmIntegral₃ (l i) (l j) (l k) : ℂ)

omit [Fintype d] in
/-- The coefficient tensor is symmetric in its first two indices. -/
theorem bkmCoeff_comm₁₂ (l : d → ℝ) (i j k : d) : bkmCoeff l j i k = bkmCoeff l i j k := by
  rw [bkmCoeff, bkmCoeff, bkmIntegral₃_comm₁₂]

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

variable [DecidableEq d] {l : d → ℝ}

/-- **The BKM derivative as a cyclic sum**: at `ρ = diag(l)` and for Hermitian arguments,
`DG(Z)(A, B) = -(C(A, Z, B) + C(A, B, Z))`, `C = triSum (bkmCoeff l)`. -/
theorem fderiv_bkmForm_diagonal_eq_triSum (hl : ∀ i, 0 < l i) {Z A B : Matrix d d ℂ}
    (hZ : Z.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (fderiv ℝ bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) Z A B : ℂ) =
      -(triSum (bkmCoeff l) A Z B + triSum (bkmCoeff l) A B Z) := by
  have hs : star (triSum (bkmCoeff l) A Z B) = triSum (bkmCoeff l) A B Z :=
    star_triSum (fun _ _ _ ↦ Complex.conj_ofReal _) (bkmCoeff_comm₁₂ l) hA hZ hB
  have hX : ∑ i, ∑ j, ∑ k, bkmIntegral₃ (l i) (l j) (l k) *
      ((A i j * Z j k * B k i).re + (A i j * B j k * Z k i).re) =
        (triSum (bkmCoeff l) A Z B).re + (star (triSum (bkmCoeff l) A Z B)).re := by
    rw [hs]
    simp only [triSum, bkmCoeff, Complex.re_sum, mul_add, Finset.sum_add_distrib, mul_assoc,
      Complex.re_ofReal_mul]
  rw [fderiv_bkmForm_diagonal hl, hX, ← hs, Complex.star_def, Complex.conj_re, Complex.add_conj]
  push_cast
  ring

/-- `|T|²` at `ρ = diag(l)` in a `G_ρ`-orthonormal basis of the Hermitian matrices. -/
theorem bkmContrT_diagonal (hl : ∀ i, 0 < l i) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι ℝ (hermitian d))
    (he : ∀ a b, bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (e a) (e b) =
      if a = b then 1 else 0) :
    bkmContrT (Matrix.diagonal fun i ↦ (l i : ℂ)) (fun a ↦ (e a : Matrix d d ℂ)) =
      2 * ∑ i, bkmIntegral₃ (l i) (l i) (l i) ^ 2 * (bkmIntegral₂ (l i) (l i))⁻¹ ^ 3 +
        2 * ∑ i, ∑ j, ∑ k, bkmIntegral₃ (l i) (l j) (l k) ^ 2 * ((bkmIntegral₂ (l i) (l j))⁻¹ *
          (bkmIntegral₂ (l j) (l k))⁻¹ * (bkmIntegral₂ (l k) (l i))⁻¹) := by
  have hK := sum_mul_of_orthonormal hl e he
  have hE : ∀ a, (e a : Matrix d d ℂ).IsHermitian := fun a ↦ (e a).2
  apply Complex.ofReal_injective
  simp only [bkmContrT]
  push_cast
  simp only [fderiv_bkmForm_diagonal_eq_triSum hl (hE _) (hE _) (hE _)]
  have h : ∀ X Y : ℂ, (-(X + Y)) ^ 2 = X ^ 2 + Y ^ 2 + 2 * (X * Y) := fun _ _ ↦ by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_triSum_sq hK, sum_triSum_sq' hK, sum_triSum_mul_triSum hK, ← two_mul]
  refine congrArg₂ (· + ·) (congrArg (2 * ·) ?_) (congrArg (2 * ·) ?_)
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [bkmCoeff, Complex.ofReal_inv]
    ring
  · refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ ?_
    rw [bkmCoeff_comm₁₂ l i j k]
    simp only [bkmCoeff, Complex.ofReal_inv]
    ring

/-- `|τ|²` at `ρ = diag(l)` in a `G_ρ`-orthonormal basis of the Hermitian matrices:
`τ(Z) = -2 ∑ⱼ wⱼ Zⱼⱼ` with `wⱼ = ∑ᵢ m(lᵢ, lⱼ, lⱼ) / m(lᵢ, lⱼ)`. -/
theorem bkmContrTau_diagonal (hl : ∀ i, 0 < l i) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι ℝ (hermitian d))
    (he : ∀ a b, bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (e a) (e b) =
      if a = b then 1 else 0) :
    bkmContrTau (Matrix.diagonal fun i ↦ (l i : ℂ)) (fun a ↦ (e a : Matrix d d ℂ)) =
      4 * ∑ j, (∑ i, bkmIntegral₃ (l i) (l j) (l j) * (bkmIntegral₂ (l i) (l j))⁻¹) ^ 2 *
        (bkmIntegral₂ (l j) (l j))⁻¹ := by
  have hK := sum_mul_of_orthonormal hl e he
  have hE : ∀ a, (e a : Matrix d d ℂ).IsHermitian := fun a ↦ (e a).2
  simp only [Complex.ofReal_inv] at hK
  apply Complex.ofReal_injective
  simp only [bkmContrTau]
  push_cast
  simp only [fderiv_bkmForm_diagonal_eq_triSum hl (hE _) (hE _) (hE _), Finset.sum_neg_distrib,
    Finset.sum_add_distrib, sum_triSum_self_left hK, sum_triSum_self_right hK]
  have hτ : ∀ Z : Matrix d d ℂ, -(∑ i, ∑ j, bkmCoeff l i j j * Z j j *
      ((bkmIntegral₂ (l i) (l j) : ℂ))⁻¹ + ∑ i, ∑ j, bkmCoeff l i j i * Z i i *
        ((bkmIntegral₂ (l i) (l j) : ℂ))⁻¹) =
      ∑ j, (-2 * ∑ i, bkmCoeff l i j j * ((bkmIntegral₂ (l i) (l j) : ℂ))⁻¹) * Z j j := by
    intro Z
    rw [Finset.sum_comm (f := fun i j ↦ bkmCoeff l i j j * Z j j *
      ((bkmIntegral₂ (l i) (l j) : ℂ))⁻¹), ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [bkmCoeff_comm₁₂ l i j j, bkmIntegral₂_comm (l j) (l i)]
    ring
  simp only [hτ, sum_sq_sum_diag hK, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.mul_sum]
  simp only [bkmCoeff]
  ring

end Diagonal

/-! ### The scalar curvature on all Hermitian directions -/

section Full

/-- The summand `K(x, y, z) = m(x, y, z)² / (2 m(x, y) m(y, z) m(z, x))
- x m(x, x, y) m(x, x, z) / (m(x, y) m(x, z))`, with `m = bkmIntegral₂`, `bkmIntegral₃`. -/
noncomputable def bkmSummand (x y z : ℝ) : ℝ :=
  bkmIntegral₃ x y z ^ 2 / (2 * (bkmIntegral₂ x y * bkmIntegral₂ y z * bkmIntegral₂ z x)) -
    x * bkmIntegral₃ x x y * bkmIntegral₃ x x z / (bkmIntegral₂ x y * bkmIntegral₂ x z)

variable [DecidableEq d] {l : d → ℝ}

/-- **The BKM scalar curvature on all Hermitian directions** at `ρ = diag(l)`:
`S = ∑_{(i, j, k) ∈ [n]³} K(lᵢ, lⱼ, lₖ) + ∑ᵢ 1/(8 lᵢ)`. -/
theorem scalarCurvature_bkmChart_hermitian_eq (hl : ∀ i, 0 < l i) :
    scalarCurvature (bkmChart (hermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ))) 0 =
      ∑ i, ∑ j, ∑ k, bkmSummand (l i) (l j) (l k) + ∑ i, (8 * l i)⁻¹ := by
  have hρ := posDef_diagonal_ofReal hl
  obtain ⟨e, he⟩ := exists_orthonormal_basis (bkmChart (hermitian d) _ 0)
    (fun v w ↦ (eventually_bkmChart_comm hρ).self_of_nhds v w)
    (fun v hv ↦ bkmChart_self_pos hρ (fun _ h ↦ h) hv)
  have he' : ∀ a b, bkmForm (Matrix.diagonal fun i ↦ (l i : ℂ)) (e a) (e b) =
      if a = b then 1 else 0 := fun a b ↦ by
    rw [← he, bkmChart_apply, ZeroMemClass.coe_zero, zero_add]
  rw [scalarCurvature_bkmChart_eq_contr hρ (fun _ h ↦ h) e he', bkmContrT_diagonal hl e he',
    bkmContrTau_diagonal hl e he']
  have h1 : ∑ i, bkmIntegral₃ (l i) (l i) (l i) ^ 2 * (bkmIntegral₂ (l i) (l i))⁻¹ ^ 3 =
      2 * ∑ i, (8 * l i)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [bkmIntegral₃_self (hl i), bkmIntegral₂_self (hl i)]
    field_simp
    ring
  have h2 : ∑ i, ∑ j, ∑ k, bkmIntegral₃ (l i) (l j) (l k) ^ 2 * ((bkmIntegral₂ (l i) (l j))⁻¹ *
      (bkmIntegral₂ (l j) (l k))⁻¹ * (bkmIntegral₂ (l k) (l i))⁻¹) =
      2 * ∑ i, ∑ j, ∑ k, bkmIntegral₃ (l i) (l j) (l k) ^ 2 / (2 * (bkmIntegral₂ (l i) (l j) *
        bkmIntegral₂ (l j) (l k) * bkmIntegral₂ (l k) (l i))) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have h3 : ∑ j, (∑ i, bkmIntegral₃ (l i) (l j) (l j) * (bkmIntegral₂ (l i) (l j))⁻¹) ^ 2 *
      (bkmIntegral₂ (l j) (l j))⁻¹ = ∑ i, ∑ j, ∑ k, l i * bkmIntegral₃ (l i) (l i) (l j) *
        bkmIntegral₃ (l i) (l i) (l k) / (bkmIntegral₂ (l i) (l j) * bkmIntegral₂ (l i) (l k)) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [bkmIntegral₂_self (hl i), inv_inv, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [bkmIntegral₃_comm₁₂ (l j), bkmIntegral₃_comm₂₃ (l i) (l j), bkmIntegral₃_comm₁₂ (l k),
      bkmIntegral₃_comm₂₃ (l i) (l k), bkmIntegral₂_comm (l j), bkmIntegral₂_comm (l k)]
    ring
  simp only [bkmSummand, Finset.sum_sub_distrib]
  rw [h1, h2, h3]
  ring

/-- **The BKM scalar curvature of the density matrices** at a diagonal state `ρ = diag(l)` of `n`
levels: `S = ∑_{(i, j, k) ∈ [n]³} K(lᵢ, lⱼ, lₖ) + ∑ᵢ 1/(8 lᵢ) + (n² - 1)(n² - 2)/4`. -/
theorem scalarCurvature_bkmChart_tracelessHermitian_eq_sum (hl : ∀ i, 0 < l i)
    (htr : ∑ i, l i = 1) :
    scalarCurvature (bkmChart (tracelessHermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ))) 0 =
      ∑ i, ∑ j, ∑ k, bkmSummand (l i) (l j) (l k) + ∑ i, (8 * l i)⁻¹ +
        ((Fintype.card d : ℝ) ^ 2 - 1) * ((Fintype.card d : ℝ) ^ 2 - 2) / 4 := by
  rw [scalarCurvature_bkmChart_tracelessHermitian_eq hl htr,
    scalarCurvature_bkmChart_hermitian_eq hl]

end Full

/-! ### Dittmann's form -/

section Dittmann

/-- Dittmann's symmetrized summand `hs(x, y, z) = (K(x, y, z) + K(y, z, x) + K(z, x, y)) / 3`. -/
noncomputable def bkmHs (x y z : ℝ) : ℝ :=
  (bkmSummand x y z + bkmSummand y z x + bkmSummand z x y) / 3

/-- Dittmann's closed form (61) of `hs`, in the logarithms of its arguments; it is the value of
`bkmHs` at pairwise distinct arguments (`bkmHs_eq_dittmannHs`). -/
noncomputable def dittmannHs (x y z : ℝ) : ℝ :=
  ((y - z) ^ 2 * (Real.log x - Real.log y) * (Real.log x - Real.log z) -
      (x - z) ^ 2 * (Real.log x - Real.log y) * (Real.log y - Real.log z) +
      (x - y) ^ 2 * (Real.log x - Real.log z) * (Real.log y - Real.log z)) /
    (6 * (x - y) * (x - z) * (y - z) * (Real.log x - Real.log y) * (Real.log x - Real.log z) *
      (Real.log y - Real.log z)) +
  (-x * y * (Real.log x - Real.log y) + x * z * (Real.log x - Real.log z) -
      y * z * (Real.log y - Real.log z)) /
    (3 * x * y * z * (Real.log x - Real.log y) * (Real.log x - Real.log z) *
      (Real.log y - Real.log z))

/-- `K(x, x, x) = -1/(8x)`. -/
theorem bkmSummand_self {x : ℝ} (hx : 0 < x) : bkmSummand x x x = -(8 * x)⁻¹ := by
  rw [bkmSummand, bkmIntegral₃_self hx, bkmIntegral₂_self hx]
  field_simp
  ring

/-- `hs(x, x, x) = -1/(8x)`. -/
theorem bkmHs_self {x : ℝ} (hx : 0 < x) : bkmHs x x x = -(8 * x)⁻¹ := by
  rw [bkmHs, bkmSummand_self hx]
  ring

/-- Cyclic relabeling of a sum over `[n]³`. -/
theorem sum_cyclic {M : Type*} [AddCommMonoid M] (g : d → d → d → M) :
    ∑ i, ∑ j, ∑ k, g j k i = ∑ i, ∑ j, ∑ k, g i j k := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]

/-- Summing `K` or its cyclic symmetrization `hs` over `[n]³` gives the same. -/
theorem sum_bkmHs (l : d → ℝ) :
    ∑ i, ∑ j, ∑ k, bkmHs (l i) (l j) (l k) = ∑ i, ∑ j, ∑ k, bkmSummand (l i) (l j) (l k) := by
  simp only [bkmHs, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [sum_cyclic (fun i j k ↦ bkmSummand (l i) (l j) (l k)),
    ← sum_cyclic (fun i j k ↦ bkmSummand (l k) (l i) (l j))]
  ring

/-- `m(x, x, y)` in closed form, `x ≠ y`. -/
theorem bkmIntegral₃_self_left {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    bkmIntegral₃ x x y = (x⁻¹ - (Real.log y - Real.log x) / (y - x)) / (y - x) := by
  rw [bkmIntegral₃_comm₂₃, bkmIntegral₃_of_ne hx hy hx hxy, bkmIntegral₂_self hx,
    bkmIntegral₂_of_ne hy hx hxy.symm]

/-- `m(x, y, z)` in closed form, pairwise distinct arguments. -/
theorem bkmIntegral₃_of_pairwise_ne {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    bkmIntegral₃ x y z = ((Real.log x - Real.log z) / (x - z) -
      (Real.log y - Real.log z) / (y - z)) / (y - x) := by
  rw [bkmIntegral₃_of_ne hx hy hz hxy, bkmIntegral₂_of_ne hx hz hxz, bkmIntegral₂_of_ne hy hz hyz]

/-- `m(x, x, y) / m(x, y)` in closed form, `x ≠ y`. -/
theorem bkmIntegral₃_self_left_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    bkmIntegral₃ x x y / bkmIntegral₂ x y = (y - x - x * (Real.log y - Real.log x)) /
      (x * (x - y) * (Real.log x - Real.log y)) := by
  have h1 := sub_ne_zero.mpr hxy
  have h2 := sub_ne_zero.mpr hxy.symm
  have h3 := sub_ne_zero.mpr (Real.log_injOn_pos.ne hx hy hxy)
  have h4 := sub_ne_zero.mpr (Real.log_injOn_pos.ne hy hx hxy.symm)
  rw [bkmIntegral₃_self_left hx hy hxy, bkmIntegral₂_of_ne hx hy hxy]
  field_simp
  ring

/-- The fully symmetric part of `K` in closed form, pairwise distinct arguments. -/
theorem bkmIntegral₃_sq_div {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    bkmIntegral₃ x y z ^ 2 / (2 * (bkmIntegral₂ x y * bkmIntegral₂ y z * bkmIntegral₂ z x)) =
      (-Real.log x * y + Real.log x * z + Real.log y * x - Real.log y * z - Real.log z * x +
        Real.log z * y) ^ 2 / (2 * (Real.log x - Real.log y) * (Real.log x - Real.log z) *
          (Real.log y - Real.log z) * (x - y) * (x - z) * (y - z)) := by
  have := sub_ne_zero.mpr hxy; have := sub_ne_zero.mpr hxy.symm
  have := sub_ne_zero.mpr hxz; have := sub_ne_zero.mpr hxz.symm
  have := sub_ne_zero.mpr hyz; have := sub_ne_zero.mpr hyz.symm
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hx hy hxy)
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hx hz hxz)
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hy hz hyz)
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hz hx hxz.symm)
  rw [bkmIntegral₃_of_pairwise_ne hx hy hz hxy hxz hyz, bkmIntegral₂_of_ne hx hy hxy,
    bkmIntegral₂_of_ne hy hz hyz, bkmIntegral₂_of_ne hz hx hxz.symm]
  field_simp
  ring

/-- **Dittmann's (61)**: at pairwise distinct positive arguments, `hs` is his closed form. -/
theorem bkmHs_eq_dittmannHs {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : bkmHs x y z = dittmannHs x y z := by
  have e : ∀ p q r, bkmSummand p q r = bkmIntegral₃ p q r ^ 2 /
      (2 * (bkmIntegral₂ p q * bkmIntegral₂ q r * bkmIntegral₂ r p)) -
        p * (bkmIntegral₃ p p q / bkmIntegral₂ p q) * (bkmIntegral₃ p p r / bkmIntegral₂ p r) :=
    fun _ _ _ ↦ by rw [bkmSummand]; ring
  have s1 : bkmIntegral₃ y z x ^ 2 /
      (2 * (bkmIntegral₂ y z * bkmIntegral₂ z x * bkmIntegral₂ x y)) = bkmIntegral₃ x y z ^ 2 /
        (2 * (bkmIntegral₂ x y * bkmIntegral₂ y z * bkmIntegral₂ z x)) := by
    rw [bkmIntegral₃_comm₂₃ y z x, bkmIntegral₃_comm₁₂ y x z]
    ring
  have s2 : bkmIntegral₃ z x y ^ 2 /
      (2 * (bkmIntegral₂ z x * bkmIntegral₂ x y * bkmIntegral₂ y z)) = bkmIntegral₃ x y z ^ 2 /
        (2 * (bkmIntegral₂ x y * bkmIntegral₂ y z * bkmIntegral₂ z x)) := by
    rw [bkmIntegral₃_comm₁₂ z x y, bkmIntegral₃_comm₂₃ x z y]
    ring
  rw [bkmHs, e, e, e, s1, s2, bkmIntegral₃_sq_div hx hy hz hxy hxz hyz,
    bkmIntegral₃_self_left_div hx hy hxy, bkmIntegral₃_self_left_div hx hz hxz,
    bkmIntegral₃_self_left_div hy hz hyz, bkmIntegral₃_self_left_div hy hx hxy.symm,
    bkmIntegral₃_self_left_div hz hx hxz.symm, bkmIntegral₃_self_left_div hz hy hyz.symm,
    dittmannHs]
  have := hx.ne'; have := hy.ne'; have := hz.ne'
  have := sub_ne_zero.mpr hxy; have := sub_ne_zero.mpr hxy.symm
  have := sub_ne_zero.mpr hxz; have := sub_ne_zero.mpr hxz.symm
  have := sub_ne_zero.mpr hyz; have := sub_ne_zero.mpr hyz.symm
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hx hy hxy)
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hy hx hxy.symm)
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hx hz hxz)
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hz hx hxz.symm)
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hy hz hyz)
  have := sub_ne_zero.mpr (Real.log_injOn_pos.ne hz hy hyz.symm)
  field_simp
  ring

variable [DecidableEq d] {l : d → ℝ} in
/-- **Dittmann's Theorem 2** (58): the scalar curvature of the Kubo–Mori metric on the density
matrices of `n` levels at `ρ = diag(l)` is
`∑_{(i, j, k) ∈ [n]³} hs(lᵢ, lⱼ, lₖ) - ∑ᵢ hs(lᵢ, lᵢ, lᵢ) + (n² - 1)(n² - 2)/4`. Dittmann's
summand `d` of (57) is replaced by its symmetrization `hs` (61), which gives the same sums, since
`d(x, x, x) = hs(x, x, x)`. -/
theorem scalarCurvature_bkmChart_tracelessHermitian_eq_hs (hl : ∀ i, 0 < l i)
    (htr : ∑ i, l i = 1) :
    scalarCurvature (bkmChart (tracelessHermitian d) (Matrix.diagonal fun i ↦ (l i : ℂ))) 0 =
      ∑ i, ∑ j, ∑ k, bkmHs (l i) (l j) (l k) - ∑ i, bkmHs (l i) (l i) (l i) +
        ((Fintype.card d : ℝ) ^ 2 - 1) * ((Fintype.card d : ℝ) ^ 2 - 2) / 4 := by
  rw [scalarCurvature_bkmChart_tracelessHermitian_eq_sum hl htr, sum_bkmHs]
  simp only [bkmHs_self (hl _), Finset.sum_neg_distrib]
  ring

end Dittmann

/-! ### Continuity: `hs` is the continuous extension of (61) -/

section Continuity

open Filter Topology

/-- `m(x, y)` is continuous on the positive quadrant, coincident arguments included. -/
theorem continuousAt_bkmIntegral₂ {p : ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2) :
    ContinuousAt (fun q : ℝ × ℝ ↦ bkmIntegral₂ q.1 q.2) p := by
  refine continuousAt_intervalIntegral_of_continuousAt
    (f := fun z : (ℝ × ℝ) × ℝ ↦ ((1 - z.2) * z.1.1 + z.2)⁻¹ * ((1 - z.2) * z.1.2 + z.2)⁻¹)
    fun t ht ↦ ?_
  have h1' := (pathScalar_pos h1 ht).ne'
  have h2' := (pathScalar_pos h2 ht).ne'
  fun_prop (disch := assumption)

/-- `m(x, y, z)` is continuous on the positive octant, coincident arguments included. -/
theorem continuousAt_bkmIntegral₃ {p : ℝ × ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2.1)
    (h3 : 0 < p.2.2) : ContinuousAt (fun q : ℝ × ℝ × ℝ ↦ bkmIntegral₃ q.1 q.2.1 q.2.2) p := by
  refine continuousAt_intervalIntegral_of_continuousAt
    (f := fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (1 - z.2) * (((1 - z.2) * z.1.1 + z.2)⁻¹ *
      ((1 - z.2) * z.1.2.1 + z.2)⁻¹ * ((1 - z.2) * z.1.2.2 + z.2)⁻¹)) fun t ht ↦ ?_
  have h1' := (pathScalar_pos h1 ht).ne'
  have h2' := (pathScalar_pos h2 ht).ne'
  have h3' := (pathScalar_pos h3 ht).ne'
  fun_prop (disch := assumption)

variable {X : Type*} [TopologicalSpace X] {f g h : X → ℝ} {x₀ : X}

theorem continuousAt_bkmIntegral₂_comp (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀)
    (hf0 : 0 < f x₀) (hg0 : 0 < g x₀) :
    ContinuousAt (fun x ↦ bkmIntegral₂ (f x) (g x)) x₀ :=
  ContinuousAt.comp (g := fun q : ℝ × ℝ ↦ bkmIntegral₂ q.1 q.2) (f := fun x ↦ (f x, g x))
    (continuousAt_bkmIntegral₂ (p := (f x₀, g x₀)) hf0 hg0) (hf.prodMk hg)

theorem continuousAt_bkmIntegral₃_comp (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀)
    (hh : ContinuousAt h x₀) (hf0 : 0 < f x₀) (hg0 : 0 < g x₀) (hh0 : 0 < h x₀) :
    ContinuousAt (fun x ↦ bkmIntegral₃ (f x) (g x) (h x)) x₀ :=
  ContinuousAt.comp (g := fun q : ℝ × ℝ × ℝ ↦ bkmIntegral₃ q.1 q.2.1 q.2.2)
    (f := fun x ↦ (f x, g x, h x))
    (continuousAt_bkmIntegral₃ (p := (f x₀, g x₀, h x₀)) hf0 hg0 hh0) (hf.prodMk (hg.prodMk hh))

theorem continuousAt_bkmSummand_comp (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀)
    (hh : ContinuousAt h x₀) (hf0 : 0 < f x₀) (hg0 : 0 < g x₀) (hh0 : 0 < h x₀) :
    ContinuousAt (fun x ↦ bkmSummand (f x) (g x) (h x)) x₀ := by
  have a₁ := continuousAt_bkmIntegral₂_comp hf hg hf0 hg0
  have a₂ := continuousAt_bkmIntegral₂_comp hg hh hg0 hh0
  have a₃ := continuousAt_bkmIntegral₂_comp hh hf hh0 hf0
  have a₄ := continuousAt_bkmIntegral₂_comp hf hh hf0 hh0
  have n₁ := (bkmIntegral₂_pos hf0 hg0).ne'
  have n₂ := (bkmIntegral₂_pos hg0 hh0).ne'
  have n₃ := (bkmIntegral₂_pos hh0 hf0).ne'
  have n₄ := (bkmIntegral₂_pos hf0 hh0).ne'
  exact ContinuousAt.sub (((continuousAt_bkmIntegral₃_comp hf hg hh hf0 hg0 hh0).pow 2).div
    (continuousAt_const.mul ((a₁.mul a₂).mul a₃))
      (mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero n₁ n₂) n₃)))
    (((hf.mul (continuousAt_bkmIntegral₃_comp hf hf hg hf0 hf0 hg0)).mul
      (continuousAt_bkmIntegral₃_comp hf hf hh hf0 hf0 hh0)).div (a₁.mul a₄) (mul_ne_zero n₁ n₄))

/-- `hs` is continuous on the positive octant. -/
theorem continuousAt_bkmHs {p : ℝ × ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2.1) (h3 : 0 < p.2.2) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ ↦ bkmHs q.1 q.2.1 q.2.2) p := by
  have c1 : ContinuousAt (fun q : ℝ × ℝ × ℝ ↦ q.1) p := continuousAt_fst
  have c2 : ContinuousAt (fun q : ℝ × ℝ × ℝ ↦ q.2.1) p := continuousAt_snd.fst
  have c3 : ContinuousAt (fun q : ℝ × ℝ × ℝ ↦ q.2.2) p := continuousAt_snd.snd
  exact (((continuousAt_bkmSummand_comp c1 c2 c3 h1 h2 h3).add
    (continuousAt_bkmSummand_comp c2 c3 c1 h2 h3 h1)).add
      (continuousAt_bkmSummand_comp c3 c1 c2 h3 h1 h2)).div_const 3

/-- **`hs` is the continuous extension of Dittmann's closed form (61)**: as pairwise distinct
arguments tend to any positive `(x, y, z)`, coincident or not, (61) tends to `hs(x, y, z)`. -/
theorem tendsto_dittmannHs {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Tendsto (fun q : ℝ × ℝ × ℝ ↦ dittmannHs q.1 q.2.1 q.2.2)
      (𝓝[{q | q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2}] (x, y, z)) (𝓝 (bkmHs x y z)) := by
  refine ((continuousAt_bkmHs (p := (x, y, z)) hx hy hz).tendsto.mono_left
    nhdsWithin_le_nhds).congr' ?_
  have p1 : ∀ᶠ q : ℝ × ℝ × ℝ in 𝓝 (x, y, z), 0 < q.1 :=
    continuousAt_fst.eventually (lt_mem_nhds hx)
  have p2 : ∀ᶠ q : ℝ × ℝ × ℝ in 𝓝 (x, y, z), 0 < q.2.1 :=
    continuousAt_snd.fst.eventually (lt_mem_nhds hy)
  have p3 : ∀ᶠ q : ℝ × ℝ × ℝ in 𝓝 (x, y, z), 0 < q.2.2 :=
    continuousAt_snd.snd.eventually (lt_mem_nhds hz)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (p1.and (p2.and p3))] with q hq hp
  exact bkmHs_eq_dittmannHs hp.1 hp.2.1 hp.2.2 hq.1 hq.2.1 hq.2.2

end Continuity

/-! ### Unitary invariance: every faithful state -/

section Unitary

variable [DecidableEq d] {U : Matrix d d ℂ}

/-- Conjugation `A ↦ U A Uᴴ` by a unitary `U`, as a real-linear equivalence. -/
noncomputable def unitaryConjL (hU : U ∈ unitaryGroup d ℂ) : Matrix d d ℂ ≃L[ℝ] Matrix d d ℂ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun A ↦ U * A * star U
      invFun := fun A ↦ star U * A * U
      map_add' := fun A B ↦ by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r A ↦ by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
      left_inv := fun A ↦ by
        simp only [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU, Matrix.one_mul]
        rw [Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU, Matrix.mul_one]
      right_inv := fun A ↦ by
        simp only [← Matrix.mul_assoc, Unitary.mul_star_self_of_mem hU, Matrix.one_mul]
        rw [Matrix.mul_assoc, Unitary.mul_star_self_of_mem hU, Matrix.mul_one] }

theorem unitaryConjL_apply (hU : U ∈ unitaryGroup d ℂ) (A : Matrix d d ℂ) :
    unitaryConjL hU A = U * A * star U :=
  rfl

theorem unitaryConjL_symm_apply (hU : U ∈ unitaryGroup d ℂ) (A : Matrix d d ℂ) :
    (unitaryConjL hU).symm A = star U * A * U :=
  rfl

theorem bkmPath_unitaryConjL (hU : U ∈ unitaryGroup d ℂ) (x : Matrix d d ℂ) (t : ℝ) :
    bkmPath (unitaryConjL hU x, t) = unitaryConjL hU (bkmPath (x, t)) := by
  simp only [bkmPath, unitaryConjL_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Unitary.mul_star_self_of_mem hU]

theorem inv_unitaryConjL (hU : U ∈ unitaryGroup d ℂ) (M : Matrix d d ℂ) :
    (unitaryConjL hU M)⁻¹ = unitaryConjL hU M⁻¹ := by
  rw [unitaryConjL_apply, unitaryConjL_apply, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.inv_eq_left_inv (Unitary.mul_star_self_of_mem hU),
    Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hU), Matrix.mul_assoc]

/-- The sandwich form is invariant under simultaneous unitary conjugation, by cyclicity of the
trace. -/
theorem sandwichForm_unitaryConjL (hU : U ∈ unitaryGroup d ℂ) (R A B : Matrix d d ℂ) :
    sandwichForm (unitaryConjL hU R) (unitaryConjL hU A) (unitaryConjL hU B) =
      sandwichForm R A B := by
  have h := Unitary.star_mul_self_of_mem hU
  simp only [sandwichForm_apply, unitaryConjL_apply]
  have e : U * A * star U * (U * R * star U) * (U * B * star U) * (U * R * star U) =
      U * (A * R * B * R) * star U := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star U) U, h, Matrix.one_mul]
  rw [e, Matrix.trace_mul_cycle, h, Matrix.one_mul]

/-- The bilinear forms transported by `unitaryConjL`: `B ↦ B(U* · U, U* · U)`. -/
noncomputable def bilinConj (hU : U ∈ unitaryGroup d ℂ) :
    (Matrix d d ℂ →L[ℝ] Matrix d d ℂ →L[ℝ] ℝ) ≃L[ℝ] (Matrix d d ℂ →L[ℝ] Matrix d d ℂ →L[ℝ] ℝ) :=
  (unitaryConjL hU).arrowCongr ((unitaryConjL hU).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))

/-- **Unitary invariance of the BKM form**: `G_{U x U*} = G_x(U* · U, U* · U)`. -/
theorem bkmForm_unitaryConjL (hU : U ∈ unitaryGroup d ℂ) (x : Matrix d d ℂ) :
    bkmForm (unitaryConjL hU x) = bilinConj hU (bkmForm x) := by
  have hi : ∀ t : ℝ, bkmIntegrand (unitaryConjL hU x, t) = bilinConj hU (bkmIntegrand (x, t)) := by
    intro t
    ext A B
    simp only [bkmIntegrand, bilinConj, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.refl_apply, bkmPath_unitaryConjL, inv_unitaryConjL]
    rw [← sandwichForm_unitaryConjL hU (bkmPath (x, t))⁻¹ ((unitaryConjL hU).symm A),
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp only [bkmForm, hi]
  simp_rw [intervalIntegral, (bilinConj hU).integral_comp_comm, (bilinConj hU).map_sub]

theorem bkmForm_unitaryConjL_apply (hU : U ∈ unitaryGroup d ℂ) (x A B : Matrix d d ℂ) :
    bkmForm (unitaryConjL hU x) (unitaryConjL hU A) (unitaryConjL hU B) = bkmForm x A B := by
  rw [bkmForm_unitaryConjL]
  simp [bilinConj]

/-- Conjugation by a unitary preserves the traceless Hermitian matrices. -/
theorem unitaryConjL_mem (hU : U ∈ unitaryGroup d ℂ) {A : Matrix d d ℂ}
    (hA : A ∈ tracelessHermitian d) : unitaryConjL hU A ∈ tracelessHermitian d := by
  refine ⟨?_, ?_⟩
  · rw [unitaryConjL_apply, Matrix.star_eq_conjTranspose]
    exact isHermitian_mul_mul_conjTranspose U hA.1
  · rw [unitaryConjL_apply, Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem hU,
      Matrix.one_mul, hA.2]

/-- Conjugation by a unitary on the traceless Hermitian matrices. -/
noncomputable def tracelessConj (hU : U ∈ unitaryGroup d ℂ) :
    tracelessHermitian d ≃L[ℝ] tracelessHermitian d :=
  LinearEquiv.toContinuousLinearEquiv <| LinearEquiv.ofLinearMap
    ((unitaryConjL hU).toLinearMap.restrict fun _ hA ↦ unitaryConjL_mem hU hA)
    ((unitaryConjL (Unitary.star_mem hU)).toLinearMap.restrict fun _ hA ↦
      unitaryConjL_mem (Unitary.star_mem hU) hA)
    (LinearMap.ext fun z ↦ Subtype.ext <| by
      change U * (star U * z * star (star U)) * star U = z
      rw [star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Unitary.mul_star_self_of_mem hU,
        Matrix.one_mul, Matrix.mul_assoc, Unitary.mul_star_self_of_mem hU, Matrix.mul_one])
    (LinearMap.ext fun z ↦ Subtype.ext <| by
      change star U * (U * z * star U) * star (star U) = z
      rw [star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU,
        Matrix.one_mul, Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU, Matrix.mul_one])

theorem coe_tracelessConj (hU : U ∈ unitaryGroup d ℂ) (z : tracelessHermitian d) :
    (tracelessConj hU z : Matrix d d ℂ) = U * z * star U :=
  rfl

/-- **The BKM chart at `U ρ U*`** is the pullback of the chart at `ρ` by `z ↦ U* z U`. -/
theorem bkmChart_unitaryConjL (hU : U ∈ unitaryGroup d ℂ) (ρ : Matrix d d ℂ) :
    bkmChart (tracelessHermitian d) (unitaryConjL hU ρ) =
      pullback (tracelessConj (Unitary.star_mem hU)) (bkmChart (tracelessHermitian d) ρ) := by
  ext z u w
  rw [pullback_apply, ContinuousLinearEquiv.fderiv, bkmChart_apply, bkmChart_apply]
  symm
  rw [← bkmForm_unitaryConjL_apply hU]
  have h := Unitary.mul_star_self_of_mem hU
  have e : ∀ v : Matrix d d ℂ, unitaryConjL hU (star U * v * star (star U)) = v := fun v ↦ by
    rw [unitaryConjL_apply, star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul,
      Matrix.mul_assoc, h, Matrix.mul_one]
  simp only [ContinuousLinearEquiv.coe_coe, coe_tracelessConj, map_add, e]

/-- **The BKM scalar curvature is unitarily invariant.** -/
theorem scalarCurvature_bkmChart_unitaryConjL (hU : U ∈ unitaryGroup d ℂ) {ρ : Matrix d d ℂ}
    (hρ : ρ.PosDef) :
    scalarCurvature (bkmChart (tracelessHermitian d) (unitaryConjL hU ρ)) 0 =
      scalarCurvature (bkmChart (tracelessHermitian d) ρ) 0 := by
  set ψ := tracelessConj (Unitary.star_mem hU)
  have h0 : ψ 0 = 0 := map_zero ψ
  rw [bkmChart_unitaryConjL hU, scalarCurvature_pullback (φ := ψ) (x := 0) ψ.contDiff.contDiffAt
    (by rw [ψ.fderiv]; exact ⟨ψ, rfl⟩) (by rw [h0]; exact contDiffAt_bkmChart hρ 2)
    (by rw [h0]; exact eventually_bkmChart_comm hρ)
    (by rw [h0]; exact isInvertible_bkmChart hρ fun _ hA ↦ hA.1), h0]

/-- **Dittmann's Theorem 2 at every faithful state**: for a positive definite density matrix `ρ`
of `n` levels with eigenvalues `λ`, the scalar curvature of the Kubo–Mori metric is
`∑_{(i, j, k) ∈ [n]³} hs(λᵢ, λⱼ, λₖ) - ∑ᵢ hs(λᵢ, λᵢ, λᵢ) + (n² - 1)(n² - 2)/4`. -/
theorem scalarCurvature_bkmChart_eq_hs {ρ : Matrix d d ℂ} (hρ : ρ.PosDef) (htr : ρ.trace = 1) :
    scalarCurvature (bkmChart (tracelessHermitian d) ρ) 0 =
      ∑ i, ∑ j, ∑ k, bkmHs (hρ.1.eigenvalues i) (hρ.1.eigenvalues j) (hρ.1.eigenvalues k) -
        ∑ i, bkmHs (hρ.1.eigenvalues i) (hρ.1.eigenvalues i) (hρ.1.eigenvalues i) +
          ((Fintype.card d : ℝ) ^ 2 - 1) * ((Fintype.card d : ℝ) ^ 2 - 2) / 4 := by
  set l := hρ.1.eigenvalues
  have hl : ∀ i, 0 < l i := hρ.eigenvalues_pos
  have hU := hρ.1.eigenvectorUnitary.2
  have hρU : ρ = unitaryConjL hU (Matrix.diagonal fun i ↦ (l i : ℂ)) := by
    conv_lhs => rw [hρ.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have htr' : ∑ i, l i = 1 := by
    have h : ((∑ i, l i : ℝ) : ℂ) = 1 := by
      rw [← htr, hρ.1.trace_eq_sum_eigenvalues, Complex.ofReal_sum]
      rfl
    exact_mod_cast h
  rw [hρU, scalarCurvature_bkmChart_unitaryConjL hU (posDef_diagonal_ofReal hl),
    scalarCurvature_bkmChart_tracelessHermitian_eq_hs hl htr']

end Unitary

end PetzCurvature
