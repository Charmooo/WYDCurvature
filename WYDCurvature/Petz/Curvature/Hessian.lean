/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import WYDCurvature.Petz.Curvature.Basic

/-!
# Curvature of metrics with a totally symmetric derivative

A **Hessian metric** is the field of second derivatives `G = D²φ` of a function `φ : E → ℝ`, in
an affine chart: the metric of a Hessian structure in Shima's sense. The
Bogoliubov–Kubo–Mori metric is one, on the cone of positive matrices, with `φ(ρ) = Tr ρ log ρ`,
the negative of the von Neumann entropy: the derivative of `log` at `ρ` in the direction `B` is
`∫₀^∞ (ρ + t)⁻¹ B (ρ + t)⁻¹ dt`, so `D²φ(ρ)(A, B)` is the BKM resolvent integral.

For a Hessian metric the curvature involves only the third derivative `T = D³φ`, because the
fourth derivatives cancel in the Riemann map. The proofs use only that `G` is symmetric, `DG`
symmetric in its first two slots near `x` (so `DG` is totally symmetric; a Codazzi tensor for the
flat connection of the chart) and `G` of class `C²`. This is the local form of a Hessian metric,
stated for any field (`*_of_fderiv_comm`), so a metric given by a formula, such as the BKM
integral, needs no potential. Dittmann makes the same observation for the Kubo–Mori metric: the
second derivatives of `g` cancel because `D_X g(X, Y) = D_Y g(X, X)` (the remark before his
(59)). With `Γ` the Christoffel map,
* `Γ(v, w) = ½ G⁻¹ T(v, w, ·)`,
* `R(X, Y) Z = Γ(Y, Γ(X, Z)) - Γ(X, Γ(Y, Z))`,
* `Ric(Y, Z) = tr (Γ_Y ∘ Γ_Z) - tr Γ_{Γ(Y, Z)}`, with `Γ_v = Γ(v, ·)`,
* `S = ¼ (|T|² - |τ|²)` in a `G x`-orthonormal basis, `τ = tr_G T`, the classical formula for
  Hessian manifolds.

## Main statements

* `christoffelForm_of_fderiv_comm`, `apply_christoffel_of_fderiv_comm`: the Christoffel map,
  `G(Γ(v, w), u) = ½ T(v, w, u)`.
* `riemann_of_fderiv_comm`, `ricci_of_fderiv_comm`: the Riemann and Ricci maps.
* `scalarCurvature_of_fderiv_comm_of_orthonormal`: in a `G x`-orthonormal basis,
  `S = ¼ (∑ T(bᵢ, bⱼ, bₖ)² - ∑ᵢ (∑ⱼ T(bᵢ, bⱼ, bⱼ))²)` with `T = DG(x)`; via
  `scalarCurvature_eq_sum_of_orthonormal` (`S = ∑ᵢ Ric(bᵢ, bᵢ)`) and
  `trace_eq_sum_of_orthonormal`.
* `exists_orthonormal_basis`: a positive definite form has an orthonormal basis.

## References

* [H. Shima, *The Geometry of Hessian Structures*][shima2007]
* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]
-/

open Filter ContinuousLinearMap PetzCurvature.Curvature
open scoped Topology

namespace PetzCurvature.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

/-! ### The Christoffel map of a field with totally symmetric derivative

The hypothesis `hT`, symmetry of `DG` in its first two slots, is the Codazzi equation for `G` and
the flat connection of the chart; with the symmetry of `G` it makes `DG` totally symmetric. -/

section Codazzi

variable {G : E → E →L[ℝ] E →L[ℝ] ℝ}

/-- `DG(x)` is symmetric in its last two slots, because `G y` is symmetric for `y` near `x`.
Together with the Codazzi hypothesis `hT` (symmetry in the first two slots) it makes `DG(x)`
totally symmetric. -/
theorem fderiv_apply_comm₂₃ (hGs : ∀ᶠ y in 𝓝 x, ∀ v w, G y v w = G y w v) (u v w : E) :
    fderiv ℝ G x u v w = fderiv ℝ G x u w v :=
  fderiv_apply_comm_of_eventually hGs u v w

/-- The Christoffel form of a field with totally symmetric derivative is `½ DG v w`. -/
theorem christoffelForm_of_fderiv_comm (hGs : ∀ᶠ y in 𝓝 x, ∀ v w, G y v w = G y w v)
    (hT : ∀ u v w, fderiv ℝ G x u v w = fderiv ℝ G x v u w) (v w : E) :
    christoffelForm G x v w = (2⁻¹ : ℝ) • fderiv ℝ G x v w := by
  ext u
  rw [christoffelForm_apply, smul_apply, smul_eq_mul, hT w v u, hT u v w,
    fderiv_apply_comm₂₃ hGs v u w]
  ring

/-- `G(Γ(v, w), u) = ½ DG(v, w, u)` where `G x` is invertible. -/
theorem apply_christoffel_of_fderiv_comm (hGs : ∀ᶠ y in 𝓝 x, ∀ v w, G y v w = G y w v)
    (hT : ∀ u v w, fderiv ℝ G x u v w = fderiv ℝ G x v u w) (hx : (G x).IsInvertible)
    (v w u : E) : G x (christoffel G x v w) u = 2⁻¹ * fderiv ℝ G x v w u := by
  rw [christoffel_spec hx, christoffelForm_of_fderiv_comm hGs hT, smul_apply, smul_eq_mul]

end Codazzi

/-! ### Curvature of a field with totally symmetric derivative -/

section FiniteDimensional

variable [FiniteDimensional ℝ E]

section Codazzi

variable {G : E → E →L[ℝ] E →L[ℝ] ℝ}

/-- The derivative of the Christoffel map of a field with totally symmetric derivative, paired
with `G`: `G(DΓ(X, v, w), u) = ½ D²G(X, v, w, u) - DG(X, Γ(v, w), u)`. -/
theorem apply_fderiv_christoffel_of_fderiv_comm (hGs : ∀ᶠ y in 𝓝 x, ∀ v w, G y v w = G y w v)
    (hT : ∀ᶠ y in 𝓝 x, ∀ u v w, fderiv ℝ G y u v w = fderiv ℝ G y v u w)
    (hG₂ : ContDiffAt ℝ 2 G x) (hx : (G x).IsInvertible) (X v w u : E) :
    G x (fderiv ℝ (christoffel G) x X v w) u =
      2⁻¹ * fderiv ℝ (fderiv ℝ G) x X v w u - fderiv ℝ G x X (christoffel G x v w) u := by
  have hinv : ∀ᶠ y in 𝓝 x, (G y).IsInvertible :=
    hG₂.continuousAt.eventually hx.eventually_nhds
  have hΓ : DifferentiableAt ℝ (christoffel G) x :=
    (contDiffAt_christoffel (k := 1) (by simpa [one_add_one_eq_two] using hG₂) hx).differentiableAt
      one_ne_zero
  have hΓa : DifferentiableAt ℝ (fun y ↦ christoffel G y v w) x :=
    (hΓ.clm_apply (differentiableAt_const v)).clm_apply (differentiableAt_const w)
  have hGx : DifferentiableAt ℝ G x := hG₂.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ G) x :=
    (hG₂.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y ↦ G y (christoffel G y v w) u) =ᶠ[𝓝 x]
      fun y ↦ 2⁻¹ * fderiv ℝ G y v w u :=
    ((hinv.and hT).and hGs.eventually_nhds).mono fun y hy ↦
      apply_christoffel_of_fderiv_comm hy.2 hy.1.2 hy.1.1 v w u
  have h := congrArg (fun L : E →L[ℝ] ℝ ↦ L X) heq.fderiv_eq
  rw [fderiv_apply_apply (a := fun y ↦ christoffel G y v w) (b := fun _ ↦ u) hGx hΓa
    (differentiableAt_const u), fderiv_clm_apply_apply_const hΓ v w X, fderiv_const_mul
    (((hD.clm_apply (differentiableAt_const v)).clm_apply (differentiableAt_const w)).clm_apply
      (differentiableAt_const u)), smul_apply, smul_eq_mul,
    fderiv_clm_apply_const ((hD.clm_apply (differentiableAt_const v)).clm_apply
      (differentiableAt_const w)) u X, fderiv_clm_apply_apply_const hD v w X] at h
  simp only [fderiv_const_apply, zero_apply, map_zero, add_zero] at h
  linarith

/-- **The Riemann map of a field with totally symmetric derivative** (a Hessian metric, locally):
`R(X, Y) Z = Γ(Y, Γ(X, Z)) - Γ(X, Γ(Y, Z))`; the second derivatives of `G` cancel. -/
theorem riemann_of_fderiv_comm (hGs : ∀ᶠ y in 𝓝 x, ∀ v w, G y v w = G y w v)
    (hT : ∀ᶠ y in 𝓝 x, ∀ u v w, fderiv ℝ G y u v w = fderiv ℝ G y v u w)
    (hG₂ : ContDiffAt ℝ 2 G x) (hx : (G x).IsInvertible) (X Y Z : E) :
    riemann G x X Y Z = christoffel G x Y (christoffel G x X Z) -
      christoffel G x X (christoffel G x Y Z) := by
  -- Pair both sides with `G x`: the fourth derivatives `D²G X Y Z u` and `D²G Y X Z u` agree by
  -- the symmetry of second derivatives (`hs`), and the rest rearranges by
  -- `G(Γ(v, w), u) = ½ DG(v, w, u)` (`c₁`, `c₂`) and its derivative (`d₁`, `d₂`).
  apply hx.injective
  ext u
  have hs := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ ↦ L Z u)
    (hG₂.isSymmSndFDerivAt (by simp) X Y)
  have d₁ := apply_fderiv_christoffel_of_fderiv_comm hGs hT hG₂ hx X Y Z u
  have d₂ := apply_fderiv_christoffel_of_fderiv_comm hGs hT hG₂ hx Y X Z u
  have c₁ := apply_christoffel_of_fderiv_comm hGs hT.self_of_nhds hx X (christoffel G x Y Z) u
  have c₂ := apply_christoffel_of_fderiv_comm hGs hT.self_of_nhds hx Y (christoffel G x X Z) u
  simp only [Curvature.riemann_apply, map_add, map_sub, add_apply, sub_apply]
  linarith

/-- **The Ricci map of a field with totally symmetric derivative**:
`Ric(Y, Z) = tr (Γ_Y ∘ Γ_Z) - tr Γ_{Γ(Y, Z)}`. -/
theorem ricci_of_fderiv_comm (hGs : ∀ᶠ y in 𝓝 x, ∀ v w, G y v w = G y w v)
    (hT : ∀ᶠ y in 𝓝 x, ∀ u v w, fderiv ℝ G y u v w = fderiv ℝ G y v u w)
    (hG₂ : ContDiffAt ℝ 2 G x) (hx : (G x).IsInvertible) (Y Z : E) :
    ricci G x Y Z =
      LinearMap.trace ℝ E ((christoffel G x Y ∘L christoffel G x Z : E →L[ℝ] E)) -
        LinearMap.trace ℝ E ((christoffel G x (christoffel G x Y Z) : E →L[ℝ] E)) := by
  have key : (((riemann G x).flip Y).flip Z : E →L[ℝ] E) =
      christoffel G x Y ∘L christoffel G x Z - christoffel G x (christoffel G x Y Z) := by
    ext X
    rw [flip_apply, flip_apply, riemann_of_fderiv_comm hGs hT hG₂ hx, sub_apply, comp_apply,
      christoffel_comm hGs X Z, christoffel_comm hGs X (christoffel G x Y Z)]
  rw [ricci_apply, key]
  exact map_sub (LinearMap.trace ℝ E) _ _

section Orthonormal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [Fintype ι] in
/-- In a `G x`-orthonormal basis the coordinates are inner products: `b.repr v i = G(bᵢ, v)`. -/
theorem repr_eq_of_orthonormal (b : Module.Basis ι ℝ E)
    (hb : ∀ i j, G x (b i) (b j) = if i = j then 1 else 0) (v : E) (i : ι) :
    b.repr v i = G x (b i) v := by
  have h : b.coord i = ((G x (b i) : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ) :=
    b.ext fun j ↦ by simp [hb, Finsupp.single_apply, eq_comm]
  simpa using LinearMap.congr_fun h v

omit [FiniteDimensional ℝ E] in
/-- The trace in a `G x`-orthonormal basis: `tr f = ∑ᵢ G(bᵢ, f bᵢ)`. -/
theorem trace_eq_sum_of_orthonormal (b : Module.Basis ι ℝ E)
    (hb : ∀ i j, G x (b i) (b j) = if i = j then 1 else 0) (f : E →L[ℝ] E) :
    LinearMap.trace ℝ E (f : E →ₗ[ℝ] E) = ∑ i, G x (b i) (f (b i)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  simp [LinearMap.toMatrix_apply, repr_eq_of_orthonormal b hb]

/-- The scalar curvature in a `G x`-orthonormal basis: `S = ∑ᵢ Ric(bᵢ, bᵢ)`. -/
theorem scalarCurvature_eq_sum_of_orthonormal (hGx : ∀ v w, G x v w = G x w v)
    (hx : (G x).IsInvertible) (b : Module.Basis ι ℝ E)
    (hb : ∀ i j, G x (b i) (b j) = if i = j then 1 else 0) :
    scalarCurvature G x = ∑ i, ricci G x (b i) (b i) := by
  rw [scalarCurvature, trace_eq_sum_of_orthonormal b hb]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [comp_apply, hGx, hx.self_apply_inverse]

/-- **The scalar curvature of a field with totally symmetric derivative** in a `G x`-orthonormal
basis: with `T = DG(x)` and `τᵢ = ∑ⱼ T(bᵢ, bⱼ, bⱼ)`, `S = ¼ (|T|² - |τ|²)`. -/
theorem scalarCurvature_of_fderiv_comm_of_orthonormal
    (hGs : ∀ᶠ y in 𝓝 x, ∀ v w, G y v w = G y w v)
    (hT : ∀ᶠ y in 𝓝 x, ∀ u v w, fderiv ℝ G y u v w = fderiv ℝ G y v u w)
    (hG₂ : ContDiffAt ℝ 2 G x) (hx : (G x).IsInvertible) (b : Module.Basis ι ℝ E)
    (hb : ∀ i j, G x (b i) (b j) = if i = j then 1 else 0) :
    scalarCurvature G x = 4⁻¹ * (∑ i, ∑ j, ∑ k, fderiv ℝ G x (b i) (b j) (b k) ^ 2 -
      ∑ i, (∑ j, fderiv ℝ G x (b i) (b j) (b j)) ^ 2) := by
  have hGx := hGs.self_of_nhds
  have hT0 := hT.self_of_nhds
  have hΓ : ∀ v w c, G x (b c) (christoffel G x v w) = 2⁻¹ * fderiv ℝ G x v w (b c) :=
    fun v w c ↦ by rw [hGx, apply_christoffel_of_fderiv_comm hGs hT0 hx]
  have hexp : ∀ v, v = ∑ c, G x (b c) v • b c := fun v ↦ by
    conv_lhs => rw [← b.sum_repr v]
    simp only [repr_eq_of_orthonormal b hb]
  have h1 : ∀ Y, LinearMap.trace ℝ E ((christoffel G x Y ∘L christoffel G x Y : E →L[ℝ] E)) =
      4⁻¹ * ∑ a, ∑ c, fderiv ℝ G x Y (b a) (b c) ^ 2 := by
    intro Y
    rw [trace_eq_sum_of_orthonormal b hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [comp_apply, hexp (christoffel G x Y (b a)), map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_smul, map_smul, smul_eq_mul, hΓ, hΓ, fderiv_apply_comm₂₃ hGs Y (b c) (b a)]
    ring
  have h2 : ∀ Y, LinearMap.trace ℝ E ((christoffel G x (christoffel G x Y Y) : E →L[ℝ] E)) =
      4⁻¹ * ∑ c, fderiv ℝ G x Y Y (b c) * ∑ a, fderiv ℝ G x (b c) (b a) (b a) := by
    intro Y
    rw [trace_eq_sum_of_orthonormal b hb, hexp (christoffel G x Y Y)]
    simp only [hΓ, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  have hsym : ∀ i c, fderiv ℝ G x (b i) (b i) (b c) = fderiv ℝ G x (b c) (b i) (b i) :=
    fun i c ↦ by rw [fderiv_apply_comm₂₃ hGs, hT0]
  rw [scalarCurvature_eq_sum_of_orthonormal hGx hx b hb]
  simp only [ricci_of_fderiv_comm hGs hT hG₂ hx, h1, h2]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub]
  congr 2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [← Finset.sum_mul, sq]
  exact congrArg (· * _) (Finset.sum_congr rfl fun i _ ↦ hsym i c)

end Orthonormal

end Codazzi

end FiniteDimensional

section OrthonormalBasis

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] {ι : Type*} [DecidableEq ι]

/-- A family orthonormal for a bilinear form is linearly independent. -/
theorem linearIndependent_of_orthonormal (B : M →L[ℝ] M →L[ℝ] ℝ) {v : ι → M}
    (hv : ∀ i j, B (v i) (v j) = if i = j then 1 else 0) : LinearIndependent ℝ v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have := congrArg (B (v i)) hg
  simpa [map_sum, hv, hi] using this

/-- **Orthonormal bases exist** for a symmetric positive definite bilinear form on a
finite-dimensional real space. -/
theorem exists_orthonormal_basis [FiniteDimensional ℝ M] (B : M →L[ℝ] M →L[ℝ] ℝ)
    (hsymm : ∀ v w, B v w = B w v) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ M)) ℝ M,
      ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := ContinuousLinearMap.toLinearMap₁₂ B) ⟨fun x y ↦ by simp [hsymm]⟩
  have hp : ∀ i, 0 < B (v i) (v i) := fun i ↦ hpos _ (v.ne_zero i)
  refine ⟨v.isUnitSMul (w := fun i ↦ (√(B (v i) (v i)))⁻¹)
    (fun i ↦ (inv_pos.2 (Real.sqrt_pos.2 (hp i))).ne'.isUnit), fun i j ↦ ?_⟩
  simp only [Module.Basis.isUnitSMul_apply, map_smul, smul_apply, smul_eq_mul]
  split_ifs with h
  · subst h
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt (hp i).le, inv_mul_cancel₀ (hp i).ne']
  · have h0 : B (v i) (v j) = 0 := by simpa using hv h
    simp [h0]

end OrthonormalBasis

end PetzCurvature.Curvature
