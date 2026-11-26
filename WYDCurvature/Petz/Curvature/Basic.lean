/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Trace
import WYDCurvature.Petz.ForMathlib.Basic

/-!
# Christoffel map and curvature

For a field `G : E → E →L[ℝ] E →L[ℝ] ℝ` of bilinear forms on a real normed space `E` (a metric in
a chart), this file defines the **Christoffel map** `christoffel G x : E →L[ℝ] E →L[ℝ] E`, the
**Riemann map** `riemann G x : E →L[ℝ] E →L[ℝ] E →L[ℝ] E` and, in finite dimension, the **Ricci
map** `ricci G x : E →L[ℝ] E →L[ℝ] ℝ` and the **scalar curvature** `scalarCurvature G x : ℝ`.
The definitions ask nothing of `G`, not even a signature, so they serve any nondegenerate metric.
Where `G x` is not invertible the Christoffel map is `0`, and where a field is not differentiable
its derivative is `0`. Each fact carries only the hypotheses it needs: invertibility of `G x` for
the defining identity of the Christoffel map, and symmetry of `G y` for `y` near `x` for its
symmetry.

## Main definitions

* `christoffelForm G x v w`: the covector `u ↦ ½ (D v w u + D w v u - D u v w)`,
  `D = fderiv ℝ G x` (the Christoffel symbols of the first kind).
* `christoffel G x`: the Christoffel map, `G x (Γ(v, w)) u = christoffelForm G x v w u`.
* `riemann G x`: the Riemann map, `R X Y Z = DΓ X Y Z - DΓ Y X Z + Γ X (Γ Y Z) - Γ Y (Γ X Z)`.
* `ricci G x`: the Ricci map, `Ric(Y, Z) = tr (X ↦ R X Y Z)`.
* `scalarCurvature G x`: the trace of `(G x)⁻¹ ∘ Ric`.

## Main statements

* `christoffel_spec`: the defining identity of the Christoffel map.
* `christoffelForm_comm`, `christoffel_comm`: its symmetry.
* `contDiffOn_christoffel`, `contDiffAt_christoffel`: smoothness of the Christoffel map.

## Implementation notes

The curvature conventions are `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`,
`Ric(Y, Z) = tr (X ↦ R(X, Y) Z)` and scalar curvature `tr_G Ric`, the conventions for which the
round unit sphere has scalar curvature `2`. For constant vector fields on `E`, `[X, Y] = 0` and
`∇_Y Z = Γ(Y, Z)`, which gives the formula of `riemann`.

The Christoffel map uses `ContinuousLinearMap.inverse` of `G x : E →L[ℝ] (E →L[ℝ] ℝ)` and needs
no finite dimension; the traces in `ricci` and `scalarCurvature` do. The smoothness of the
Christoffel map is proved in finite dimension, coordinate by coordinate (`contDiffOn_clm_apply`).

A space of trilinear maps with values in `ℝ`, such as the type of `fderiv ℝ G x`, carries the
instances of `ContinuousLinearMap` when it is elaborated from syntax and those of the operator
norm when it comes out of a lemma about a normed space `F := E →L[ℝ] E →L[ℝ] ℝ`, and instance
search does not identify the two: it finds no `Add`, `Sub` or `NormedAddCommGroup` on
`E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ` written out. So the file forms no sums of such maps:
`christoffelForm` is a covector for each pair `v, w`, `christoffel` is assembled in
`E →L[ℝ] E →L[ℝ] E`, and the lemmas about `fderiv ℝ G x` are applied with explicit arguments
(`fderiv_apply_comm_of_eventually`).

## References

* [O'Neill, *Semi-Riemannian Geometry, with Applications to Relativity*][oneill1983]
  (Levi-Civita connection, Christoffel symbols, curvature).
-/

open Filter ContinuousLinearMap
open scoped Topology

namespace PetzCurvature.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Derivatives of fields of bilinear maps -/

/-- If `f y` is a symmetric bilinear map for every `y` near `x`, then so is every directional
derivative of `f` at `x`. -/
theorem fderiv_apply_comm_of_eventually {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → E →L[ℝ] E →L[ℝ] F} {x : E} (hf : ∀ᶠ y in 𝓝 x, ∀ v w, f y v w = f y w v)
    (u v w : E) : fderiv ℝ f x u v w = fderiv ℝ f x u w v := by
  have h₁ : (fun y ↦ flipₗᵢ ℝ E E F (f y)) =ᶠ[𝓝 x] f :=
    hf.mono fun y hy ↦ by
      ext v w
      exact hy w v
  have h₂ := LinearIsometryEquiv.comp_fderiv (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] F)
    (iso := flipₗᵢ ℝ E E F) (f := f) (x := x)
  rw [Function.comp_def, h₁.fderiv_eq] at h₂
  have h₃ := congrArg (fun L ↦ L u v w) h₂
  simpa using h₃

/-- **The product rule** for `y ↦ G y (a y) (b y)`. -/
theorem fderiv_apply_apply {G : E → E →L[ℝ] E →L[ℝ] ℝ} {a b : E → E} {x : E}
    (hG : DifferentiableAt ℝ G x) (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (X : E) :
    fderiv ℝ (fun y ↦ G y (a y) (b y)) x X =
      fderiv ℝ G x X (a x) (b x) + G x (fderiv ℝ a x X) (b x) + G x (a x) (fderiv ℝ b x X) := by
  rw [fderiv_clm_apply (hG.clm_apply ha) hb, fderiv_clm_apply hG ha]
  simp only [add_apply, comp_apply, flip_apply]
  ring

/-! ### The Christoffel map -/

/-- The **Christoffel form** of a field `G` of bilinear forms at `x`, the Christoffel symbols of
the first kind: the covector `u ↦ ½ (D v w u + D w v u - D u v w)`, `D = fderiv ℝ G x`. -/
noncomputable def christoffelForm (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x v w : E) : E →L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • (fderiv ℝ G x v w + fderiv ℝ G x w v - ((fderiv ℝ G x).flip v).flip w)

/-- The value of the Christoffel form: `½ (D v w u + D w v u - D u v w)`, `D = fderiv ℝ G x`. -/
@[simp]
theorem christoffelForm_apply (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x v w u : E) :
    christoffelForm G x v w u =
      2⁻¹ * (fderiv ℝ G x v w u + fderiv ℝ G x w v u - fderiv ℝ G x u v w) := by
  simp [christoffelForm]

/-- The **Christoffel map** of a field `G` of bilinear forms at `x`: `christoffel G x v w` is the
vector `Γ(v, w)` with `G x (Γ(v, w)) u = christoffelForm G x v w u` for every `u`, where `G x` is
invertible (`christoffel_spec`), and `0` where it is not. -/
noncomputable def christoffel (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  (2⁻¹ : ℝ) • (compL ℝ E (E →L[ℝ] ℝ) E (G x).inverse ∘L fderiv ℝ G x +
    (compL ℝ E (E →L[ℝ] ℝ) E (G x).inverse ∘L fderiv ℝ G x).flip -
    compL ℝ E (E →L[ℝ] ℝ) E (G x).inverse ∘L
      ((flipₗᵢ ℝ E E ℝ : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) ∘L (fderiv ℝ G x).flip))

/-- The Christoffel map is `(G x).inverse` applied to the Christoffel form. -/
theorem christoffel_apply (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x v w : E) :
    christoffel G x v w = (G x).inverse (christoffelForm G x v w) := by
  simp [christoffel, christoffelForm]

variable {G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}

/-- **The defining identity of the Christoffel map**: where `G x` is invertible,
`G x (Γ(v, w)) u = ½ (D v w u + D w v u - D u v w)`. -/
theorem christoffel_spec (hx : (G x).IsInvertible) (v w u : E) :
    G x (christoffel G x v w) u = christoffelForm G x v w u := by
  rw [christoffel_apply, hx.self_apply_inverse]

/-- The Christoffel form is symmetric in `v, w` when `G y` is symmetric for every `y` near `x`. -/
theorem christoffelForm_comm (hG : ∀ᶠ y in 𝓝 x, ∀ v w, G y v w = G y w v) (v w : E) :
    christoffelForm G x v w = christoffelForm G x w v := by
  ext u
  simp only [christoffelForm_apply, fderiv_apply_comm_of_eventually hG u v w]
  ring

/-- **The Christoffel map is symmetric**, `Γ(v, w) = Γ(w, v)`, when `G y` is symmetric for every
`y` near `x`. -/
theorem christoffel_comm (hG : ∀ᶠ y in 𝓝 x, ∀ v w, G y v w = G y w v) (v w : E) :
    christoffel G x v w = christoffel G x w v := by
  rw [christoffel_apply, christoffel_apply, christoffelForm_comm hG]

/-- The **Riemann map** of a field `G` of bilinear forms at `x`, in the convention
`R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`: with `Γ = christoffel G x` and
`DΓ = fderiv ℝ (christoffel G) x`,
`R X Y Z = DΓ X Y Z - DΓ Y X Z + Γ X (Γ Y Z) - Γ Y (Γ X Z)` (`riemann_apply`). This is the
formula for constant vector fields `X`, `Y`, `Z` on `E`, for which `[X, Y] = 0` and
`∇_Y Z = Γ(Y, Z)`; since `R` is tensorial, it determines `R` at `x`. -/
noncomputable def riemann (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  fderiv ℝ (christoffel G) x - (fderiv ℝ (christoffel G) x).flip +
    (compL ℝ E E E).bilinearComp (christoffel G x) (christoffel G x) -
    ((compL ℝ E E E).bilinearComp (christoffel G x) (christoffel G x)).flip

/-- The value of the Riemann map:
`R X Y Z = DΓ X Y Z - DΓ Y X Z + Γ X (Γ Y Z) - Γ Y (Γ X Z)`. -/
@[simp]
theorem riemann_apply (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x X Y Z : E) :
    riemann G x X Y Z = fderiv ℝ (christoffel G) x X Y Z - fderiv ℝ (christoffel G) x Y X Z +
      christoffel G x X (christoffel G x Y Z) - christoffel G x Y (christoffel G x X Z) := by
  simp [riemann]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-! ### Smoothness of the Christoffel map -/

/-- **Smoothness of the Christoffel map**: in finite dimension, if `G` is `C^(k+1)` on an open set
`U` and `G y` is invertible for every `y ∈ U`, then `christoffel G` is `C^k` on `U`. -/
theorem contDiffOn_christoffel {U : Set E} {k : WithTop ℕ∞} (hU : IsOpen U)
    (hG : ContDiffOn ℝ (k + 1) G U) (hinv : ∀ y ∈ U, (G y).IsInvertible) :
    ContDiffOn ℝ k (christoffel G) U := by
  have hD := hG.fderiv_of_isOpen hU (m := k) le_rfl
  have hI : ContDiffOn ℝ k (fun y ↦ (G y).inverse) U := by
    intro y hy
    obtain ⟨e, he⟩ := hinv y hy
    have h₁ : ContDiffAt ℝ k ContinuousLinearMap.inverse (G y) := he ▸ contDiffAt_map_inverse e
    exact (h₁.comp y ((hG.contDiffAt (hU.mem_nhds hy)).of_le le_self_add)).contDiffWithinAt
  have h : ∀ a b c : E, ContDiffOn ℝ k (fun y ↦ fderiv ℝ G y a b c) U := fun a b c ↦
    ((hD.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const
  refine contDiffOn_clm_apply.2 fun v ↦ contDiffOn_clm_apply.2 fun w ↦ ?_
  simp only [christoffel_apply]
  refine hI.clm_apply (contDiffOn_clm_apply.2 fun u ↦ ?_)
  simp only [christoffelForm_apply]
  exact contDiffOn_const.mul (((h v w u).add (h w v u)).sub (h u v w))

/-- **Smoothness of the Christoffel map at a point**: in finite dimension, if `G` is `C^(k+1)` at
`x` (`k` a natural number) and `G x` is invertible, then `christoffel G` is `C^k` at `x`. -/
theorem contDiffAt_christoffel {k : ℕ} (hG : ContDiffAt ℝ (k + 1) G x)
    (hx : (G x).IsInvertible) : ContDiffAt ℝ k (christoffel G) x := by
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.1
    ((hG.continuousAt.eventually hx.eventually_nhds).and (hG.eventually (by simp)))
  exact (contDiffOn_christoffel hVo (fun y hy ↦ (hV hy).2.contDiffWithinAt)
    fun y hy ↦ (hV hy).1).contDiffAt (hVo.mem_nhds hxV)

/-! ### The Ricci map and the scalar curvature -/

/-- The **Ricci map** of a field `G` of bilinear forms at `x`: `ricci G x Y Z` is the trace of
`X ↦ riemann G x X Y Z` (`ricci_apply`). -/
noncomputable def ricci (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  compL ℝ E (E →L[ℝ] E) ℝ (LinearMap.toContinuousLinearMap (LinearMap.trace ℝ E ∘ₗ coeLM ℝ)) ∘L
    ((flipₗᵢ ℝ E E E : (E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E) ∘L (riemann G x).flip)

/-- The value of the Ricci map: the trace of `X ↦ riemann G x X Y Z`. -/
theorem ricci_apply (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x Y Z : E) :
    ricci G x Y Z = LinearMap.trace ℝ E (((riemann G x).flip Y).flip Z : E →L[ℝ] E) :=
  rfl

/-- The **scalar curvature** of a field `G` of bilinear forms at `x`, the trace of the Ricci map
with respect to `G x`: the trace of `(G x).inverse ∘L ricci G x : E →L[ℝ] E`. In a
`G x`-orthonormal basis it is `∑ᵢ Ric(bᵢ, bᵢ)` (`scalarCurvature_eq_sum_of_orthonormal`, in
`Curvature/Hessian.lean`). -/
noncomputable def scalarCurvature (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : ℝ :=
  LinearMap.trace ℝ E ((G x).inverse ∘L ricci G x : E →L[ℝ] E)

end FiniteDimensional

end PetzCurvature.Curvature
