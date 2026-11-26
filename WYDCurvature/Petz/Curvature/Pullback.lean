/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import WYDCurvature.Petz.Curvature.Basic
import WYDCurvature.Petz.ForMathlib.Basic

/-!
# Changes of chart

For a map `φ : E → F` between real normed spaces and a field `G : F → F →L[ℝ] F →L[ℝ] ℝ` of
bilinear forms (a metric in a chart), this file defines the **pullback**
`pullback φ G x u w = G (φ x) (Dφ x u) (Dφ x w)`, the metric in the chart `φ`, and proves that
curvature is a tensor. Write `A = Dφ x`, `B = D²φ x`, `Γ` and `R` for the Christoffel and Riemann
maps of `G` at `φ x`, and `Γ̃`, `R̃` for those of the pullback at `x`.

* The pullback is invertible where `G (φ x)` and `A` are, and `C^n` where `G` is `C^n` and `φ`
  is `C^(n+1)`.
* **The Christoffel map transforms** with an inhomogeneous term: `A (Γ̃(u, w)) = Γ(A u, A w) +
  B u w`, where `φ` is `C²` at `x`, `A` is invertible, `G` is differentiable at `φ x` and `G (φ x)`
  is symmetric and invertible.
* **Curvature is a tensor**: `A (R̃ X Y Z) = R (A X) (A Y) (A Z)`, the Ricci maps correspond,
  `Ric̃(Y, Z) = Ric(A Y, A Z)`, and the scalar curvatures are equal, where `φ` is `C³` at `x` with
  `A` invertible, `G` is `C²` at `φ x`, symmetric near `φ x` and invertible at `φ x`, in finite
  dimension.

The BKM metric on the density matrices is the pullback of the BKM form by an affine map
`z ↦ ρ₀ + z` (`pullback_affine`).

## Main definitions

* `pullback φ G`: the field `x ↦ G (φ x) (Dφ x ·) (Dφ x ·)`.

## Main statements

* `pullback_apply`, `isInvertible_pullback`, `differentiableAt_pullback`, `contDiffAt_pullback`,
  `fderiv_pullback_apply`: the pullback.
* `christoffelForm_pullback`, `christoffel_pullback`: the transformation law of the Christoffel
  map.
* `fderiv_christoffel_pullback_apply`: the derivative of the Christoffel map of the pullback.
* `riemann_pullback`, `ricci_pullback`, `scalarCurvature_pullback`: curvature is a tensor.
* `pullback_affine`: the pullback by an affine map.

## Implementation notes

* The definition asks nothing of `φ`: where `φ` is not differentiable, `Dφ x = 0` and the pullback
  at `x` is `0`. Each fact carries the hypotheses it needs. The transformation law of the
  Christoffel map is proved through its defining identity `christoffel_spec`, and needs `G (φ x)`
  symmetric at the point `φ x` only; the curvature laws differentiate it at the points near `x`,
  so they ask for symmetry near `φ x`.
* Fields of maps with values in written-out spaces such as `F →L[ℝ] F →L[ℝ] F` carry the
  instances of `ContinuousLinearMap` when elaborated from syntax, and instance search does not
  unify them with those of the operator norm in the composition lemmas
  (`HasFDerivAt.comp`, `DifferentiableAt.comp`); compare the implementation notes of
  `Curvature/Basic.lean`. The compositions are formed with the target type given explicitly or
  from hypotheses stated without a type ascription.

## References

* [O'Neill, *Semi-Riemannian Geometry, with Applications to Relativity*][oneill1983]
  (transformation of the Christoffel symbols under a change of coordinates, tensoriality of the
  curvature).
-/

open Filter ContinuousLinearMap
open scoped Topology

namespace PetzCurvature.Curvature

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The product rule** for `y ↦ c y (a y) (b y)`, `c` a field of bilinear maps. -/
private theorem fderiv_bilin_apply_apply {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁]
    [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃]
    [NormedSpace ℝ F₃] {c : E → F₁ →L[ℝ] F₂ →L[ℝ] F₃} {a : E → F₁} {b : E → F₂} {x : E}
    (hc : DifferentiableAt ℝ c x) (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (X : E) :
    fderiv ℝ (fun y ↦ c y (a y) (b y)) x X =
      fderiv ℝ c x X (a x) (b x) + c x (fderiv ℝ a x X) (b x) + c x (a x) (fderiv ℝ b x X) := by
  rw [fderiv_clm_apply (hc.clm_apply ha) hb, fderiv_clm_apply hc ha]
  simp only [add_apply, comp_apply, flip_apply]
  abel

/-! ### The pullback of a field of bilinear forms -/

/-- The **pullback** of a field `G` of bilinear forms on `F` by a map `φ : E → F`:
`pullback φ G x u w = G (φ x) (Dφ x u) (Dφ x w)`, `Dφ = fderiv ℝ φ` (`pullback_apply`). For a
change of chart `φ`, it is the metric `G` written in the new chart. -/
noncomputable def pullback (φ : E → F) (G : F → F →L[ℝ] F →L[ℝ] ℝ) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (G (φ x)).bilinearComp (fderiv ℝ φ x) (fderiv ℝ φ x)

/-- The value of the pullback: `G (φ x) (Dφ x u) (Dφ x w)`. -/
@[simp]
theorem pullback_apply (φ : E → F) (G : F → F →L[ℝ] F →L[ℝ] ℝ) (x u w : E) :
    pullback φ G x u w = G (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x w) :=
  rfl

/-- The pullback as a composition of fields of continuous linear maps:
`pullback φ G y = (· ∘L Dφ y) ∘L G (φ y) ∘L Dφ y`. -/
theorem pullback_eq_comp (φ : E → F) (G : F → F →L[ℝ] F →L[ℝ] ℝ) :
    pullback φ G = fun y ↦ ((compL ℝ E F ℝ).flip (fderiv ℝ φ y) ∘L G (φ y)) ∘L fderiv ℝ φ y := by
  ext y u w
  rfl

variable {φ : E → F} {G : F → F →L[ℝ] F →L[ℝ] ℝ} {x : E}

/-- The pullback is invertible where `G (φ x)` and `Dφ x` are. -/
theorem isInvertible_pullback (hG : (G (φ x)).IsInvertible) (hφ : (fderiv ℝ φ x).IsInvertible) :
    (pullback φ G x).IsInvertible :=
  hG.bilinearComp hφ hφ

/-- The pullback is differentiable at `x` where `G` is differentiable at `φ x` and `φ` and `Dφ`
are differentiable at `x`. -/
theorem differentiableAt_pullback (hG : DifferentiableAt ℝ G (φ x))
    (hφ : DifferentiableAt ℝ φ x) (hDφ : DifferentiableAt ℝ (fderiv ℝ φ) x) :
    DifferentiableAt ℝ (pullback φ G) x := by
  rw [pullback_eq_comp]
  exact (((differentiableAt_const _).clm_apply hDφ).clm_comp (hG.comp x hφ)).clm_comp hDφ

/-- **Smoothness of the pullback**: it is `C^n` at `x` where `G` is `C^n` at `φ x` and `φ` is
`C^(n+1)` at `x`. -/
theorem contDiffAt_pullback {n : WithTop ℕ∞} (hG : ContDiffAt ℝ n G (φ x))
    (hφ : ContDiffAt ℝ (n + 1) φ x) : ContDiffAt ℝ n (pullback φ G) x := by
  have hDφ : ContDiffAt ℝ n (fderiv ℝ φ) x := hφ.fderiv_right le_rfl
  rw [pullback_eq_comp]
  exact ((contDiffAt_const.clm_apply hDφ).clm_comp (hG.comp x (hφ.of_le le_self_add))).clm_comp
    hDφ

/-- **The derivative of the pullback**: with `A = Dφ x` and `B = D²φ x`,
`D(pullback φ G) X u w = DG (A X) (A u) (A w) + G (φ x) (B X u) (A w) + G (φ x) (A u) (B X w)`. -/
theorem fderiv_pullback_apply (hG : DifferentiableAt ℝ G (φ x)) (hφ : DifferentiableAt ℝ φ x)
    (hDφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (X u w : E) :
    fderiv ℝ (pullback φ G) x X u w =
      fderiv ℝ G (φ x) (fderiv ℝ φ x X) (fderiv ℝ φ x u) (fderiv ℝ φ x w) +
        G (φ x) (fderiv ℝ (fderiv ℝ φ) x X u) (fderiv ℝ φ x w) +
        G (φ x) (fderiv ℝ φ x u) (fderiv ℝ (fderiv ℝ φ) x X w) := by
  have hGφ : HasFDerivAt (fun y ↦ G (φ y)) ((fderiv ℝ G (φ x)).comp (fderiv ℝ φ x)) x :=
    HasFDerivAt.comp (G := F →L[ℝ] F →L[ℝ] ℝ) x hG.hasFDerivAt hφ.hasFDerivAt
  rw [← fderiv_clm_apply_apply_const (differentiableAt_pullback hG hφ hDφ)]
  simp only [pullback_apply]
  rw [fderiv_bilin_apply_apply hGφ.differentiableAt (hDφ.clm_apply (differentiableAt_const u))
    (hDφ.clm_apply (differentiableAt_const w)), hGφ.fderiv, fderiv_clm_apply_const hDφ,
    fderiv_clm_apply_const hDφ]
  rfl

/-! ### The Christoffel map of the pullback -/

/-- **The Christoffel form of the pullback**: where `φ` is `C²` at `x`, `G` is differentiable at
`φ x` and `G (φ x)` is symmetric, with `A = Dφ x` and `B = D²φ x`,
`christoffelForm (pullback φ G) x v w u = christoffelForm G (φ x) (A v) (A w) (A u) +
G (φ x) (B v w) (A u)`. -/
theorem christoffelForm_pullback (hφ : ContDiffAt ℝ 2 φ x) (hG : DifferentiableAt ℝ G (φ x))
    (hGs : ∀ v w, G (φ x) v w = G (φ x) w v) (v w u : E) :
    christoffelForm (pullback φ G) x v w u =
      christoffelForm G (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x w) (fderiv ℝ φ x u) +
        G (φ x) (fderiv ℝ (fderiv ℝ φ) x v w) (fderiv ℝ φ x u) := by
  have hφd : DifferentiableAt ℝ φ x := hφ.differentiableAt (by simp)
  have hDφ : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hs := hφ.isSymmSndFDerivAt (by simp)
  simp only [christoffelForm_apply, fderiv_pullback_apply hG hφd hDφ]
  rw [hs v u, hs w v, hs w u, hGs (fderiv ℝ φ x w)]
  ring

/-- **The Christoffel map transforms** under a change of chart: where `φ` is `C²` at `x` with
`Dφ x` invertible, `G` is differentiable at `φ x` and `G (φ x)` is symmetric and invertible,
`Dφ x (Γ̃(u, w)) = Γ(Dφ x u, Dφ x w) + D²φ x u w`, with `Γ̃ = christoffel (pullback φ G) x` and
`Γ = christoffel G (φ x)`. -/
theorem christoffel_pullback (hφ : ContDiffAt ℝ 2 φ x) (hA : (fderiv ℝ φ x).IsInvertible)
    (hG : DifferentiableAt ℝ G (φ x)) (hGs : ∀ v w, G (φ x) v w = G (φ x) w v)
    (hGx : (G (φ x)).IsInvertible) (u w : E) :
    fderiv ℝ φ x (christoffel (pullback φ G) x u w) =
      christoffel G (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x w) + fderiv ℝ (fderiv ℝ φ) x u w := by
  apply hGx.injective
  ext z
  obtain ⟨y, rfl⟩ := hA.surjective z
  have h := christoffel_spec (isInvertible_pullback hGx hA) u w y
  rw [pullback_apply, christoffelForm_pullback hφ hG hGs, ← christoffel_spec hGx] at h
  rw [h, map_add, add_apply]

section FiniteDimensional

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **The derivative of the Christoffel map of the pullback**: where `φ` is `C³` at `x` with
`Dφ x` invertible, `G` is `C²` at `φ x`, `G y` is symmetric for `y` near `φ x` and `G (φ x)` is
invertible, with `A = Dφ x`, `B = D²φ x`, `C = D³φ x`, `Γ`, `DΓ` the Christoffel map of `G` and
its derivative at `φ x`, and `Γ̃`, `DΓ̃` those of the pullback at `x`,
`A (DΓ̃ X Y Z) = DΓ (A X) (A Y) (A Z) + Γ (B X Y) (A Z) + Γ (A Y) (B X Z) + C X Y Z -
B X (Γ̃ Y Z)`. -/
theorem fderiv_christoffel_pullback_apply (hφ : ContDiffAt ℝ 3 φ x)
    (hA : (fderiv ℝ φ x).IsInvertible) (hG : ContDiffAt ℝ 2 G (φ x))
    (hGs : ∀ᶠ y in 𝓝 (φ x), ∀ v w, G y v w = G y w v) (hGx : (G (φ x)).IsInvertible)
    (X Y Z : E) :
    fderiv ℝ φ x (fderiv ℝ (christoffel (pullback φ G)) x X Y Z) =
      fderiv ℝ (christoffel G) (φ x) (fderiv ℝ φ x X) (fderiv ℝ φ x Y) (fderiv ℝ φ x Z) +
        christoffel G (φ x) (fderiv ℝ (fderiv ℝ φ) x X Y) (fderiv ℝ φ x Z) +
        christoffel G (φ x) (fderiv ℝ φ x Y) (fderiv ℝ (fderiv ℝ φ) x X Z) +
        fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x X Y Z -
        fderiv ℝ (fderiv ℝ φ) x X (christoffel (pullback φ G) x Y Z) := by
  have hφc : ContinuousAt φ x := hφ.continuousAt
  have hDφ2 : ContDiffAt ℝ 2 (fderiv ℝ φ) x := hφ.fderiv_right (by norm_num)
  have hφ2 : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 φ y :=
    (hφ.eventually (by simp)).mono fun y hy ↦ hy.of_le (by norm_num)
  have hAev : ∀ᶠ y in 𝓝 x, (fderiv ℝ φ y).IsInvertible :=
    hDφ2.continuousAt.eventually hA.eventually_nhds
  have hGev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ G (φ y) :=
    hφc.eventually ((hG.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp))
  have hGsev : ∀ᶠ y in 𝓝 x, ∀ v w, G (φ y) v w = G (φ y) w v := hφc.eventually hGs
  have hGxev : ∀ᶠ y in 𝓝 x, (G (φ y)).IsInvertible :=
    hφc.eventually (hG.continuousAt.eventually hGx.eventually_nhds)
  have hev : (fun y ↦ fderiv ℝ φ y (christoffel (pullback φ G) y Y Z)) =ᶠ[𝓝 x]
      fun y ↦ christoffel G (φ y) (fderiv ℝ φ y Y) (fderiv ℝ φ y Z) +
        fderiv ℝ (fderiv ℝ φ) y Y Z := by
    filter_upwards [hφ2, hAev, hGev, hGsev, hGxev] with y h₁ h₂ h₃ h₄ h₅
    exact christoffel_pullback h₁ h₂ h₃ h₄ h₅ Y Z
  have hφd : DifferentiableAt ℝ φ x := hφ.differentiableAt (by simp)
  have hD₁ : DifferentiableAt ℝ (fderiv ℝ φ) x := hDφ2.differentiableAt (by simp)
  have hD₂ : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ φ)) x :=
    (hDφ2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hP : ContDiffAt ℝ (1 + 1) (pullback φ G) x :=
    contDiffAt_pullback (by simpa [one_add_one_eq_two] using hG) (hφ.of_le (by norm_num))
  have hΓ' : DifferentiableAt ℝ (christoffel (pullback φ G)) x :=
    (contDiffAt_christoffel (k := 1) hP (isInvertible_pullback hGx hA)).differentiableAt
      one_ne_zero
  -- no type ascription: `hΓ` keeps the instances of the normed space of trilinear maps
  have hΓ := (contDiffAt_christoffel (k := 1) (by simpa [one_add_one_eq_two] using hG)
    hGx).differentiableAt one_ne_zero
  have hΓφ₀ := hΓ.hasFDerivAt.comp x hφd.hasFDerivAt
  have hΓφ : HasFDerivAt (fun y ↦ christoffel G (φ y))
      ((fderiv ℝ (christoffel G) (φ x)).comp (fderiv ℝ φ x)) x :=
    hΓφ₀
  have hΓYZ : DifferentiableAt ℝ (fun y ↦ christoffel (pullback φ G) y Y Z) x :=
    (hΓ'.clm_apply (differentiableAt_const Y)).clm_apply (differentiableAt_const Z)
  have hAY : DifferentiableAt ℝ (fun y ↦ fderiv ℝ φ y Y) x :=
    hD₁.clm_apply (differentiableAt_const Y)
  have hAZ : DifferentiableAt ℝ (fun y ↦ fderiv ℝ φ y Z) x :=
    hD₁.clm_apply (differentiableAt_const Z)
  have hBYZ : DifferentiableAt ℝ (fun y ↦ fderiv ℝ (fderiv ℝ φ) y Y Z) x :=
    (hD₂.clm_apply (differentiableAt_const Y)).clm_apply (differentiableAt_const Z)
  have h := congrArg (fun L : E →L[ℝ] F ↦ L X) hev.fderiv_eq
  rw [fderiv_clm_apply hD₁ hΓYZ, fderiv_fun_add
    ((hΓφ.differentiableAt.clm_apply hAY).clm_apply hAZ) hBYZ] at h
  simp only [add_apply] at h
  rw [fderiv_bilin_apply_apply hΓφ.differentiableAt hAY hAZ, hΓφ.fderiv,
    fderiv_clm_apply_const hD₁, fderiv_clm_apply_const hD₁,
    fderiv_clm_apply_apply_const hD₂] at h
  simp only [comp_apply, flip_apply, fderiv_clm_apply_apply_const hΓ'] at h
  rw [← h]
  abel

/-- **Curvature is a tensor**: where `φ` is `C³` at `x` with `Dφ x` invertible, `G` is `C²` at
`φ x`, `G y` is symmetric for `y` near `φ x` and `G (φ x)` is invertible, the Riemann map of the
pullback is that of `G` carried by `A = Dφ x`: `A (R̃ X Y Z) = R (A X) (A Y) (A Z)`, with
`R̃ = riemann (pullback φ G) x` and `R = riemann G (φ x)`. -/
theorem riemann_pullback (hφ : ContDiffAt ℝ 3 φ x) (hA : (fderiv ℝ φ x).IsInvertible)
    (hG : ContDiffAt ℝ 2 G (φ x)) (hGs : ∀ᶠ y in 𝓝 (φ x), ∀ v w, G y v w = G y w v)
    (hGx : (G (φ x)).IsInvertible) (X Y Z : E) :
    fderiv ℝ φ x (riemann (pullback φ G) x X Y Z) =
      riemann G (φ x) (fderiv ℝ φ x X) (fderiv ℝ φ x Y) (fderiv ℝ φ x Z) := by
  have hφ2 : ContDiffAt ℝ 2 φ x := hφ.of_le (by norm_num)
  have hΓ := christoffel_pullback hφ2 hA (hG.differentiableAt (by simp)) hGs.self_of_nhds hGx
  have hD := fderiv_christoffel_pullback_apply hφ hA hG hGs hGx
  have hB := hφ2.isSymmSndFDerivAt (by simp)
  have hC := (hφ.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt (by simp)
  simp only [riemann_apply, map_add, map_sub]
  rw [hD X Y Z, hD Y X Z, hΓ X (christoffel (pullback φ G) x Y Z),
    hΓ Y (christoffel (pullback φ G) x X Z), hΓ Y Z, hΓ X Z, hB Y X, hC Y X]
  simp only [map_add]
  abel

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The trace is invariant under conjugation by a continuous linear equivalence:
`tr (e⁻¹ ∘ T ∘ e) = tr T`. -/
private theorem trace_symm_comp_comp (e : E ≃L[ℝ] F) (T : F →L[ℝ] F) :
    LinearMap.trace ℝ E ((e.symm : F →L[ℝ] E) ∘L T ∘L (e : E →L[ℝ] F) : E →L[ℝ] E) =
      LinearMap.trace ℝ F (T : F →L[ℝ] F) := by
  have h : (((e.symm : F →L[ℝ] E) ∘L T ∘L (e : E →L[ℝ] F) : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      e.symm.toLinearEquiv.conj (T : F →ₗ[ℝ] F) :=
    LinearMap.ext fun _ ↦ rfl
  rw [h, LinearMap.trace_conj']

/-- **The Ricci map of the pullback**: under the hypotheses of `riemann_pullback`,
`Ric̃(Y, Z) = Ric(Dφ x Y, Dφ x Z)`. -/
theorem ricci_pullback (hφ : ContDiffAt ℝ 3 φ x) (hA : (fderiv ℝ φ x).IsInvertible)
    (hG : ContDiffAt ℝ 2 G (φ x)) (hGs : ∀ᶠ y in 𝓝 (φ x), ∀ v w, G y v w = G y w v)
    (hGx : (G (φ x)).IsInvertible) (Y Z : E) :
    ricci (pullback φ G) x Y Z = ricci G (φ x) (fderiv ℝ φ x Y) (fderiv ℝ φ x Z) := by
  have hR := riemann_pullback hφ hA hG hGs hGx
  obtain ⟨e, he⟩ := hA
  have key : (((riemann (pullback φ G) x).flip Y).flip Z : E →L[ℝ] E) =
      (e.symm : F →L[ℝ] E) ∘L (((riemann G (φ x)).flip (e Y)).flip (e Z)) ∘L (e : E →L[ℝ] F) := by
    ext X
    simp only [flip_apply, comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [← e.symm_apply_apply (riemann (pullback φ G) x X Y Z)]
    congr 1
    simpa [← he] using hR X Y Z
  rw [ricci_apply, ricci_apply, key, trace_symm_comp_comp, ← he]
  rfl

/-- **The scalar curvature is a scalar**: under the hypotheses of `riemann_pullback`, the scalar
curvature of the pullback at `x` is that of `G` at `φ x`. -/
theorem scalarCurvature_pullback (hφ : ContDiffAt ℝ 3 φ x) (hA : (fderiv ℝ φ x).IsInvertible)
    (hG : ContDiffAt ℝ 2 G (φ x)) (hGs : ∀ᶠ y in 𝓝 (φ x), ∀ v w, G y v w = G y w v)
    (hGx : (G (φ x)).IsInvertible) :
    scalarCurvature (pullback φ G) x = scalarCurvature G (φ x) := by
  have hRic := ricci_pullback hφ hA hG hGs hGx
  have hP := isInvertible_pullback hGx hA
  obtain ⟨e, he⟩ := hA
  have key : (pullback φ G x).inverse ∘L ricci (pullback φ G) x =
      (e.symm : F →L[ℝ] E) ∘L ((G (φ x)).inverse ∘L ricci G (φ x)) ∘L (e : E →L[ℝ] F) := by
    ext Y : 1
    rw [comp_apply, hP.inverse_apply_eq]
    ext Z
    simp only [pullback_apply, comp_apply, hRic, ← he, ContinuousLinearEquiv.coe_coe,
      e.apply_symm_apply, hGx.self_apply_inverse]
  rw [scalarCurvature, key, trace_symm_comp_comp]
  rfl

end FiniteDimensional

/-! ### Affine changes of chart -/

/-- The pullback by an affine map `y ↦ L y + c` is `G (L y + c)` composed with `L` on both
sides. -/
theorem pullback_affine (L : E →L[ℝ] F) (c : F) (G : F → F →L[ℝ] F →L[ℝ] ℝ) :
    pullback (fun y ↦ L y + c) G = fun y ↦ (G (L y + c)).bilinearComp L L := by
  ext y u w
  rw [pullback_apply, (L.hasFDerivAt.add_const c).fderiv]
  rfl

end PetzCurvature.Curvature
