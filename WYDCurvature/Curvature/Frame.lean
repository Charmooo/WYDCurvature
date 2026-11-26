/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.Curvature.Gauss
import WYDCurvature.Curvature.Triples

/-!
# Scalar curvature from a split second fundamental form

`scalarCurvature_of_split`: the Gauss equation for a pullback metric whose second derivative splits
as `Γ ± N/2` in a frame with one unit normal `r`, `⟨Γ(v, w), r⟩ = -½ G(v, w)`:
`S = ¼ ∑ (|N(bᵢ, bⱼ)|² - ⟨N(bᵢ, bᵢ), N(bⱼ, bⱼ)⟩) + ¼ (m² - m)`.
`sum_frame_eq`: the sum over the tangent basis equals the sum over the frame with `r` adjoined.
-/

open ContinuousLinearMap Filter
open AlphaCurvature.Curvature
open scoped Topology

namespace WYD

section Split

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → F} {B : F →L[ℝ] F →L[ℝ] ℝ} {x : E} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scalarCurvature_of_split (hφ : ContDiffAt ℝ 3 φ x) (hB : ∀ v w, B v w = B w v)
    (hx : (pullback φ (fun _ ↦ B) x).IsInvertible) (b : Module.Basis ι ℝ E)
    (hb : ∀ i j, pullback φ (fun _ ↦ B) x (b i) (b j) = if i = j then 1 else 0)
    (g : M → M → ℝ) (X : E → M) (Γ N : E → E → M) (r : M)
    (hG : ∀ u w, B (fderiv ℝ φ x u) (fderiv ℝ φ x w) = g (X u) (X w))
    (hII : ∀ v w v' w', B (fderiv ℝ (fderiv ℝ φ) x v w) (fderiv ℝ (fderiv ℝ φ) x v' w') =
      g (Γ v w) (Γ v' w') - g (N v w) (N v' w') / 4)
    (hIA : ∀ v w u, B (fderiv ℝ (fderiv ℝ φ) x v w) (fderiv ℝ φ x u) = g (Γ v w) (X u))
    (hr : ∀ v w, g (Γ v w) r = -(g (X v) (X w)) / 2)
    (hp : ∀ v w v' w', g (Γ v w) (Γ v' w') = g (Γ v w) r * g (Γ v' w') r +
      ∑ i, g (Γ v w) (X (b i)) * g (Γ v' w') (X (b i))) :
    scalarCurvature (pullback φ fun _ ↦ B) x =
      (∑ i, ∑ j, g (N (b i) (b j)) (N (b i) (b j)) -
        ∑ i, ∑ j, g (N (b i) (b i)) (N (b j) (b j))) / 4 +
        ((Fintype.card ι : ℝ) ^ 2 - Fintype.card ι) / 4 := by
  set G := pullback φ fun _ ↦ B with hGdef
  have hGX : ∀ u w, G x u w = g (X u) (X w) := fun u w ↦ by
    rw [hGdef, pullback_apply]; exact hG u w
  have hspec : ∀ v w u, G x (christoffel G x v w) u = g (Γ v w) (X u) := fun v w u ↦ by
    rw [hGdef, pullback_const_christoffel hφ hB hx, hIA]
  have hpar : ∀ v w, G x v w = ∑ i, G x v (b i) * G x w (b i) := fun v w ↦ by
    have hs := pullback_const_comm (φ := φ) hB x
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, smul_eq_mul, repr_eq_of_orthonormal b hb, hs (b i) w, mul_comm]
  have hΓ : ∀ v w v' w', G x (christoffel G x v w) (christoffel G x v' w') =
      g (Γ v w) (Γ v' w') - G x v w * G x v' w' / 4 := fun v w v' w' ↦ by
    rw [hpar, hp, hr, hr]
    simp only [hspec, hGX]
    ring
  rw [hGdef, scalarCurvature_pullback_const hφ hB hx b hb, ← hGdef]
  simp only [hII, hΓ, hb]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [Finset.sum_comm (f := fun j i ↦ g (Γ (b j) (b j)) (Γ (b i) (b i))),
    Finset.sum_comm (f := fun j i ↦ g (N (b i) (b j)) (N (b i) (b j)))]
  simp
  ring

end Split

end WYD
