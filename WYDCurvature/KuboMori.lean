/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Paper.Conjecture81
import WYDCurvature.Petz.Main

/-!
# The case `p = 1`: the Kubo–Mori metric

At `p = 1` (and `p = ∞`) the function of Definition 6.1 is `f₁(x) = (x - 1)/log x`, so `WYD(1)` is the
Bogoliubov–Kubo–Mori metric. Its scalar curvature is Schur-increasing by Petz's conjecture, proved in the
PetzCurvature library (`PetzCurvature.scalarCurvature_bkmChart_le_of_isMajorizedBy`, imported here as the
`KM` copy, which builds on AlphaCurvature's copies of the shared files). This file identifies the paper's
metric at `p = 1` with PetzCurvature's BKM form (`bkmForm_eq`), and so completes `wyd_schurIncreasing` to
every `p ≤ -1` and `p ≥ 1/2`: the finite `p` for which the metric is monotone (Theorem 6.1).

## Main statements

* `bkmForm_eq`: at a positive definite `ρ`, PetzCurvature's `bkmForm ρ A B = ∫₀¹ Re tr(A R B R) ds`,
  `R = ((1 - s)ρ + s)⁻¹`, is `Re Tr (A c_{f₁}(L_ρ, R_ρ)(B))`.
* `kuboMori_schurIncreasing`, `kuboMori_strictly`: the scalar curvature of `WYD(1)` is Schur-increasing,
  strictly for different spectra.
* `wyd_schurIncreasing_all`, `wyd_strictly_all`: the same for every `p ≤ -1` and `p ≥ 1/2` (strictly for
  `p ≠ 2`).
* `scal_kuboMori_uniform`: at `I/n` the value is Petz's `(n² - 1)(n² - 4)/8`.
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set
open AlphaCurvature AlphaCurvature.Curvature AlphaCurvature.Quantum

namespace WYD.Paper

/-! ### The two libraries agree -/

/-- PetzCurvature's traceless Hermitian matrices are AlphaCurvature's. -/
theorem tracelessHermitian_eq (d : Type*) [Fintype d] [DecidableEq d] :
    PetzCurvature.tracelessHermitian d = tracelessHermitian d := by
  ext A
  rw [PetzCurvature.mem_tracelessHermitian, mem_tracelessHermitian]

/-- PetzCurvature's scalar curvature is AlphaCurvature's: the definitions are the same. -/
theorem scalarCurvature_petz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (G : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    PetzCurvature.Curvature.scalarCurvature G x = scalarCurvature G x :=
  rfl

/-! ### The metric at `p = 1` -/

theorem bkm_comm (x y : ℝ) : PetzCurvature.PetzKernel.bkm x y = PetzCurvature.PetzKernel.bkm y x := by
  unfold PetzCurvature.PetzKernel.bkm
  by_cases h : x = y
  · subst h; rfl
  · simp only [h, Ne.symm h, ite_false]
    rw [div_eq_div_iff (sub_ne_zero.2 h) (sub_ne_zero.2 (Ne.symm h))]
    ring

/-- `c_{f₁}` is the BKM kernel `(log x - log y)/(x - y)`, `1/x` on the diagonal. -/
theorem cMC_fGI_one_eq_bkm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    cMC (fGI 1) x y = PetzCurvature.PetzKernel.bkm x y := by
  by_cases h : x = y
  · subst h
    rw [PetzCurvature.PetzKernel.bkm_self, cMC, div_self hx.ne', fGI, ite_eq_left rfl, mul_one,
      one_div]
  · rw [cMC_fGI_one hx hy h, PetzCurvature.PetzKernel.bkm, ite_eq_right h]

variable {n : ℕ}

/-- **PetzCurvature's BKM form is the paper's metric at `p = 1`**, at every positive definite `ρ` and for
all matrices `A`, `B`. -/
theorem bkmForm_eq {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosDef) (A B : Matrix (Fin n) (Fin n) ℂ) :
    PetzCurvature.bkmForm ρ A B = (Matrix.trace (A * cLR (fGI 1) ρ B)).re := by
  have hU := hρ.1.eigenvectorUnitary.2
  set U := (hρ.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun i ↦ (hρ.1.eigenvalues i : ℂ) with hD
  have hρU : ρ = PetzCurvature.unitaryConjL hU D := by
    conv_lhs => rw [hρ.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have back : ∀ M : Matrix (Fin n) (Fin n) ℂ, PetzCurvature.unitaryConjL hU (star U * M * U) = M :=
    fun M ↦ by
      rw [← PetzCurvature.unitaryConjL_symm_apply hU, ContinuousLinearEquiv.apply_symm_apply]
  have e : PetzCurvature.bkmForm ρ A B =
      PetzCurvature.bkmForm D (star U * A * U) (star U * B * U) := by
    rw [← PetzCurvature.bkmForm_unitaryConjL_apply hU D, back, back, ← hρU]
  rw [e, hD, PetzCurvature.bkmForm_diagonal_eq_bkm hρ.eigenvalues_pos, trace_cLR _ hρ.1]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [cMC_fGI_one_eq_bkm (hρ.eigenvalues_pos j) (hρ.eigenvalues_pos i), bkm_comm]

/-- PetzCurvature's BKM chart is the paper's metric at `p = 1`, in the chart `z ↦ ρ₀ + z`. -/
theorem isWYD_one_bkmChart (ρ₀ : Matrix (Fin n) (Fin n) ℂ) :
    IsWYD 1 ρ₀ (PetzCurvature.bkmChart (tracelessHermitian (Fin n)) ρ₀) := by
  intro z hz A B
  rw [PetzCurvature.bkmChart_apply, bkmForm_eq hz]

/-- Two fields that are both the `WYD(1)` metric have the same scalar curvature. -/
theorem IsWYD.scalarCurvature_eq_bkm {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosDef)
    {G : tracelessHermitian (Fin n) →
      tracelessHermitian (Fin n) →L[ℝ] tracelessHermitian (Fin n) →L[ℝ] ℝ}
    (hG : IsWYD 1 ρ G) :
    scalarCurvature G 0 =
      scalarCurvature (PetzCurvature.bkmChart (tracelessHermitian (Fin n)) ρ) 0 := by
  refine scalarCurvature_congr ?_
  filter_upwards [eventually_posDef_chart (V := tracelessHermitian (Fin n)) hρ fun v hv ↦
    (mem_tracelessHermitian.1 hv).1] with z hz
  ext A B
  rw [hG z hz, isWYD_one_bkmChart ρ z hz]

/-! ### Petz's theorem, in the paper's terms -/

section Main

variable {ρ σ : Matrix (Fin n) (Fin n) ℂ}

/-- The scalar curvature of the Kubo–Mori metric in the chart `z ↦ ρ + z`, on AlphaCurvature's
traceless Hermitian matrices, is PetzCurvature's. -/
theorem scalarCurvature_bkmChart_eq (ρ : Matrix (Fin n) (Fin n) ℂ) :
    scalarCurvature (PetzCurvature.bkmChart (tracelessHermitian (Fin n)) ρ) 0 =
      PetzCurvature.Curvature.scalarCurvature
        (PetzCurvature.bkmChart (PetzCurvature.tracelessHermitian (Fin n)) ρ) 0 := by
  rw [tracelessHermitian_eq]
  rfl

/-- The strict form at `p = 1`, in charts. -/
theorem kuboMori_strictly_chart (hρ : ρ.PosDef) (hσ : σ.PosDef) (hρt : ρ.trace = 1)
    (hσt : σ.trace = 1) (hmix : MoreMixed hρ.1.eigenvalues hσ.1.eigenvalues)
    (hne : ∀ τ : Equiv.Perm (Fin n), hρ.1.eigenvalues ∘ τ ≠ hσ.1.eigenvalues)
    {G G' : tracelessHermitian (Fin n) →
      tracelessHermitian (Fin n) →L[ℝ] tracelessHermitian (Fin n) →L[ℝ] ℝ}
    (hG : IsWYD 1 ρ G) (hG' : IsWYD 1 σ G') : scalarCurvature G' 0 < scalarCurvature G 0 := by
  rw [hG.scalarCurvature_eq_bkm hρ, hG'.scalarCurvature_eq_bkm hσ, scalarCurvature_bkmChart_eq,
    scalarCurvature_bkmChart_eq]
  exact PetzCurvature.scalarCurvature_bkmChart_lt_of_isMajorizedBy hρ hσ hρt hσt
    (IsMajorizedBy.comp_equiv ((moreMixed_iff _ _).1 hmix) _) hne

/-- The non-strict form at `p = 1`, in charts; equal spectra are included. -/
theorem kuboMori_schurIncreasing_chart (hρ : ρ.PosDef) (hσ : σ.PosDef) (hρt : ρ.trace = 1)
    (hσt : σ.trace = 1) (hmix : MoreMixed hρ.1.eigenvalues hσ.1.eigenvalues)
    {G G' : tracelessHermitian (Fin n) →
      tracelessHermitian (Fin n) →L[ℝ] tracelessHermitian (Fin n) →L[ℝ] ℝ}
    (hG : IsWYD 1 ρ G) (hG' : IsWYD 1 σ G') : scalarCurvature G' 0 ≤ scalarCurvature G 0 := by
  rw [hG.scalarCurvature_eq_bkm hρ, hG'.scalarCurvature_eq_bkm hσ, scalarCurvature_bkmChart_eq,
    scalarCurvature_bkmChart_eq]
  exact PetzCurvature.scalarCurvature_bkmChart_le_of_isMajorizedBy hρ hσ hρt hσt
    (IsMajorizedBy.comp_equiv ((moreMixed_iff _ _).1 hmix) _)

end Main

/-! ### On `D¹ₙ` -/

section Global

variable {p : ℝ} {g : FormField n}

/-- **The scalar curvature of the Kubo–Mori metric `WYD(1)` is Schur-increasing on `D¹ₙ`.** -/
theorem kuboMori_schurIncreasing (hg : IsWYDMetric 1 g) : SchurIncreasingOn (density n) (scal g) := by
  rintro A ⟨hA, hAt⟩ B ⟨hB, hBt⟩ ⟨_, _, hmix⟩
  exact kuboMori_schurIncreasing_chart hA hB hAt hBt hmix (hg.chart hAt) (hg.chart hBt)

/-- **It is strictly Schur-increasing.** -/
theorem kuboMori_strictly (hg : IsWYDMetric 1 g) : StrictSchurIncreasingOn (density n) (scal g) := by
  rintro A ⟨hA, hAt⟩ B ⟨hB, hBt⟩ ⟨_, _, hmix⟩ hne
  exact kuboMori_strictly_chart hA hB hAt hBt hmix (fun τ h ↦ hne ⟨_, _, τ, h⟩)
    (hg.chart hAt) (hg.chart hBt)

/-- **The scalar curvature of the `WYD(p)` metric is Schur-increasing on `D¹ₙ` for every `p ≤ -1` and
every `p ≥ 1/2`**, every `n`: all the finite `p` for which the metric is monotone (Theorem 6.1).
`p = ∞` gives the same metric as `p = 1`. -/
theorem wyd_schurIncreasing_all (hp : p ≤ -1 ∨ 1 / 2 ≤ p) (hg : IsWYDMetric p g) :
    SchurIncreasingOn (density n) (scal g) := by
  by_cases h1 : p = 1
  · subst h1
    exact kuboMori_schurIncreasing hg
  · exact wyd_schurIncreasing hp h1 hg

/-- **Strictly**, for the same `p` except `p = 2`, where it is constant (`scal_wigner_yanase`). -/
theorem wyd_strictly_all (hp : p ≤ -1 ∨ 1 / 2 ≤ p) (h2 : p ≠ 2) (hg : IsWYDMetric p g) :
    StrictSchurIncreasingOn (density n) (scal g) := by
  by_cases h1 : p = 1
  · subst h1
    exact kuboMori_strictly hg
  · exact wyd_strictly hp h1 h2 hg

/-! ### Sanity checks at `p = 1` -/

/-- The metric exists at `p = 1`: PetzCurvature's BKM form, restricted to the tangent spaces. -/
theorem exists_isWYDMetric_one : ∃ g : FormField n, IsWYDMetric 1 g :=
  ⟨fun ρ ↦ (PetzCurvature.bkmForm ρ).bilinearComp (tracelessHermitian (Fin n)).subtypeL
      (tracelessHermitian (Fin n)).subtypeL,
    fun _ hρ A B ↦ bkmForm_eq hρ.1 A B⟩

/-- The `WYD(1)` metric is symmetric. -/
theorem IsWYDMetric.symm_one (hg : IsWYDMetric 1 g) {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ ∈ density n) (A B : tracelessHermitian (Fin n)) : g ρ A B = g ρ B A := by
  rw [hg ρ hρ, hg ρ hρ, ← bkmForm_eq hρ.1, ← bkmForm_eq hρ.1,
    PetzCurvature.bkmForm_comm (PetzCurvature.isUnit_bkmPath_of_posDef hρ.1)]

/-- The `WYD(1)` metric is positive definite at every density matrix. -/
theorem IsWYDMetric.pos_one (hg : IsWYDMetric 1 g) {ρ : Matrix (Fin n) (Fin n) ℂ}
    (hρ : ρ ∈ density n) {A : tracelessHermitian (Fin n)} (hA : A ≠ 0) : 0 < g ρ A A := by
  rw [hg ρ hρ, ← bkmForm_eq hρ.1]
  exact PetzCurvature.bkmForm_self_pos hρ.1 (mem_tracelessHermitian.1 A.2).1
    fun h ↦ hA (Subtype.ext h)

/-- At `I/n` the scalar curvature of `WYD(1)` is Petz's `(n² - 1)(n² - 4)/8` (his Theorem 6.2). -/
theorem scal_kuboMori_uniform [NeZero n] (hg : IsWYDMetric 1 g) :
    scal g ((n : ℂ)⁻¹ • 1) = ((n : ℝ) ^ 2 - 1) * ((n : ℝ) ^ 2 - 4) / 8 := by
  have hρ : ((n : ℂ)⁻¹ • 1 : Matrix (Fin n) (Fin n) ℂ) ∈ density n := by
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n)))
      have e : ((n : ℂ)⁻¹ • 1 : Matrix (Fin n) (Fin n) ℂ) = (((n : ℝ)⁻¹ : ℝ) : ℂ) • 1 := by
        push_cast; rfl
      rw [e]
      exact PosDef.one.smul (by exact_mod_cast this)
    · rw [trace_smul, trace_one, Fintype.card_fin, smul_eq_mul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne n))]
  rw [scal, IsWYD.scalarCurvature_eq_bkm hρ.1 (hg.chart hρ.2), scalarCurvature_bkmChart_eq]
  have h := PetzCurvature.scalarCurvature_bkmChart_traceState (d := Fin n)
  simp only [Fintype.card_fin] at h
  exact h

end Global

end WYD.Paper
