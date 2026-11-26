/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import AlphaCurvature.Quantum.Assembly
import WYDCurvature.Scalar
import WYDCurvature.Forms

/-!
# The WYD scalar curvature under mixing

* `wydMetric_apply`: the metric is `Re tr (D(ρ^β)[u] D(ρ^{1-β})[w]) / (β (1 - β))`, with
  `matPow` the functional calculus (`AlphaCurvature.Quantum.matPow_eq_cfc`).
* `scalarCurvature_wydMetric`: the closed form at every faithful state.
* `wyd_curvature_lt`: for `β ∈ [-1, 2] \ {0, ½, 1}`, if `hs_β` satisfies Dittmann's inequalities
  (64) and (65), then the scalar curvature strictly increases under mixing. (62) and (63) are proved.
* `wyd_curvature_lt_of_qubit`: two levels, no hypothesis.
-/

open scoped Matrix.Norms.L2Operator Topology ComplexOrder
open Matrix ContinuousLinearMap Filter Set
open AlphaCurvature AlphaCurvature.Curvature AlphaCurvature.Quantum

namespace WYD

variable {d : Type*} [Fintype d] [DecidableEq d] {β : ℝ}

/-! ### The metric at a general state -/

theorem fderiv_powChart_apply (s : ℝ) {V : Submodule ℝ (Matrix d d ℂ)} {ρ : Matrix d d ℂ}
    (hρ : ρ.PosDef) (w : V) : fderiv ℝ (fun z : V ↦ matPow s (V.subtypeL z + ρ)) 0 w =
      fderiv ℝ (matPow s) ρ w := by
  have hd := (contDiffAt_matPow s hρ 1).differentiableAt one_ne_zero
  rw [← chart_zero' (V := V) (ρ₀ := ρ)] at hd
  rw [fderiv_comp_chart hd, chart_zero']

theorem fderiv_matPow_conj (s : ℝ) {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    {l : d → ℝ} (hl : ∀ i, 0 < l i) (B : Matrix d d ℂ) :
    fderiv ℝ (matPow s) (U * diagS l * star U) (U * B * star U) =
      U * fderiv ℝ (matPow s) (diagS l) B * star U := by
  have hx := isUnit_logPath_of_posDef (posDef_diagonal_ofReal hl)
  exact fderiv_conj_of_eventually (Eventually.of_forall fun y ↦ matPow_conj s hU y)
    ((contDiffAt_matPow_of_isUnit s hx 1).differentiableAt one_ne_zero)
    ((contDiffAt_matPow_of_isUnit s (isUnit_logPath_conj hU hx) 1).differentiableAt one_ne_zero) B

/-- `Re tr (D(ρ^s)[u] D(ρ^t)[w])` is symmetric in `u, w`. -/
theorem hsForm_fderiv_matPow_comm (s t : ℝ) {ρ : Matrix d d ℂ} (hρ : ρ.PosDef)
    (u w : Matrix d d ℂ) :
    hsForm (fderiv ℝ (matPow s) ρ u) (fderiv ℝ (matPow t) ρ w) =
      hsForm (fderiv ℝ (matPow s) ρ w) (fderiv ℝ (matPow t) ρ u) := by
  obtain ⟨U, hU, l, hl, rfl⟩ := exists_unitary_diagonal_of_posDef hρ
  have hUs : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hsU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hc : ∀ B : Matrix d d ℂ, B = U * (star U * B * U) * star U := fun B ↦ by
    simp only [Matrix.mul_assoc, hsU, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hsU, Matrix.one_mul]
  have key : ∀ B C : Matrix d d ℂ,
      hsForm (fderiv ℝ (matPow s) (diagS l) B) (fderiv ℝ (matPow t) (diagS l) C) =
        hsForm (fderiv ℝ (matPow s) (diagS l) C) (fderiv ℝ (matPow t) (diagS l) B) := by
    intro B C
    simp only [hsForm_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum,
      fderiv_matPow_diagonal_apply _ hl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [powKernel_comm s (l j), powKernel_comm t (l i)]
    congr 1
    ring
  rw [hc u, hc w, fderiv_matPow_conj s hU hl, fderiv_matPow_conj s hU hl,
    fderiv_matPow_conj t hU hl, fderiv_matPow_conj t hU hl, hsForm_conj hU, hsForm_conj hU, key]

/-- **The Wigner–Yanase–Dyson metric**:
`g(u, w) = Re tr (D(ρ^β)[u] D(ρ^{1-β})[w]) / (β (1 - β))`. -/
theorem wydMetric_apply (V : Submodule ℝ (Matrix d d ℂ)) {ρ : Matrix d d ℂ} (hρ : ρ.PosDef)
    (u w : V) : wydMetric β V ρ 0 u w = (β * (1 - β))⁻¹ *
      (Matrix.trace (fderiv ℝ (matPow β) ρ u * fderiv ℝ (matPow (1 - β)) ρ w)).re := by
  have hf : ∀ w : V, fderiv ℝ (wydChart β V ρ) 0 w =
      (fderiv ℝ (matPow β) ρ w, fderiv ℝ (matPow (1 - β)) ρ w) := fun w ↦ by
    have h := (((contDiffAt_powChart (V := V) β hρ 1).differentiableAt
      one_ne_zero).hasFDerivAt.prodMk ((contDiffAt_powChart (V := V)
        (1 - β) hρ 1).differentiableAt one_ne_zero).hasFDerivAt)
    have h' : HasFDerivAt (wydChart β V ρ) _ 0 := h
    rw [h'.fderiv, ContinuousLinearMap.prod_apply, fderiv_powChart_apply _ hρ,
      fderiv_powChart_apply _ hρ]
  rw [wydMetric, pullback_apply, hf, hf, wydPairing_apply, ← hsForm_apply,
    hsForm_fderiv_matPow_comm β (1 - β) hρ w u, mul_inv]
  ring

/-- **The spectral form** of the metric at a diagonal state:
`∑ᵢⱼ c(lᵢ, lⱼ) |wᵢⱼ|²`, `c(x, y) = [x^β, y^β]₁ [x^{1-β}, y^{1-β}]₁ / (β (1 - β))`, where
`powKernel s x y = (x^s - y^s)/(x - y)`, and `s x^{s-1}` for `x = y`. -/
theorem wydMetric_diag_spectral {l : d → ℝ} (hl : ∀ i, 0 < l i) (w : tracelessHermitian d) :
    wydMetric β (tracelessHermitian d) (diagS l) 0 w w = ∑ i, ∑ j,
      (powKernel β (l i) (l j) * powKernel (1 - β) (l i) (l j)) / (β * (1 - β)) *
        ‖(w : Matrix d d ℂ) i j‖ ^ 2 := by
  have hw := (mem_tracelessHermitian.1 w.2).1
  rw [wydMetric_apply _ (posDef_diagonal_ofReal hl), Matrix.trace, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [fderiv_matPow_diagonal_apply _ hl, fderiv_matPow_diagonal_apply _ hl, mul_mul_mul_comm,
    ← hw.apply j i, Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq, powKernel_comm (1 - β) (l j)]
  ring

/-! ### Unitary invariance -/

theorem wydPairing_conj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    (A B C D : Matrix d d ℂ) :
    wydPairing β (U * A * star U, U * B * star U) (U * C * star U, U * D * star U) =
      wydPairing β (A, B) (C, D) := by
  simp only [wydPairing_apply, hsForm_conj hU]

theorem wydMetric_conj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ) (ρ₀ : Matrix d d ℂ) :
    wydMetric β (tracelessHermitian d) ρ₀ = pullback (tracelessConj (Unitary.star_mem hU))
      (wydMetric β (tracelessHermitian d) (star U * ρ₀ * U)) := by
  have hU' : star U ∈ Matrix.unitaryGroup d ℂ := Unitary.star_mem hU
  have hsU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  let T : (Matrix d d ℂ × Matrix d d ℂ) ≃L[ℝ] (Matrix d d ℂ × Matrix d d ℂ) :=
    (unitaryConj hU).prodCongr (unitaryConj hU)
  have hT : ∀ P, T P = (U * P.1 * star U, U * P.2 * star U) := fun P ↦ by
    simp [T, unitaryConj_apply]
  have hφ : wydChart β (tracelessHermitian d) ρ₀ = T ∘
      wydChart β (tracelessHermitian d) (star U * ρ₀ * U) ∘ tracelessConj hU' := by
    funext z
    have hz : U * ((tracelessHermitian d).subtypeL (tracelessConj hU' z) + star U * ρ₀ * U) *
        star U = (tracelessHermitian d).subtypeL z + ρ₀ := by
      simp only [Submodule.subtypeL_apply, coe_tracelessConj, star_star, Matrix.mul_add,
        Matrix.add_mul, ← Matrix.mul_assoc, hsU, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hsU, Matrix.mul_one]
    simp only [Function.comp_apply, wydChart, hT, ← matPow_conj _ hU, hz]
  ext z u w
  rw [wydMetric, pullback_apply, pullback_apply, (tracelessConj hU').fderiv, wydMetric,
    pullback_apply, hφ, T.comp_fderiv, (tracelessConj hU').comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hT]
  exact wydPairing_conj hU _ _ _ _

theorem scalarCurvature_wydMetric_conj {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ)
    {l : d → ℝ} (hl : ∀ i, 0 < l i) (h0 : β ≠ 0) (h1 : β ≠ 1) :
    scalarCurvature (wydMetric β (tracelessHermitian d) (U * diagS l * star U)) 0 =
      scalarCurvature (wydMetric β (tracelessHermitian d) (diagS l)) 0 := by
  have hUs : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hD : star U * (U * diagS l * star U) * U = diagS l := by
    simp only [← Matrix.mul_assoc, hUs, Matrix.one_mul]
    rw [Matrix.mul_assoc, hUs, Matrix.mul_one]
  have hU' : star U ∈ Matrix.unitaryGroup d ℂ := Unitary.star_mem hU
  rw [wydMetric_conj hU, hD]
  have hz : tracelessConj hU' 0 = 0 := map_zero _
  have hG := contDiffAt_pullback (n := 2) (G := fun _ ↦ (wydPairing β : _ →L[ℝ] _))
    (contDiffAt_const (x := wydChart β (tracelessHermitian d) (diagS l) 0))
    (contDiffAt_wydChart (β := β) (V := tracelessHermitian d) (posDef_diagonal_ofReal hl) 3)
  rw [scalarCurvature_pullback (tracelessConj hU').contDiff.contDiffAt
    ⟨tracelessConj hU', (tracelessConj hU').fderiv.symm⟩ (by rw [hz]; exact hG)
    (Eventually.of_forall fun y v w ↦ wydMetric_comm _ y v w)
    (by rw [hz]; exact LinearMap.BilinForm.isInvertible_of_pos fun _ hu ↦
      wydMetric_diag_self_pos hl h0 h1 hu), hz]

/-- **The WYD scalar curvature** at a faithful state, in the eigenvalues:
`S = ∑ᵢⱼₖ hs_β(λᵢ, λⱼ, λₖ) - ∑ᵢ hs_β(λᵢ, λᵢ, λᵢ) + (n² - 1)(n² - 2)/4`. -/
theorem scalarCurvature_wydMetric (h0 : β ≠ 0) (h1 : β ≠ 1) {ρ : Matrix d d ℂ} (hρ : ρ.PosDef)
    (htr : ρ.trace = 1) :
    scalarCurvature (wydMetric β (tracelessHermitian d) ρ) 0 =
      curvSum (wydHs β) hρ.1.eigenvalues +
        ((Fintype.card d : ℝ) ^ 2 - 1) * ((Fintype.card d : ℝ) ^ 2 - 2) / 4 := by
  have hxD : ρ = (hρ.1.eigenvectorUnitary : Matrix d d ℂ) * diagS hρ.1.eigenvalues *
      star (hρ.1.eigenvectorUnitary : Matrix d d ℂ) := by
    conv_lhs => rw [hρ.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have key := scalarCurvature_wydMetric_conj (β := β) hρ.1.eigenvectorUnitary.2
    hρ.eigenvalues_pos h0 h1
  rw [← hxD] at key
  have hsum : ∑ i, hρ.1.eigenvalues i = 1 := by
    have h : ((∑ i, hρ.1.eigenvalues i : ℝ) : ℂ) = 1 := by
      rw [← htr, hρ.1.trace_eq_sum_eigenvalues, Complex.ofReal_sum]
      rfl
    exact_mod_cast h
  rw [key, scalarCurvature_wydMetric_diagonal hρ.eigenvalues_pos hsum h0 h1]

/-! ### The theorems -/

/-- Dittmann's inequality (64) for `hs_β`. -/
def Ineq64 (β : ℝ) : Prop := ∀ x y l : ℝ, 0 < x → x < y → 0 < l →
  0 ≤ hsDeriv (wydHs β) x y l - hsDeriv (wydHs β) y x l

/-- Dittmann's inequality (65) for `hs_β`. -/
def Ineq65 (β : ℝ) : Prop := ∀ x y l m : ℝ, 0 < x → x < y → 0 < l → 0 < m →
  0 ≤ hsDeriv (wydHs β) x l m - hsDeriv (wydHs β) y l m

section Mixing

variable {ρ σ : Matrix d d ℂ}

/-- **The strict form of Gibilisco–Isola's Conjecture 8.1, from (64) and (65)**: let
`β ∈ [-1, 2] \ {0, ½, 1}` and suppose `hs_β` satisfies (64) and (65). If the eigenvalues of the
faithful state `ρ` are majorized by those of `σ` (`ρ` is more mixed) and the spectra differ, then
the scalar curvature of the WYD metric is strictly larger at `ρ`. -/
theorem wyd_curvature_lt (hm : -1 ≤ β) (hM : β ≤ 2) (h0 : β ≠ 0) (h1 : β ≠ 1)
    (h2 : 2 * β - 1 ≠ 0) (H64 : Ineq64 β) (H65 : Ineq65 β) (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hρt : ρ.trace = 1) (hσt : σ.trace = 1)
    (hmix : IsMajorizedBy (hρ.1.eigenvalues ∘ (Fintype.equivFin d).symm)
      (hσ.1.eigenvalues ∘ (Fintype.equivFin d).symm))
    (hne : ∀ π : Equiv.Perm d, hρ.1.eigenvalues ∘ π ≠ hσ.1.eigenvalues) :
    scalarCurvature (wydMetric β (tracelessHermitian d) σ) 0 <
      scalarCurvature (wydMetric β (tracelessHermitian d) ρ) 0 := by
  rw [scalarCurvature_wydMetric h0 h1 hρ hρt, scalarCurvature_wydMetric h0 h1 hσ hσt]
  have H : DittmannInequalities (wydHs β) :=
    ⟨fun x y hx hxy ↦ (wyd_62 hm hM h0 h1 h2 hx hxy).le,
      fun x y l hx hxy hl ↦ (wyd_63 hm hM h0 h1 h2 hx hxy hl).le, H64, H65⟩
  set e := Fintype.equivFin d
  have hne' : Majorization.sortInc (hρ.1.eigenvalues ∘ e.symm) ≠
      Majorization.sortInc (hσ.1.eigenvalues ∘ e.symm) := fun h ↦ by
    obtain ⟨π, hπ⟩ := Majorization.exists_comp_eq_of_sortInc_eq h
    refine hne ((e.trans π).trans e.symm) (funext fun i ↦ ?_)
    simpa using congrFun hπ (e i)
  have h := (isCurvFun_wydHs β).curvSum_lt_of_isMajorizedBy H
    (fun x y hx hxy ↦ wyd_62 hm hM h0 h1 h2 hx hxy) (fun _ ↦ hρ.eigenvalues_pos _)
    (fun _ ↦ hσ.eigenvalues_pos _) hmix hne'
  have c1 := curvSum_comp_equiv (hs := wydHs β) e.symm hρ.1.eigenvalues
  have c2 := curvSum_comp_equiv (hs := wydHs β) e.symm hσ.1.eigenvalues
  have h' : curvSum (wydHs β) (hσ.1.eigenvalues ∘ e.symm) <
      curvSum (wydHs β) (hρ.1.eigenvalues ∘ e.symm) := h
  linarith

end Mixing

section Qubit

variable {ρ σ : Matrix (Fin 2) (Fin 2) ℂ}

/-- The gradient for two levels needs (62) only. -/
theorem curvGrad_lt_of_two (hm : -1 ≤ β) (hM : β ≤ 2) (h0 : β ≠ 0) (h1 : β ≠ 1)
    (h2 : 2 * β - 1 ≠ 0) {z : Fin 2 → ℝ} (hz : ∀ i, 0 < z i) {a b : Fin 2} (hab : z a < z b) :
    curvGrad (wydHs β) z b < curvGrad (wydHs β) z a := by
  have hne : a ≠ b := fun h ↦ hab.ne (congrArg z h)
  have he : ∀ a b : Fin 2, a ≠ b → (Finset.univ.erase a).erase b = ∅ := by decide
  have h := (isCurvFun_wydHs β).curvGrad_sub_curvGrad z hne
  rw [he a b hne] at h
  simp only [Finset.sum_empty, mul_zero, add_zero] at h
  have := wyd_62 hm hM h0 h1 h2 (hz a) hab
  linarith

/-- **The qubit case, unconditionally**: on two-level states the scalar curvature of the WYD metric,
`β ∈ [-1, 2] \ {0, ½, 1}`, strictly increases under mixing. -/
theorem wyd_curvature_lt_of_qubit (hm : -1 ≤ β) (hM : β ≤ 2) (h0 : β ≠ 0) (h1 : β ≠ 1)
    (h2 : 2 * β - 1 ≠ 0) (hρ : ρ.PosDef) (hσ : σ.PosDef) (hρt : ρ.trace = 1) (hσt : σ.trace = 1)
    (hmix : IsMajorizedBy hρ.1.eigenvalues hσ.1.eigenvalues)
    (hne : ∀ π : Equiv.Perm (Fin 2), hρ.1.eigenvalues ∘ π ≠ hσ.1.eigenvalues) :
    scalarCurvature (wydMetric β (tracelessHermitian (Fin 2)) σ) 0 <
      scalarCurvature (wydMetric β (tracelessHermitian (Fin 2)) ρ) 0 := by
  rw [scalarCurvature_wydMetric h0 h1 hρ hρt, scalarCurvature_wydMetric h0 h1 hσ hσt]
  have hne' : Majorization.sortInc hρ.1.eigenvalues ≠ Majorization.sortInc hσ.1.eigenvalues :=
    fun h ↦ by
      obtain ⟨π, hπ⟩ := Majorization.exists_comp_eq_of_sortInc_eq h
      exact hne π hπ
  have h := lt_of_isMajorizedBy (U := {z : Fin 2 → ℝ | ∀ i, 0 < z i}) (F := curvSum (wydHs β))
    (grad := curvGrad (wydHs β))
    (by
      have : {z : Fin 2 → ℝ | ∀ i, 0 < z i} = Set.pi Set.univ fun _ ↦ Set.Ioi 0 := by
        ext z; simp
      rw [this]
      exact convex_pi fun _ _ ↦ convex_Ioi 0)
    (fun z hz π ↦ ⟨fun i ↦ hz (π i), curvSum_comp_equiv π z⟩)
    (fun z hz v ↦ by
      have h := (isCurvFun_wydHs β).hasDerivAt_curvSum (L := fun s ↦ z + s • v) (L' := v) (t := 0)
        (fun i ↦ by
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (z i))
        (fun i ↦ by simpa using hz i)
      simpa using h)
    (fun z hz hmono a b hab ↦ by
      rcases (hmono hab).lt_or_eq with h | h
      · exact (curvGrad_lt_of_two hm hM h0 h1 h2 hz h).le
      · exact (curvGrad_congr h).ge)
    (fun z hz _ a b hab ↦ curvGrad_lt_of_two hm hM h0 h1 h2 hz hab)
    hρ.eigenvalues_pos hσ.eigenvalues_pos hmix hne'
  linarith

end Qubit

end WYD

#print axioms WYD.wyd_curvature_lt
#print axioms WYD.wyd_curvature_lt_of_qubit
#print axioms WYD.scalarCurvature_wydMetric
