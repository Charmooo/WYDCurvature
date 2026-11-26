import WYDCurvature.OperatorMonotone.GeomMean
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Operator monotone functions on `(0, ∞)`

In a unital C⋆-algebra `A`, `Mono A f` says `X ≤ Y → f(X) ≤ f(Y)` for strictly positive `X`,
`Anti A f` the reverse. The closure properties used for Gibilisco–Isola Theorem 6.1:

* `mono_id`, `anti_inv`, `Mono.affine`, `Anti.affine`, `Mono.inv`, `Anti.inv`, `Mono.congr`;
* `Mono.gmean`: `f^{1-t} g^t` is operator monotone if `f`, `g` are and `t ∈ [0, 1]`
  (the operator geometric mean, `WYD.GeomMean`);
* `Anti.integral`: averages over the unit square `I × I` of operator antitone kernels.
-/

namespace WYD.OpMono

open CFC Set MeasureTheory WYD.GeomMean unitInterval Function

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `f` is operator monotone on the strictly positive elements of `A`. -/
def Mono (f : ℝ → ℝ) : Prop :=
  ∀ ⦃X Y : A⦄, IsStrictlyPositive X → X ≤ Y → cfc f X ≤ cfc f Y

/-- `f` is operator antitone on the strictly positive elements of `A`. -/
def Anti (f : ℝ → ℝ) : Prop :=
  ∀ ⦃X Y : A⦄, IsStrictlyPositive X → X ≤ Y → cfc f Y ≤ cfc f X

variable {A}

/-- `f` is continuous and positive on `(0, ∞)`. -/
structure Good (f : ℝ → ℝ) : Prop where
  cont : ContinuousOn f (Ioi 0)
  pos : ∀ x, 0 < x → 0 < f x

theorem spectrum_subset {X : A} (hX : IsStrictlyPositive X) : spectrum ℝ X ⊆ Ioi 0 :=
  fun _ hx => hX.spectrum_pos hx

theorem Good.contSpec {f : ℝ → ℝ} (hf : Good f) {X : A} (hX : IsStrictlyPositive X) :
    ContinuousOn f (spectrum ℝ X) := hf.cont.mono (spectrum_subset hX)

theorem Good.posSpec {f : ℝ → ℝ} (hf : Good f) {X : A} (hX : IsStrictlyPositive X) :
    ∀ x ∈ spectrum ℝ X, 0 < f x := fun x hx => hf.pos x (spectrum_subset hX hx)

theorem Good.isStrictlyPositive {f : ℝ → ℝ} (hf : Good f) {X : A} (hX : IsStrictlyPositive X) :
    IsStrictlyPositive (cfc f X) :=
  (cfc_isStrictlyPositive_iff f X (hf.contSpec hX) hX.isSelfAdjoint).2 (hf.posSpec hX)

theorem Mono.congr {f g : ℝ → ℝ} (hf : Mono A f) (h : EqOn f g (Ioi 0)) : Mono A g := by
  intro X Y hX hXY
  have hY := hX.of_le hXY
  rw [← cfc_congr (h.mono (spectrum_subset hX)), ← cfc_congr (h.mono (spectrum_subset hY))]
  exact hf hX hXY

theorem Anti.congr {f g : ℝ → ℝ} (hf : Anti A f) (h : EqOn f g (Ioi 0)) : Anti A g := by
  intro X Y hX hXY
  have hY := hX.of_le hXY
  rw [← cfc_congr (h.mono (spectrum_subset hX)), ← cfc_congr (h.mono (spectrum_subset hY))]
  exact hf hX hXY

theorem mono_id : Mono A (fun x => x) := by
  intro X Y hX hXY
  have hY := hX.of_le hXY
  rw [cfc_id' ℝ X, cfc_id' ℝ Y]
  exact hXY

theorem anti_inv : Anti A (fun x => x⁻¹) := by
  intro X Y hX hXY
  have hY := hX.of_le hXY
  rw [cfc_ringInverse_id (R := ℝ) X hX.isUnit, cfc_ringInverse_id (R := ℝ) Y hY.isUnit]
  exact CStarAlgebra.ringInverse_le_ringInverse hXY hX

theorem cfc_affine {f : ℝ → ℝ} {X : A} (hX : IsStrictlyPositive X) (hf : ContinuousOn f (Ioi 0))
    (c d : ℝ) : cfc (fun x => c + d * f x) X = algebraMap ℝ A c + d • cfc f X := by
  have h := hf.mono (spectrum_subset hX)
  rw [cfc_const_add c (fun x => d * f x) X (continuousOn_const.mul h) hX.isSelfAdjoint,
    cfc_const_mul d f X h]

theorem Mono.affine {f : ℝ → ℝ} (hf : Mono A f) (hc : ContinuousOn f (Ioi 0)) (c : ℝ) {d : ℝ}
    (hd : 0 ≤ d) : Mono A (fun x => c + d * f x) := by
  intro X Y hX hXY
  rw [cfc_affine hX hc, cfc_affine (hX.of_le hXY) hc]
  exact add_le_add le_rfl (smul_le_smul_of_nonneg_left (hf hX hXY) hd)

theorem Anti.affine {f : ℝ → ℝ} (hf : Anti A f) (hc : ContinuousOn f (Ioi 0)) (c : ℝ) {d : ℝ}
    (hd : 0 ≤ d) : Anti A (fun x => c + d * f x) := by
  intro X Y hX hXY
  rw [cfc_affine hX hc, cfc_affine (hX.of_le hXY) hc]
  exact add_le_add le_rfl (smul_le_smul_of_nonneg_left (hf hX hXY) hd)

theorem cfc_inv' {f : ℝ → ℝ} (hg : Good f) {X : A} (hX : IsStrictlyPositive X) :
    cfc (fun x => (f x)⁻¹) X = Ring.inverse (cfc f X) :=
  cfc_inv f X (fun x hx => (hg.posSpec hX x hx).ne') (hg.contSpec hX) hX.isSelfAdjoint

theorem Mono.inv {f : ℝ → ℝ} (hf : Mono A f) (hg : Good f) : Anti A (fun x => (f x)⁻¹) := by
  intro X Y hX hXY
  have hY := hX.of_le hXY
  rw [cfc_inv' hg hX, cfc_inv' hg hY]
  exact CStarAlgebra.ringInverse_le_ringInverse (hf hX hXY) (hg.isStrictlyPositive hX)

theorem Anti.inv {f : ℝ → ℝ} (hf : Anti A f) (hg : Good f) : Mono A (fun x => (f x)⁻¹) := by
  intro X Y hX hXY
  have hY := hX.of_le hXY
  rw [cfc_inv' hg hX, cfc_inv' hg hY]
  exact CStarAlgebra.ringInverse_le_ringInverse (hf hX hXY) (hg.isStrictlyPositive hY)

theorem Good.inv {f : ℝ → ℝ} (hg : Good f) : Good (fun x => (f x)⁻¹) :=
  ⟨hg.cont.inv₀ fun x hx => (hg.pos x hx).ne', fun x hx => inv_pos.2 (hg.pos x hx)⟩

theorem Good.gmean {f g : ℝ → ℝ} (hf : Good f) (hg : Good g) (t : ℝ) :
    Good (fun x => f x ^ (1 - t) * g x ^ t) :=
  ⟨(hf.cont.rpow_const fun x hx => Or.inl (hf.pos x hx).ne').mul
      (hg.cont.rpow_const fun x hx => Or.inl (hg.pos x hx).ne'),
    fun x hx => by have := hf.pos x hx; have := hg.pos x hx; positivity⟩

/-- If `f` and `g` are operator monotone, so is `f^{1-t} g^t` for `t ∈ [0, 1]`. -/
theorem Mono.gmean {f g : ℝ → ℝ} (hf : Mono A f) (hg : Mono A g) (gf : Good f) (gg : Good g)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Mono A (fun x => f x ^ (1 - t) * g x ^ t) := by
  intro X Y hX hXY
  have hY := hX.of_le hXY
  rw [← gmean_cfc (gf.contSpec hX) (gg.contSpec hX) (gf.posSpec hX) (gg.posSpec hX) t
      hX.isSelfAdjoint,
    ← gmean_cfc (gf.contSpec hY) (gg.contSpec hY) (gf.posSpec hY) (gg.posSpec hY) t
      hY.isSelfAdjoint]
  exact gmean_mono ht (gf.isStrictlyPositive hX) (gg.isStrictlyPositive hY) (hf hX hXY)
    (hg hX hXY)

/-! ### Averaging over the unit square -/

/-- An average over `I × I` of operator antitone kernels is operator antitone. -/
theorem Anti.integral {k : I × I → ℝ → ℝ} (hk : ContinuousOn (uncurry k) (univ ×ˢ Ioi 0))
    (h : ∀ ω, Anti A (k ω)) : Anti A (fun x => ∫ ω, k ω x) := by
  have key : ∀ Z : A, IsStrictlyPositive Z →
      cfc (fun x => ∫ ω, k ω x) Z = ∫ ω, cfc (k ω) Z ∧ Integrable (fun ω => cfc (k ω) Z) := by
    intro Z hZ
    have hc : ContinuousOn (uncurry k) (univ ×ˢ spectrum ℝ Z) :=
      hk.mono (prod_mono subset_rfl (spectrum_subset hZ))
    obtain ⟨C, hC⟩ := (isCompact_univ.prod (spectrum.isCompact Z)).exists_bound_of_continuousOn hc
    have hb : ∀ᵐ ω ∂(volume : Measure (I × I)), ∀ z ∈ spectrum ℝ Z, ‖k ω z‖ ≤ C :=
      ae_of_all _ fun ω z hz => hC (ω, z) ⟨mem_univ _, hz⟩
    exact ⟨cfc_integral k (fun _ => C) Z hc hb (hasFiniteIntegral_const C) hZ.isSelfAdjoint,
      integrable_cfc k (fun _ => C) Z hc hb (hasFiniteIntegral_const C) hZ.isSelfAdjoint⟩
  intro X Y hX hXY
  have hY := hX.of_le hXY
  rw [(key X hX).1, (key Y hY).1]
  exact integral_mono (key Y hY).2 (key X hX).2 fun ω => h ω hX hXY

theorem continuousOn_integral {k : I × I → ℝ → ℝ} (hk : ContinuousOn (uncurry k) (univ ×ˢ Ioi 0)) :
    ContinuousOn (fun x => ∫ ω, k ω x) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : LocallyCompactSpace (Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  have hc : Continuous (uncurry fun (x : Ioi (0 : ℝ)) (ω : I × I) => k ω x) :=
    hk.comp_continuous (f := fun p : Ioi (0 : ℝ) × (I × I) => (p.2, (p.1 : ℝ))) (by fun_prop)
      fun p => ⟨mem_univ _, p.1.2⟩
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure (I × I))) hc
    isCompact_univ
  rw [Measure.restrict_univ] at h
  exact h

theorem integral_pos {k : I × I → ℝ → ℝ} (hk : ContinuousOn (uncurry k) (univ ×ˢ Ioi 0))
    (hpos : ∀ ω x, 0 < x → 0 < k ω x) {x : ℝ} (hx : 0 < x) : 0 < ∫ ω, k ω x := by
  have hc : Continuous (fun ω => k ω x) :=
    hk.comp_continuous (f := fun ω : I × I => (ω, x)) (by fun_prop) fun _ => ⟨mem_univ _, hx⟩
  have hint : Integrable (fun ω => k ω x) :=
    integrableOn_univ.1 (hc.continuousOn.integrableOn_compact isCompact_univ)
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hpos ω x hx).le) hint,
    show support (fun ω => k ω x) = univ from eq_univ_of_forall fun ω => (hpos ω x hx).ne',
    measure_univ]
  exact one_pos

/-- The harmonic average: if each `k ω` is positive and operator antitone, `(∫ k)⁻¹` is operator
monotone. -/
theorem mono_inv_integral {k : I × I → ℝ → ℝ} (hk : ContinuousOn (uncurry k) (univ ×ˢ Ioi 0))
    (hpos : ∀ ω x, 0 < x → 0 < k ω x) (h : ∀ ω, Anti A (k ω)) :
    Mono A (fun x => (∫ ω, k ω x)⁻¹) :=
  (Anti.integral hk h).inv ⟨continuousOn_integral hk, fun _ hx => integral_pos hk hpos hx⟩

theorem integral_unitInterval (F : ℝ → ℝ) : ∫ s : I, F s = ∫ s in (0 : ℝ)..1, F s := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe F

theorem integral_prod_unitInterval (F G : ℝ → ℝ) :
    ∫ ω : I × I, F ω.1 * G ω.2 = (∫ s in (0 : ℝ)..1, F s) * ∫ u in (0 : ℝ)..1, G u := by
  rw [← integral_unitInterval, ← integral_unitInterval]
  exact integral_prod_mul (fun s : I => F s) (fun u : I => G u)

end WYD.OpMono
