import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# The weighted operator geometric mean

In a unital C⋆-algebra `A`, for strictly positive `P`, `Q` and `t ∈ ℝ`,

  `gmean t P Q = P^{1/2} (P^{-1/2} Q P^{-1/2})^t P^{1/2}`.

* `gmean_mono_right`: for `t ∈ [0, 1]` it is monotone in `Q` (Löwner–Heinz).
* `gmean_symm`: `gmean t P Q = gmean (1 - t) Q P`, so it is also monotone in `P`.
* `gmean_cfc`: for commuting arguments `φ(X)`, `ψ(X)` it is `(φ^{1-t} ψ^t)(X)`.

The symmetry rests on `rpow_mul_star_self`: `(C C⋆)^t = C (C⋆ C)^{t-1} C⋆` for invertible `C`,
proved with the unitary `U = C (C⋆C)^{-1/2}` and `StarAlgHomClass.map_cfc`.
-/

namespace WYD.GeomMean

open CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [StarOrderedRing A] in
theorem isStrictlyPositive_iff {a : A} : IsStrictlyPositive a ↔ 0 ≤ a ∧ IsUnit a :=
  IsStrictlyPositive.iff_of_unital

theorem isSelfAdjoint_rpow (a : A) (t : ℝ) : IsSelfAdjoint (a ^ t) :=
  IsSelfAdjoint.of_nonneg rpow_nonneg

theorem star_rpow (a : A) (t : ℝ) : star (a ^ t) = a ^ t := (isSelfAdjoint_rpow a t).star_eq

theorem rpow_mul_rpow {a : A} (ha : IsStrictlyPositive a) (x y : ℝ) :
    a ^ x * a ^ y = a ^ (x + y) := (rpow_add ha.isUnit).symm

theorem continuousOn_rpow_spectrum {a : A} (ha : IsStrictlyPositive a) (t : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ t) (spectrum ℝ a) :=
  ContinuousOn.rpow_const continuousOn_id fun _ hx => Or.inl (ha.spectrum_pos hx).ne'

/-- `rpow` commutes with conjugation by a unitary. -/
theorem rpow_unitary_conj (u : unitary A) {a : A} (ha : IsStrictlyPositive a) (t : ℝ) :
    ((u : A) * a * star (u : A)) ^ t = (u : A) * a ^ t * star (u : A) := by
  have hφ : ⇑(Unitary.conjStarAlgAut ℝ A u) = fun x => (u : A) * x * star (u : A) :=
    funext fun x => Unitary.conjStarAlgAut_apply u x
  have hc : Continuous (Unitary.conjStarAlgAut ℝ A u) := by
    rw [hφ]; fun_prop
  have h := StarAlgHomClass.map_cfc (S := ℝ) (Unitary.conjStarAlgAut ℝ A u) (fun x : ℝ => x ^ t) a
    (continuousOn_rpow_spectrum ha t) hc ha.isSelfAdjoint
    (by rw [hφ]; exact (ha.isSelfAdjoint.conjugate _))
  rw [hφ] at h
  simp only at h
  rw [rpow_eq_cfc_real ha.nonneg, h, rpow_eq_cfc_real (star_right_conjugate_nonneg ha.nonneg _)]

/-- For invertible `C`, `(C C⋆)^t = C (C⋆ C)^{t-1} C⋆`: with `D = C⋆ C` the element
`U = C D^{-1/2}` is unitary, `C = U D^{1/2}` and `C C⋆ = U D U⋆`. -/
theorem rpow_mul_star_self {C : A} (hC : IsUnit C) (t : ℝ) :
    (C * star C) ^ t = C * (star C * C) ^ (t - 1) * star C := by
  have hDp : IsStrictlyPositive (star C * C) :=
    isStrictlyPositive_iff.2 ⟨star_mul_self_nonneg C, hC.star.mul hC⟩
  set D := star C * C with hD
  set U := C * D ^ (-(1 / 2) : ℝ) with hU
  have hUU : star U * U = 1 := by
    calc star U * U = D ^ (-(1 / 2) : ℝ) * D * D ^ (-(1 / 2) : ℝ) := by
          rw [hU, star_mul, star_rpow, hD]; simp only [mul_assoc]
      _ = 1 := conjugate_rpow_neg_one_half D
  have hUunit : IsUnit U := hC.mul (IsStrictlyPositive.rpow D _ hDp).isUnit
  have hUU' : U * star U = 1 := by
    have : star U = ↑hUunit.unit⁻¹ := by
      calc star U = star U * (U * ↑hUunit.unit⁻¹) := by rw [IsUnit.mul_val_inv, mul_one]
        _ = ↑hUunit.unit⁻¹ := by rw [← mul_assoc, hUU, one_mul]
    rw [this, IsUnit.mul_val_inv]
  let u : unitary A := ⟨U, Unitary.mem_iff.2 ⟨hUU, hUU'⟩⟩
  have hCU : C = U * D ^ (1 / 2 : ℝ) := by
    rw [hU, mul_assoc, rpow_mul_rpow hDp, show -(1 / 2 : ℝ) + 1 / 2 = 0 by norm_num,
      rpow_zero D hDp.nonneg, mul_one]
  have hCC : C * star C = (u : A) * D * star (u : A) := by
    calc C * star C = U * D ^ (1 / 2 : ℝ) * star (U * D ^ (1 / 2 : ℝ)) := by rw [← hCU]
      _ = U * (D ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ)) * star U := by
          rw [star_mul, star_rpow]; simp only [mul_assoc]
      _ = (u : A) * D * star (u : A) := by
          rw [rpow_mul_rpow hDp, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, rpow_one D hDp.nonneg]
  rw [hCC, rpow_unitary_conj u hDp t]
  calc (u : A) * D ^ t * star (u : A)
      = U * (D ^ (1 / 2 : ℝ) * D ^ (t - 1) * D ^ (1 / 2 : ℝ)) * star U := by
        rw [rpow_mul_rpow hDp, rpow_mul_rpow hDp, show (1 / 2 : ℝ) + (t - 1) + 1 / 2 = t by ring]
    _ = U * D ^ (1 / 2 : ℝ) * D ^ (t - 1) * star (U * D ^ (1 / 2 : ℝ)) := by
        rw [star_mul U, star_rpow]; simp only [mul_assoc]
    _ = C * D ^ (t - 1) * star C := by rw [← hCU]

/-- The weighted geometric mean `P #_t Q = P^{1/2} (P^{-1/2} Q P^{-1/2})^t P^{1/2}`. -/
noncomputable def gmean (t : ℝ) (P Q : A) : A :=
  P ^ (1 / 2 : ℝ) * (P ^ (-(1 / 2) : ℝ) * Q * P ^ (-(1 / 2) : ℝ)) ^ t * P ^ (1 / 2 : ℝ)

/-- Monotone in the second argument, for `t ∈ [0, 1]` (Löwner–Heinz). -/
theorem gmean_mono_right {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (P : A) {Q Q' : A} (h : Q ≤ Q') :
    gmean t P Q ≤ gmean t P Q' :=
  IsSelfAdjoint.conjugate_le_conjugate
    (rpow_le_rpow ht (IsSelfAdjoint.conjugate_le_conjugate h (isSelfAdjoint_rpow P _)))
    (isSelfAdjoint_rpow P _)

omit [PartialOrder A] [StarOrderedRing A] in
/-- The algebra behind the symmetry of the geometric mean, with `p = P^{1/2}`, `p' = P^{-1/2}`,
`q = Q^{1/2}`, `q' = Q^{-1/2}`. -/
theorem gmean_symm_aux [PartialOrder A] [StarOrderedRing A] {p p' q q' P Q : A}
    (hp : p * p' = 1) (hp' : p' * p = 1) (hq : q * q' = 1) (hq' : q' * q = 1)
    (hP : p * p = P) (hQ : q * q = Q) (sp' : star p' = p') (sq : star q = q) (t : ℝ) :
    p * (p' * Q * p') ^ t * p = q * (q' * P * q') ^ (1 - t) * q := by
  have hC : IsUnit (p' * q) :=
    (Units.isUnit ⟨p', p, hp', hp⟩).mul (Units.isUnit ⟨q, q', hq, hq'⟩)
  have starC : star (p' * q) = q * p' := by rw [star_mul, sq, sp']
  have hCC : p' * q * star (p' * q) = p' * Q * p' := by
    rw [starC, ← hQ]; simp only [mul_assoc]
  have hE : IsStrictlyPositive (star (p' * q) * (p' * q)) :=
    isStrictlyPositive_iff.2 ⟨star_mul_self_nonneg _, hC.star.mul hC⟩
  have hpX : ∀ X, p * (p' * X) = X := fun X => by rw [← mul_assoc, hp, one_mul]
  have hq'X : ∀ X, q' * (q * X) = X := fun X => by rw [← mul_assoc, hq', one_mul]
  have hFE : q' * P * q' * (star (p' * q) * (p' * q)) = 1 := by
    rw [starC, ← hP]; simp only [mul_assoc, hq'X, hpX, hq']
  have hinv : (star (p' * q) * (p' * q)) ^ (-1 : ℝ) = q' * P * q' := by
    rw [← hE.isUnit.mul_left_inj, hFE]
    calc (star (p' * q) * (p' * q)) ^ (-1 : ℝ) * (star (p' * q) * (p' * q))
        = (star (p' * q) * (p' * q)) ^ (-1 : ℝ) * (star (p' * q) * (p' * q)) ^ (1 : ℝ) := by
          rw [rpow_one _ hE.nonneg]
      _ = 1 := by
          rw [rpow_mul_rpow hE, show (-1 : ℝ) + 1 = 0 by norm_num, rpow_zero _ hE.nonneg]
  have hpow : (star (p' * q) * (p' * q)) ^ (t - 1) = (q' * P * q') ^ (1 - t) := by
    rw [← hinv, rpow_rpow _ _ _ hE, show (-1 : ℝ) * (1 - t) = t - 1 by ring]
  rw [← hCC, rpow_mul_star_self hC t, hpow, starC]
  simp only [mul_assoc, hpX, hp', mul_one]

/-- `P #_t Q = Q #_{1-t} P`. -/
theorem gmean_symm {P Q : A} (hP : IsStrictlyPositive P) (hQ : IsStrictlyPositive Q) (t : ℝ) :
    gmean t P Q = gmean (1 - t) Q P := by
  have facts : ∀ a : A, IsStrictlyPositive a →
      a ^ (1 / 2 : ℝ) * a ^ (-(1 / 2) : ℝ) = 1 ∧ a ^ (-(1 / 2) : ℝ) * a ^ (1 / 2 : ℝ) = 1 ∧
        a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a := fun a ha => by
    refine ⟨?_, ?_, ?_⟩ <;> rw [rpow_mul_rpow ha]
    · rw [show (1 / 2 : ℝ) + -(1 / 2) = 0 by norm_num, rpow_zero a ha.nonneg]
    · rw [show -(1 / 2 : ℝ) + 1 / 2 = 0 by norm_num, rpow_zero a ha.nonneg]
    · rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, rpow_one a ha.nonneg]
  obtain ⟨hp, hp', hPP⟩ := facts P hP
  obtain ⟨hq, hq', hQQ⟩ := facts Q hQ
  exact gmean_symm_aux hp hp' hq hq' hPP hQQ (star_rpow _ _) (star_rpow _ _) t

theorem isStrictlyPositive_gmean {P Q : A} (hP : IsStrictlyPositive P) (hQ : IsStrictlyPositive Q)
    (t : ℝ) : IsStrictlyPositive (gmean t P Q) := by
  have hM : IsStrictlyPositive (P ^ (-(1 / 2) : ℝ) * Q * P ^ (-(1 / 2) : ℝ)) := by
    have h := (IsStrictlyPositive.rpow P (-(1 / 2)) hP).isUnit
    refine isStrictlyPositive_iff.2 ⟨?_, (h.mul hQ.isUnit).mul h⟩
    exact (isSelfAdjoint_rpow P _).conjugate_nonneg hQ.nonneg
  have h := (IsStrictlyPositive.rpow P (1 / 2) hP).isUnit
  refine isStrictlyPositive_iff.2 ⟨?_, (h.mul (IsStrictlyPositive.rpow _ t hM).isUnit).mul h⟩
  exact (isSelfAdjoint_rpow P _).conjugate_nonneg rpow_nonneg

/-- Jointly monotone, for `t ∈ [0, 1]`. -/
theorem gmean_mono {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {P P' Q Q' : A}
    (hP : IsStrictlyPositive P) (hQ' : IsStrictlyPositive Q') (hPP : P ≤ P') (hQQ : Q ≤ Q') :
    gmean t P Q ≤ gmean t P' Q' := by
  have hP' := hP.of_le hPP
  have ht' : 1 - t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  calc gmean t P Q ≤ gmean t P Q' := gmean_mono_right ht P hQQ
    _ = gmean (1 - t) Q' P := gmean_symm hP hQ' t
    _ ≤ gmean (1 - t) Q' P' := gmean_mono_right ht' Q' hPP
    _ = gmean t P' Q' := by rw [gmean_symm hP' hQ' t]

theorem real_gmean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    a ^ (1 / 2 : ℝ) * (a ^ (-(1 / 2) : ℝ) * b * a ^ (-(1 / 2) : ℝ)) ^ t * a ^ (1 / 2 : ℝ) =
      a ^ (1 - t) * b ^ t := by
  have h1 : a ^ (-(1 / 2) : ℝ) * b * a ^ (-(1 / 2) : ℝ) = a ^ (-1 : ℝ) * b := by
    rw [mul_comm _ b, mul_assoc, ← Real.rpow_add ha]; norm_num; ring
  calc a ^ (1 / 2 : ℝ) * (a ^ (-(1 / 2) : ℝ) * b * a ^ (-(1 / 2) : ℝ)) ^ t * a ^ (1 / 2 : ℝ)
      = (a ^ (1 / 2 : ℝ) * a ^ (-1 * t) * a ^ (1 / 2 : ℝ)) * b ^ t := by
        rw [h1, Real.mul_rpow (by positivity) hb.le, ← Real.rpow_mul ha.le]; ring
    _ = a ^ (1 - t) * b ^ t := by
        rw [← Real.rpow_add ha, ← Real.rpow_add ha]; congr 2; ring

/-- For commuting arguments the geometric mean is the pointwise one. -/
theorem gmean_cfc {X : A} {φ ψ : ℝ → ℝ} (hφ : ContinuousOn φ (spectrum ℝ X))
    (hψ : ContinuousOn ψ (spectrum ℝ X)) (hφp : ∀ x ∈ spectrum ℝ X, 0 < φ x)
    (hψp : ∀ x ∈ spectrum ℝ X, 0 < ψ x) (t : ℝ) (hX : IsSelfAdjoint X := by cfc_tac) :
    gmean t (cfc φ X) (cfc ψ X) = cfc (fun x => φ x ^ (1 - t) * ψ x ^ t) X := by
  have hc : ∀ y : ℝ, ContinuousOn (fun x => φ x ^ y) (spectrum ℝ X) := fun y =>
    hφ.rpow_const fun x hx => Or.inl (hφp x hx).ne'
  have hm : ContinuousOn (fun x => φ x ^ (-(1 / 2) : ℝ) * ψ x * φ x ^ (-(1 / 2) : ℝ))
      (spectrum ℝ X) := ((hc _).mul hψ).mul (hc _)
  have hmp : ∀ x ∈ spectrum ℝ X, 0 < φ x ^ (-(1 / 2) : ℝ) * ψ x * φ x ^ (-(1 / 2) : ℝ) :=
    fun x hx => by have := hφp x hx; have := hψp x hx; positivity
  have e1 : cfc φ X ^ (1 / 2 : ℝ) = cfc (fun x => φ x ^ (1 / 2 : ℝ)) X := cfc_rpow hφp hφ
  have e2 : cfc φ X ^ (-(1 / 2) : ℝ) = cfc (fun x => φ x ^ (-(1 / 2) : ℝ)) X := cfc_rpow hφp hφ
  have e3 : cfc (fun x => φ x ^ (-(1 / 2) : ℝ)) X * cfc ψ X * cfc (fun x => φ x ^ (-(1 / 2) : ℝ)) X
      = cfc (fun x => φ x ^ (-(1 / 2) : ℝ) * ψ x * φ x ^ (-(1 / 2) : ℝ)) X := by
    rw [cfc_mul (fun x => φ x ^ (-(1 / 2) : ℝ) * ψ x) (fun x => φ x ^ (-(1 / 2) : ℝ)) X
      ((hc _).mul hψ) (hc _), cfc_mul (fun x => φ x ^ (-(1 / 2) : ℝ)) ψ X (hc _) hψ]
  have e4 : cfc (fun x => φ x ^ (-(1 / 2) : ℝ) * ψ x * φ x ^ (-(1 / 2) : ℝ)) X ^ t
      = cfc (fun x => (φ x ^ (-(1 / 2) : ℝ) * ψ x * φ x ^ (-(1 / 2) : ℝ)) ^ t) X :=
    cfc_rpow hmp hm
  have hmt : ContinuousOn (fun x => (φ x ^ (-(1 / 2) : ℝ) * ψ x * φ x ^ (-(1 / 2) : ℝ)) ^ t)
      (spectrum ℝ X) := hm.rpow_const fun x hx => Or.inl (hmp x hx).ne'
  have e5 : cfc (fun x => φ x ^ (1 / 2 : ℝ)) X *
      cfc (fun x => (φ x ^ (-(1 / 2) : ℝ) * ψ x * φ x ^ (-(1 / 2) : ℝ)) ^ t) X *
      cfc (fun x => φ x ^ (1 / 2 : ℝ)) X = cfc (fun x => φ x ^ (1 / 2 : ℝ) *
        (φ x ^ (-(1 / 2) : ℝ) * ψ x * φ x ^ (-(1 / 2) : ℝ)) ^ t * φ x ^ (1 / 2 : ℝ)) X := by
    rw [cfc_mul (fun x => φ x ^ (1 / 2 : ℝ) *
        (φ x ^ (-(1 / 2) : ℝ) * ψ x * φ x ^ (-(1 / 2) : ℝ)) ^ t) (fun x => φ x ^ (1 / 2 : ℝ)) X
        ((hc _).mul hmt) (hc _),
      cfc_mul (fun x => φ x ^ (1 / 2 : ℝ))
        (fun x => (φ x ^ (-(1 / 2) : ℝ) * ψ x * φ x ^ (-(1 / 2) : ℝ)) ^ t) X (hc _) hmt]
  unfold gmean
  rw [e1, e2, e3, e4, e5]
  exact cfc_congr fun x hx => real_gmean (hφp x hx) (hψp x hx) t

end WYD.GeomMean
