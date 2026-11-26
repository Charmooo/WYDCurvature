/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Newton.Num
import WYDCurvature.Newton.Certificates.C65_0_1
import WYDCurvature.Newton.Certificates.C65_0_2
import WYDCurvature.Newton.Certificates.C65_1_1
import WYDCurvature.Newton.Certificates.C65_1_2
import WYDCurvature.Newton.Certificates.C65_2_1
import WYDCurvature.Newton.Certificates.C65_2_2
import WYDCurvature.Newton.Certificates.C64_0_1
import WYDCurvature.Newton.Certificates.C64_0_2
import WYDCurvature.Newton.Certificates.C64_1_1
import WYDCurvature.Newton.Certificates.C64_1_2
import WYDCurvature.Newton.Certificates.C64_2_1
import WYDCurvature.Newton.Certificates.C64_2_2

/-!
# The Gibilisco–Isola conjecture for the Wigner–Yanase–Dyson metrics

The twelve Newton certificates give (64) and (65) for every `d ∈ [-3, 3] \ {-1, 0, 1}`
(`hypCond`), hence the strict form of **Gibilisco–Isola's Conjecture 8.1** for every
`β ∈ [-1, 2] \ {0, ½, 1}` and every dimension (`wyd_curvature_lt_of_isMajorizedBy`).

For `0 < d < 1` the parameter is `t = d/(1 - d)`, with `p = 1 + t`, `q = t`; for `1 < d ≤ 3` it is
`t = (3 - d)/(d - 1)`, with `p = 1 + t`, `q = 3 + t`. In both cases `d = q/p` and `t ≥ 0`.
-/

open Real Polynomial

namespace WYD

namespace Newton

theorem rep_X (t : ℝ) : Rep t (base, 1) t := by
  refine ⟨X, 0, ?_, ?_, ?_⟩ <;> simp

theorem rep_int_add_X (t : ℝ) (n : ℕ) : Rep t ((n : ℤ) + base, n + 1) (n + t) := by
  have h := (rep_int t n).add (rep_X t)
  simpa [PP.add] using h

theorem parRep1 (t : ℝ) : ParRep t par1 (1 + t) t :=
  ⟨by have h := rep_int_add_X t 1; simp only [Nat.cast_one] at h; exact h, rep_X t⟩

theorem parRep2 (t : ℝ) : ParRep t par2 (1 + t) (3 + t) :=
  ⟨by have h := rep_int_add_X t 1; simp only [Nat.cast_one] at h; exact h,
    by have h := rep_int_add_X t 3; simp only [Nat.cast_ofNat] at h; exact h⟩

theorem checks1 : Checks par1 1 :=
  ⟨cert65_0_1, cert65_1_1, cert65_2_1, cert64_0_1, cert64_1_1, cert64_2_1⟩

theorem checks2 : Checks par2 (-1) :=
  ⟨cert65_0_2, cert65_1_2, cert65_2_2, cert64_0_2, cert64_1_2, cert64_2_2⟩

end Newton

open Newton

/-- (64) and (65) for `0 < d ≤ 3`, `d ≠ 1`. -/
theorem hypCond_of_pos {d : ℝ} (hd : 0 < d) (hd3 : d ≤ 3) (hd1 : d ≠ 1) :
    HypCond64 d ∧ HypCond65 d := by
  have hsq : d ^ 2 ≠ 1 := fun h ↦ hd1 (by nlinarith)
  rcases lt_or_gt_of_ne hd1 with h | h
  · have h1 : 0 < 1 - d := by linarith
    have ht : 0 ≤ d / (1 - d) := by positivity
    have hp : 0 < 1 + d / (1 - d) := by positivity
    have hq : d / (1 - d) = (1 + d / (1 - d)) * d := by field_simp; ring
    have hG := G2_sign (q := d / (1 - d)) (s := 1) (by positivity) hd (Or.inl ⟨rfl, h⟩)
    exact ⟨hypCond64_of_checks (parRep1 _) ht hp hq hd.ne' hsq hG checks1,
      hypCond65_of_checks (parRep1 _) ht hp hq hd.ne' hsq rfl hG checks1⟩
  · have h1 : 0 < d - 1 := by linarith
    have ht : 0 ≤ (3 - d) / (d - 1) := div_nonneg (by linarith) h1.le
    have hp : 0 < 1 + (3 - d) / (d - 1) := by linarith
    have hq : 3 + (3 - d) / (d - 1) = (1 + (3 - d) / (d - 1)) * d := by field_simp; ring
    have hG := G2_sign (q := 3 + (3 - d) / (d - 1)) (s := -1) (by linarith) hd (Or.inr ⟨rfl, h⟩)
    exact ⟨hypCond64_of_checks (parRep2 _) ht hp hq hd.ne' hsq hG checks2,
      hypCond65_of_checks (parRep2 _) ht hp hq hd.ne' hsq rfl hG checks2⟩

theorem hypH_neg_param (d a b c : ℝ) : hypH (-d) a b c = hypH d a b c := by
  have e1 : ∀ x, hypPhi (-d) x = hypPhi d x := fun x ↦ by
    rw [hypPhi, hypPhi, neg_mul, sinh_neg, neg_div_neg_eq, neg_sq]
  have e2 : ∀ x, hypPhi' (-d) x = hypPhi' d x := fun x ↦ by
    rw [hypPhi', hypPhi', neg_mul, cosh_neg, neg_sq]
  have e3 : ∀ x, WYD.Ineq63.qubitK (-d) x = WYD.Ineq63.qubitK d x := fun x ↦ by
    rw [WYD.Ineq63.qubitK, WYD.Ineq63.qubitK, neg_mul, neg_mul, sinh_neg, cosh_neg, neg_mul, sub_neg_eq_add,
      ← neg_div_neg_eq, neg_neg, neg_add_rev, neg_neg]
    congr 1; ring
  simp only [hypH, e1, e2, e3]

/-- **(64) and (65)** for every `d ∈ [-3, 3] \ {-1, 0, 1}`. -/
theorem hypCond {d : ℝ} (hm : -3 ≤ d) (hM : d ≤ 3) (h0 : d ≠ 0) (h1 : d ≠ 1) (h1' : d ≠ -1) :
    HypCond64 d ∧ HypCond65 d := by
  rcases lt_or_gt_of_ne h0 with h | h
  · have hf : hypH d = hypH (-d) := by
      funext a b c; exact (hypH_neg_param d a b c).symm
    have := hypCond_of_pos (d := -d) (by linarith) (by linarith) fun e ↦ h1' (by linarith)
    unfold HypCond64 HypCond65 at this ⊢
    rwa [hf]
  · exact hypCond_of_pos h hM h1

variable {β : ℝ}

/-- **Dittmann's (64) for the WYD metrics.** -/
theorem wyd_64 (hm : -1 ≤ β) (hM : β ≤ 2) (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) :
    Ineq64 β :=
  ineq64_of_hyp h0 h1 h2 (hypCond (by linarith) (by linarith) h2 (fun h ↦ h1 (by linarith))
    fun h ↦ h0 (by linarith)).1

/-- **Dittmann's (65) for the WYD metrics.** -/
theorem wyd_65 (hm : -1 ≤ β) (hM : β ≤ 2) (h0 : β ≠ 0) (h1 : β ≠ 1) (h2 : 2 * β - 1 ≠ 0) :
    Ineq65 β :=
  ineq65_of_hyp h0 h1 h2 (hypCond (by linarith) (by linarith) h2 (fun h ↦ h1 (by linarith))
    fun h ↦ h0 (by linarith)).2

open scoped Matrix.Norms.L2Operator ComplexOrder in
open AlphaCurvature.Curvature AlphaCurvature.Quantum in
/-- **Gibilisco–Isola's Conjecture 8.1, strict form and whole range, `β = 1/p`** (the statement with the
definitions of the paper is `WYD.Paper.conjecture81`): let `β ∈ [-1, 2] \ {0, ½, 1}`. If the eigenvalues of the
faithful state `ρ` are majorized by those of `σ` (`ρ` is more mixed) and the spectra differ, then the
scalar curvature of the Wigner–Yanase–Dyson metric is strictly larger at `ρ`. -/
theorem wyd_curvature_lt_of_isMajorizedBy (hm : -1 ≤ β) (hM : β ≤ 2) (h0 : β ≠ 0) (h1 : β ≠ 1)
    (h2 : 2 * β - 1 ≠ 0) {d : Type*} [Fintype d] [DecidableEq d] {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hρt : ρ.trace = 1) (hσt : σ.trace = 1)
    (hmix : IsMajorizedBy (hρ.1.eigenvalues ∘ (Fintype.equivFin d).symm)
      (hσ.1.eigenvalues ∘ (Fintype.equivFin d).symm))
    (hne : ∀ τ : Equiv.Perm d, hρ.1.eigenvalues ∘ τ ≠ hσ.1.eigenvalues) :
    scalarCurvature (wydMetric β (tracelessHermitian d) σ) 0 <
      scalarCurvature (wydMetric β (tracelessHermitian d) ρ) 0 :=
  wyd_curvature_lt hm hM h0 h1 h2 (wyd_64 hm hM h0 h1 h2) (wyd_65 hm hM h0 h1 h2) hρ hσ hρt hσt
    hmix hne

end WYD

#print axioms WYD.wyd_curvature_lt_of_isMajorizedBy
