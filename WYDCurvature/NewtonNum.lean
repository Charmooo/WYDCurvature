/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.NewtonEP
import WYDCurvature.Translate

/-!
# (64) and (65) from Newton checks

The lists `num64` and `num65` represent the numerators of (64) and (65) for `H = hypH d`
(`hypH_eq_div`, `sem_num65`, `sem_num64`), so successful Newton checks for the three positions of the
distinguished variable give `HypCond64 d` and `HypCond65 d` (`hypCond64_of_checks`,
`hypCond65_of_checks`).
-/

open Real Filter
open scoped Topology
open WYD63 (qubitK)

namespace WYD.Newton

section

variable {t d p q : ℝ} {P : Par}

/-- `2(p sinh(dx) - q sinh x)`. -/
noncomputable def F2 (p q d x : ℝ) : ℝ := p * exp (d * x) - p * exp (-(d * x)) - q * exp x + q * exp (-x)

/-- `2q(cosh(dx) - cosh x)`. -/
noncomputable def G2 (q d x : ℝ) : ℝ := q * (exp (d * x) + exp (-(d * x)) - exp x - exp (-x))

theorem F2_neg (x : ℝ) : F2 p q d (-x) = -F2 p q d x := by
  simp only [F2, mul_neg, neg_neg]; ring

theorem G2_neg (x : ℝ) : G2 q d (-x) = G2 q d x := by
  simp only [G2, mul_neg, neg_neg]; ring

theorem F2_eq (x : ℝ) : F2 p q d x = 2 * (p * sinh (d * x) - q * sinh x) := by
  rw [F2, sinh_eq, sinh_eq]; ring

theorem G2_eq (x : ℝ) : G2 q d x = 2 * q * (cosh (d * x) - cosh x) := by
  rw [G2, cosh_eq, cosh_eq]; ring

/-- `σ_i - σ_j` in the gaps. -/
def gap (i j : ℕ) (u v : ℝ) : ℝ :=
  ((pos j).1 - (pos i).1 : ℤ) * u + ((pos j).2 - (pos i).2 : ℤ) * v

theorem eT_ev (i j : ℕ) (x y : ℤ) (c : PP) (u v : ℝ) :
    (eT i j x y c).ev d u v = exp ((x + y * d) * gap i j u v) := by
  simp only [Term.ev, eT, Term.mk', gap]
  congr 1
  push_cast
  ring

theorem Sem.single {x : Term} {c : ℝ} (hx : Rep t x.c c) : Sem t d [x] fun u v ↦ c * x.ev d u v :=
  (Sem.cons hx Sem.nil).congr fun _ _ ↦ add_zero _

theorem rep_neg1 {a : PP} {x : ℝ} (h : Rep t a x) : Rep t (neg1 a) (-x) :=
  (h.smul (-1)).congr (by push_cast; ring)

theorem sem_sort4 {x₁ x₂ x₃ x₄ : Term} {c₁ c₂ c₃ c₄ : ℝ} (h₁ : Rep t x₁.c c₁) (h₂ : Rep t x₂.c c₂)
    (h₃ : Rep t x₃.c c₃) (h₄ : Rep t x₄.c c₄) : Sem t d (sortT [x₁, x₂, x₃, x₄]) fun u v ↦
      c₁ * x₁.ev d u v + (c₂ * x₂.ev d u v + (c₃ * x₃.ev d u v + c₄ * x₄.ev d u v)) :=
  (SemL.mergeAll 5 (SemL.cons (Sem.single h₁) (SemL.cons (Sem.single h₂) (SemL.cons (Sem.single h₃)
    (SemL.cons (Sem.single h₄) SemL.nil))))).congr fun u v ↦ by ring

theorem sem_epF (hP : ParRep t P p q) (i j : ℕ) :
    Sem t d (epF P i j) fun u v ↦ F2 p q d (gap i j u v) :=
  (sem_sort4 (x₁ := eT i j 0 1 P.p) (x₂ := eT i j 0 (-1) (neg1 P.p)) (x₃ := eT i j 1 0 (neg1 P.q))
    (x₄ := eT i j (-1) 0 P.q) hP.hp (rep_neg1 hP.hp) (rep_neg1 hP.hq) hP.hq).congr fun u v ↦ by
    simp only [eT_ev, F2]
    push_cast
    simp only [zero_add, one_mul, zero_mul, add_zero, neg_mul]
    ring

theorem sem_epG (hP : ParRep t P p q) (i j : ℕ) :
    Sem t d (epG P i j) fun u v ↦ G2 q d (gap i j u v) :=
  (sem_sort4 (x₁ := eT i j 0 1 P.q) (x₂ := eT i j 0 (-1) P.q) (x₃ := eT i j 1 0 (neg1 P.q))
    (x₄ := eT i j (-1) 0 (neg1 P.q)) hP.hq hP.hq (rep_neg1 hP.hq) (rep_neg1 hP.hq)).congr
    fun u v ↦ by
    simp only [eT_ev, G2]
    push_cast
    simp only [zero_add, one_mul, zero_mul, add_zero, neg_mul]
    ring

theorem sem_epW (k : ℤ) (i : ℕ) : Sem t d (epW k i) fun u v ↦ exp (-k * gap i 2 u v) :=
  (Sem.single (x := eT i 2 (-k) 0 (1, 1)) (rep_one t)).congr fun u v ↦ by
    simp only [eT_ev, one_mul]
    push_cast
    simp only [zero_mul, add_zero]

theorem rep_m1 (t : ℝ) : Rep t (-1, 1) (-1) := by simpa using rep_int t (-1)

/-- The function of `epK`. -/
noncomputable def fK (p q d : ℝ) (i j : ℕ) (u v : ℝ) : ℝ :=
  F2 p q d (gap i j u v) + -1 * G2 q d (gap i j u v)

theorem sem_epK (hP : ParRep t P p q) (i j : ℕ) : Sem t d (epK P i j) (fK p q d i j) :=
  (sem_epF hP i j).add ((sem_epG hP i j).smul (rep_m1 t))

/-- The function of `epN`. -/
noncomputable def fN (p q d u v : ℝ) : ℝ :=
  exp (-(1 : ℤ) * gap 2 2 u v) * F2 p q d (gap 0 1 u v) +
    (exp (-(1 : ℤ) * gap 0 2 u v) * F2 p q d (gap 1 2 u v) +
      exp (-(1 : ℤ) * gap 1 2 u v) * F2 p q d (gap 2 0 u v))

theorem sem_epN (hP : ParRep t P p q) : Sem t d (epN P) (fN p q d) :=
  ((sem_epW 1 2).mul (sem_epF hP 0 1)).add (((sem_epW 1 0).mul (sem_epF hP 1 2)).add
    ((sem_epW 1 1).mul (sem_epF hP 2 0)))

/-- The function of `epV`. -/
noncomputable def fV (p q d : ℝ) (i j k : ℕ) (u v : ℝ) : ℝ :=
  exp (-(2 : ℤ) * gap i 2 u v) * G2 q d (gap j k u v) * (fK p q d j i u v * fK p q d k i u v)

theorem sem_epV (hP : ParRep t P p q) (i j k : ℕ) : Sem t d (epV P i j k) (fV p q d i j k) :=
  ((sem_epW 2 i).mul (sem_epG hP j k)).mul ((sem_epK hP j i).mul (sem_epK hP k i))

/-- The function of `epA`. -/
noncomputable def fA (p q d u v : ℝ) : ℝ :=
  (((3 : ℤ) * q) * (q * q + -(p * p))) * (fN p q d u v * fN p q d u v) +
    ((-2 : ℤ) * (p * p)) * (fV p q d 0 1 2 u v + (fV p q d 1 2 0 u v + fV p q d 2 0 1 u v))

theorem sem_epA (hP : ParRep t P p q) (ht : 0 ≤ t) : Sem t d (epA P) (fA p q d) :=
  ((((sem_epN hP).mul (sem_epN hP)).smul ((hP.hq.smul 3).mul ((hP.hq.mul hP.hq).add
    (rep_neg1 (hP.hp.mul hP.hp))))).add (((sem_epV hP 0 1 2).add ((sem_epV hP 1 2 0).add
    (sem_epV hP 2 0 1))).smul ((hP.hp.mul hP.hp).smul (-2)))).clean ht

/-- The numerator of (65). -/
def N65 (p A A1 A2 Q Q1 Q2 : ℝ) : ℝ :=
  ((A2 + -(2 * p) * A1) * Q + (A1 * (-2 * Q1) + A * (2 * p * Q1 + -1 * Q2))) * Q +
    A * (2 * (Q1 * Q1))

theorem sem_num65 (hP : ParRep t P p q) (ht : 0 ≤ t) (hp : p ≠ 0) (hd : q = p * d) {k : ℕ}
    (hk : k ≤ 2) (i j : ℕ) {s : ℤ} (hs : s.natAbs = 1) :
    ∃ A1 A2 Q1 Q2 : ℝ → ℝ → ℝ,
      (∀ (s₀ s₁ s₂ : ℝ → ℝ) (y : ℝ), HasDerivAt s₀ (dlt 0 k) y → HasDerivAt s₁ (dlt 1 k) y →
        HasDerivAt s₂ (dlt 2 k) y →
        HasDerivAt (fun s ↦ posFun (-2) (fA p q d) (s₀ s) (s₁ s) (s₂ s))
          (posFun (-2) A1 (s₀ y) (s₁ y) (s₂ y) / p) y ∧
        HasDerivAt (fun s ↦ posFun (-2) A1 (s₀ s) (s₁ s) (s₂ s))
          (posFun (-2) A2 (s₀ y) (s₁ y) (s₂ y) / p) y ∧
        HasDerivAt (fun s ↦ posFun 0 (fun u v ↦ G2 q d (gap k i u v) * G2 q d (gap k j u v))
          (s₀ s) (s₁ s) (s₂ s)) (posFun 0 Q1 (s₀ y) (s₁ y) (s₂ y) / p) y ∧
        HasDerivAt (fun s ↦ posFun 0 Q1 (s₀ s) (s₁ s) (s₂ s))
          (posFun 0 Q2 (s₀ y) (s₁ y) (s₂ y) / p) y) ∧
      Sem t d (num65 P s k i j) fun u v ↦ s * N65 p (fA p q d u v) (A1 u v) (A2 u v)
        (G2 q d (gap k i u v) * G2 q d (gap k j u v)) (Q1 u v) (Q2 u v) := by
  have hA := sem_epA (d := d) hP ht
  have hQ := (sem_epG (d := d) hP k i).mul (sem_epG hP k j)
  obtain ⟨A1, hA1, eA1⟩ := hA.der hP hp hd hk (-2)
  obtain ⟨A2, hA2, eA2⟩ := hA1.der hP hp hd hk (-2)
  obtain ⟨Q1, hQ1, eQ1⟩ := hQ.der hP hp hd hk 0
  obtain ⟨Q2, hQ2, eQ2⟩ := hQ1.der hP hp hd hk 0
  refine ⟨A1, A2, Q1, Q2, fun s₀ s₁ s₂ y e0 e1 e2 ↦ ⟨eA1 s₀ s₁ s₂ y e0 e1 e2,
    eA2 s₀ s₁ s₂ y e0 e1 e2, eQ1 s₀ s₁ s₂ y e0 e1 e2, eQ2 s₀ s₁ s₂ y e0 e1 e2⟩, ?_⟩
  have hs' : Rep t (s, 1) s := by simpa [hs] using rep_int t s
  have r2 : Rep t (2, 2) 2 := by simpa using rep_int t 2
  have rm2 : Rep t (-2, 2) (-2) := by simpa using rep_int t (-2)
  have tp : Rep t (PP.smul 2 P.p) (2 * p) := by simpa using hP.hp.smul 2
  have hB := ((hA2.add (hA1.smul (rep_neg1 tp))).mul hQ).add
    ((hA1.mul (hQ1.smul rm2)).add (hA.mul ((hQ1.smul tp).add (hQ2.smul (rep_m1 t)))))
  exact ((hB.mul hQ).add (hA.mul ((hQ1.mul hQ1).smul r2))).smul hs' |>.clean ht

/-- The denominator of `H`, up to a constant. -/
noncomputable def fD (q d u v : ℝ) : ℝ :=
  G2 q d (gap 0 1 u v) * G2 q d (gap 1 2 u v) * G2 q d (gap 0 2 u v)

theorem sem_num64 (hP : ParRep t P p q) (ht : 0 ≤ t) (hp : p ≠ 0) (hd : q = p * d) {i j : ℕ}
    (hi : i ≤ 2) (hj : j ≤ 2) : ∃ A1 D1 B1 E1 : ℝ → ℝ → ℝ,
      (∀ (s₀ s₁ s₂ : ℝ → ℝ) (y : ℝ), HasDerivAt s₀ (dlt 0 i) y → HasDerivAt s₁ (dlt 1 i) y →
        HasDerivAt s₂ (dlt 2 i) y →
        HasDerivAt (fun s ↦ posFun (-2) (fA p q d) (s₀ s) (s₁ s) (s₂ s))
          (posFun (-2) A1 (s₀ y) (s₁ y) (s₂ y) / p) y ∧
        HasDerivAt (fun s ↦ posFun 0 (fD q d) (s₀ s) (s₁ s) (s₂ s))
          (posFun 0 D1 (s₀ y) (s₁ y) (s₂ y) / p) y) ∧
      (∀ (s₀ s₁ s₂ : ℝ → ℝ) (y : ℝ), HasDerivAt s₀ (dlt 0 j) y → HasDerivAt s₁ (dlt 1 j) y →
        HasDerivAt s₂ (dlt 2 j) y →
        HasDerivAt (fun s ↦ posFun (-2) (fA p q d) (s₀ s) (s₁ s) (s₂ s))
          (posFun (-2) B1 (s₀ y) (s₁ y) (s₂ y) / p) y ∧
        HasDerivAt (fun s ↦ posFun 0 (fD q d) (s₀ s) (s₁ s) (s₂ s))
          (posFun 0 E1 (s₀ y) (s₁ y) (s₂ y) / p) y) ∧
      Sem t d (num64 P i j) fun u v ↦
        exp (-(2 : ℤ) * gap i 2 u v) * (A1 u v * fD q d u v + -1 * (fA p q d u v * D1 u v)) +
          -1 * (exp (-(2 : ℤ) * gap j 2 u v) *
            (B1 u v * fD q d u v + -1 * (fA p q d u v * E1 u v))) := by
  have hA := sem_epA (d := d) hP ht
  have hD : Sem t d (EP.mul (EP.mul (epG P 0 1) (epG P 1 2)) (epG P 0 2)) (fD q d) :=
    ((sem_epG (d := d) hP 0 1).mul (sem_epG hP 1 2)).mul (sem_epG hP 0 2)
  obtain ⟨A1, hA1, eA1⟩ := hA.der hP hp hd hi (-2)
  obtain ⟨D1, hD1, eD1⟩ := hD.der hP hp hd hi 0
  obtain ⟨B1, hB1, eB1⟩ := hA.der hP hp hd hj (-2)
  obtain ⟨E1, hE1, eE1⟩ := hD.der hP hp hd hj 0
  refine ⟨A1, D1, B1, E1, fun s₀ s₁ s₂ y e0 e1 e2 ↦ ⟨eA1 s₀ s₁ s₂ y e0 e1 e2,
    eD1 s₀ s₁ s₂ y e0 e1 e2⟩, fun s₀ s₁ s₂ y e0 e1 e2 ↦ ⟨eB1 s₀ s₁ s₂ y e0 e1 e2,
    eE1 s₀ s₁ s₂ y e0 e1 e2⟩, ?_⟩
  have L := fun {k : ℕ} {a b : EP} {f g : ℝ → ℝ → ℝ} (ha : Sem t d a f) (hb : Sem t d b g) ↦
    (sem_epW (t := t) (d := d) 2 k).mul
      ((ha.mul hD).add ((hA.mul hb).smul (rep_m1 t)))
  exact ((L (k := i) hA1 hD1).add ((L (k := j) hB1 hE1).smul (rep_m1 t))).clean ht

/-! ### The numerator and `H` -/

theorem posFun_mul (w w' : ℤ) (f g : ℝ → ℝ → ℝ) (s₀ s₁ s₂ : ℝ) :
    posFun w f s₀ s₁ s₂ * posFun w' g s₀ s₁ s₂ =
      posFun (w + w') (fun u v ↦ f u v * g u v) s₀ s₁ s₂ := by
  simp only [posFun]
  push_cast
  rw [add_mul, exp_add]; ring

theorem gap_eval (s₀ s₁ s₂ : ℝ) : gap 0 1 (s₁ - s₀) (s₂ - s₁) = s₀ - s₁ ∧
    gap 1 2 (s₁ - s₀) (s₂ - s₁) = s₁ - s₂ ∧ gap 0 2 (s₁ - s₀) (s₂ - s₁) = s₀ - s₂ ∧
    gap 1 0 (s₁ - s₀) (s₂ - s₁) = -(s₀ - s₁) ∧ gap 2 1 (s₁ - s₀) (s₂ - s₁) = -(s₁ - s₂) ∧
    gap 2 0 (s₁ - s₀) (s₂ - s₁) = -(s₀ - s₂) ∧ gap 2 2 (s₁ - s₀) (s₂ - s₁) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [gap, pos]

theorem hypPhi_eq_F2 (_ : p ≠ 0) (hd0 : d ≠ 0) (hd : q = p * d) (x : ℝ) :
    hypPhi d x = -F2 p q d x / (2 * q * (1 - d ^ 2)) := by
  rw [hypPhi, F2_eq, hd]
  by_cases h : 1 - d ^ 2 = 0
  · simp [h]
  · field_simp; ring

theorem hypPhi'_eq_G2 (hq : q ≠ 0) (x : ℝ) :
    hypPhi' d x = -G2 q d x / (2 * q * (1 - d ^ 2)) := by
  rw [hypPhi', G2_eq]
  by_cases h : 1 - d ^ 2 = 0
  · simp [h]
  · field_simp; ring

theorem qubitK_eq_F2 (hp : p ≠ 0) (hd0 : d ≠ 0) (hd : q = p * d) {x : ℝ} (hG : G2 q d x ≠ 0) :
    qubitK d x = F2 p q d x / G2 q d x := by
  have h : cosh x - cosh (d * x) ≠ 0 := fun h ↦ hG (by rw [G2_eq, ← neg_sub, h]; simp)
  rw [qubitK, div_eq_div_iff (mul_ne_zero hd0 h) hG, F2_eq, G2_eq, hd]
  ring

/-- `H` through `posFun (-2) (fA p q d)`. -/
theorem hypH_eq_div (hp : p ≠ 0) (hd0 : d ≠ 0) (hd1 : d ^ 2 ≠ 1) (hd : q = p * d) {s₀ s₁ s₂ : ℝ}
    (h01 : G2 q d (s₀ - s₁) ≠ 0) (h12 : G2 q d (s₁ - s₂) ≠ 0) (h02 : G2 q d (s₀ - s₂) ≠ 0) :
    hypH d s₀ s₁ s₂ = posFun (-2) (fA p q d) s₀ s₁ s₂ /
      (24 * p ^ 2 * (G2 q d (s₀ - s₁) * G2 q d (s₁ - s₂) * G2 q d (s₀ - s₂))) := by
  have hq : q ≠ 0 := by rw [hd]; exact mul_ne_zero hp hd0
  have hne : 1 - d ^ 2 ≠ 0 := sub_ne_zero.2 hd1.symm
  obtain ⟨g01, g12, g02, g10, g21, g20, g22⟩ := gap_eval s₀ s₁ s₂
  have n10 : s₁ - s₀ = -(s₀ - s₁) := by ring
  have n21 : s₂ - s₁ = -(s₁ - s₂) := by ring
  have n20 : s₂ - s₀ = -(s₀ - s₂) := by ring
  have k : ∀ x, G2 q d x ≠ 0 → qubitK d (-x) = -F2 p q d x / G2 q d x := fun x hx ↦ by
    rw [qubitK_eq_F2 hp hd0 hd (by rwa [G2_neg]), F2_neg, G2_neg]
  have e0 : exp (-(1 : ℤ) * (s₀ - s₂)) = exp (-s₀) / exp (-s₂) := by
    rw [← exp_sub]; congr 1; push_cast; ring
  have e1 : exp (-(1 : ℤ) * (s₁ - s₂)) = exp (-s₁) / exp (-s₂) := by
    rw [← exp_sub]; congr 1; push_cast; ring
  have e0' : exp (-(2 : ℤ) * (s₀ - s₂)) = exp (-s₀) ^ 2 / exp (-s₂) ^ 2 := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_sub]; congr 1; push_cast; ring
  have e1' : exp (-(2 : ℤ) * (s₁ - s₂)) = exp (-s₁) ^ 2 / exp (-s₂) ^ 2 := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_sub]; congr 1; push_cast; ring
  have sq : ∀ x : ℝ, exp (-2 * x) = exp (-x) ^ 2 := fun x ↦ by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have sq2 : exp (((-2 : ℤ) : ℝ) * s₂) = exp (-s₂) ^ 2 := by rw [← sq]; congr 1
  rw [hypH, posFun, fA, fN, fV, fV, fV]
  simp only [fK, g01, g12, g02, g10, g21, g20, g22]
  simp only [F2_neg, G2_neg, e0, e1, e0', e1', sq, sq2, mul_zero, exp_zero]
  simp only [n10, n21, n20, k _ h01, k _ h12, k _ h02, qubitK_eq_F2 hp hd0 hd h01,
    qubitK_eq_F2 hp hd0 hd h12, qubitK_eq_F2 hp hd0 hd h02, hypPhi_eq_F2 hp hd0 hd,
    hypPhi'_eq_G2 hq, F2_neg, G2_neg]
  have E2 := (exp_pos (-s₂)).ne'
  generalize exp (-s₀) = X0
  generalize exp (-s₁) = X1
  generalize exp (-s₂) = X2 at *
  generalize F2 p q d (s₀ - s₁) = f01
  generalize F2 p q d (s₁ - s₂) = f12
  generalize F2 p q d (s₀ - s₂) = f02
  generalize G2 q d (s₀ - s₁) = y01 at *
  generalize G2 q d (s₁ - s₂) = y12 at *
  generalize G2 q d (s₀ - s₂) = y02 at *
  subst hd
  push_cast
  field_simp
  ring

/-! ### The conditions from the checks -/

theorem hypH_swap₁₂ (a b c : ℝ) : hypH d a b c = hypH d b a c := by
  have o : ∀ x y, hypPhi d (x - y) = -hypPhi d (y - x) := fun x y ↦ by
    rw [← neg_sub, hypPhi, hypPhi, mul_neg, sinh_neg, sinh_neg]; ring
  have e : ∀ x y, hypPhi' d (x - y) = hypPhi' d (y - x) := fun x y ↦ by
    rw [← neg_sub, hypPhi', hypPhi', mul_neg, cosh_neg, cosh_neg]
  rw [hypH, hypH, o a b, o b c, o c a, e a b, e b c, e c a]
  ring

theorem hypH_swap₂₃ (a b c : ℝ) : hypH d a b c = hypH d a c b := by
  have o : ∀ x y, hypPhi d (x - y) = -hypPhi d (y - x) := fun x y ↦ by
    rw [← neg_sub, hypPhi, hypPhi, mul_neg, sinh_neg, sinh_neg]; ring
  have e : ∀ x y, hypPhi' d (x - y) = hypPhi' d (y - x) := fun x y ↦ by
    rw [← neg_sub, hypPhi', hypPhi', mul_neg, cosh_neg, cosh_neg]
  rw [hypH, hypH, o a b, o b c, o c a, e a b, e b c, e c a]
  ring

/-- The first derivative of a quotient. -/
theorem hasDerivAt_quot {A A1 D D1 h : ℝ → ℝ} {C a : ℝ} (hA : HasDerivAt A (A1 a / p) a)
    (hD : HasDerivAt D (D1 a / p) a) (hD0 : D a ≠ 0) (hC : C ≠ 0) (hp : p ≠ 0)
    (hh : h =ᶠ[𝓝 a] fun s ↦ A s / (C * D s)) :
    HasDerivAt h ((A1 a * D a - A a * D1 a) / (p * C * D a ^ 2)) a := by
  have e := hA.div (hD.const_mul C) (mul_ne_zero hC hD0)
  refine (e.congr_of_eventuallyEq hh).congr_deriv ?_
  field_simp

/-- The expression of (65) for a quotient. -/
theorem deriv2_quot {A A1 A2 Q Q1 Q2 h : ℝ → ℝ} {C a : ℝ} (hA : ∀ s, HasDerivAt A (A1 s / p) s)
    (hA1 : ∀ s, HasDerivAt A1 (A2 s / p) s) (hQ : ∀ s, HasDerivAt Q (Q1 s / p) s)
    (hQ1 : ∀ s, HasDerivAt Q1 (Q2 s / p) s) (hQ0 : Q a ≠ 0) (hC : C ≠ 0) (hp : p ≠ 0)
    (hh : ∀ᶠ s in 𝓝 a, h s = A s / (C * Q s)) :
    deriv (deriv h) a - 2 * deriv h a =
      N65 p (A a) (A1 a) (A2 a) (Q a) (Q1 a) (Q2 a) / (p ^ 2 * C * Q a ^ 3) := by
  have hQe : ∀ᶠ s in 𝓝 a, Q s ≠ 0 := (hQ a).continuousAt.eventually_ne hQ0
  have h1 : ∀ᶠ s in 𝓝 a, deriv h s = (A1 s * Q s - A s * Q1 s) / (p * C * Q s ^ 2) := by
    filter_upwards [hh.eventually_nhds, hQe] with s hs hQs
    exact (hasDerivAt_quot (hA s) (hQ s) hQs hC hp hs).deriv
  have h2 : HasDerivAt (fun s ↦ (A1 s * Q s - A s * Q1 s) / (p * C * Q s ^ 2)) _ a :=
    (((hA1 a).mul (hQ a)).sub ((hA a).mul (hQ1 a))).div (((hQ a).pow 2).const_mul (p * C))
      (mul_ne_zero (mul_ne_zero hp hC) (pow_ne_zero 2 hQ0))
  rw [(EventuallyEq.deriv_eq h1 : deriv (deriv h) a = _), h2.deriv, h1.self_of_nhds, N65]
  simp only [Pi.mul_apply, Pi.sub_apply]
  push_cast
  field_simp
  ring

/-- The checks for one value of the parameters: `s` is the sign of `p - q`. -/
structure Checks (P : Par) (s : ℤ) : Prop where
  c0 : ∃ us vs, check2 P us vs (group (num65 P s 0 1 2)) = true
  c1 : ∃ us vs, check2 P us vs (group (num65 P s 1 0 2)) = true
  c2 : ∃ us vs, check2 P us vs (group (num65 P s 2 0 1)) = true
  e0 : ∃ us vs, check2 P us vs (group (num64 P 1 2)) = true
  e1 : ∃ us vs, check2 P us vs (group (num64 P 0 2)) = true
  e2 : ∃ us vs, check2 P us vs (group (num64 P 0 1)) = true

theorem hasDerivAt_dlt {s : ℝ → ℝ} {i k : ℕ} (y : ℝ) (h1 : i = k → s = fun x ↦ x)
    (h2 : i ≠ k → ∃ c, s = fun _ ↦ c) : HasDerivAt s (dlt i k) y := by
  by_cases h : i = k
  · rw [dlt, ite_eq_left h, h1 h]; exact hasDerivAt_id' y
  · obtain ⟨c, hc⟩ := h2 h
    rw [dlt, ite_eq_right h, hc]; exact hasDerivAt_const y c

/-- (65) with the `k`-th of the three ordered positions moving. -/
theorem cond65_aux (hP : ParRep t P p q) (ht : 0 ≤ t) (hp : 0 < p) (hd : q = p * d) (hd0 : d ≠ 0)
    (hd1 : d ^ 2 ≠ 1) {s : ℤ} (hs : s.natAbs = 1) (hG : ∀ x : ℝ, x ≠ 0 → 0 < -(s * G2 q d x))
    {k i j : ℕ} (hk : k ≤ 2) (hc : ∃ us vs, check2 P us vs (group (num65 P s k i j)) = true)
    {s₀ s₁ s₂ : ℝ → ℝ} (h0 : ∀ y, HasDerivAt s₀ (dlt 0 k) y) (h1 : ∀ y, HasDerivAt s₁ (dlt 1 k) y)
    (h2 : ∀ y, HasDerivAt s₂ (dlt 2 k) y) {a : ℝ} (h01 : s₀ a < s₁ a) (h12 : s₁ a < s₂ a) {gc : ℝ}
    (hgc : gc ≠ 0) (hperm : ∀ x, gap k i (s₁ x - s₀ x) (s₂ x - s₁ x) ≠ 0 →
      gap k j (s₁ x - s₀ x) (s₂ x - s₁ x) ≠ 0 →
      G2 q d (s₀ x - s₁ x) * G2 q d (s₁ x - s₂ x) * G2 q d (s₀ x - s₂ x) =
        G2 q d gc * (G2 q d (gap k i (s₁ x - s₀ x) (s₂ x - s₁ x)) *
          G2 q d (gap k j (s₁ x - s₀ x) (s₂ x - s₁ x))))
    (hne : gap k i (s₁ a - s₀ a) (s₂ a - s₁ a) ≠ 0 ∧ gap k j (s₁ a - s₀ a) (s₂ a - s₁ a) ≠ 0) :
    deriv (deriv fun x ↦ hypH d (s₀ x) (s₁ x) (s₂ x)) a -
      2 * deriv (fun x ↦ hypH d (s₀ x) (s₁ x) (s₂ x)) a ≤ 0 := by
  obtain ⟨A1, A2, Q1, Q2, hder, hsem⟩ := sem_num65 hP ht hp.ne' hd hk i j hs
  obtain ⟨us, vs, hc⟩ := hc
  have hnn := hsem.nonneg_of_check hP ht hp hd hc (u := s₁ a - s₀ a) (v := s₂ a - s₁ a)
    (by linarith) (by linarith)
  have hG0 : ∀ x : ℝ, x ≠ 0 → G2 q d x ≠ 0 := fun x hx h ↦ by
    have := hG x hx; rw [h] at this; simp at this
  set Q : ℝ → ℝ → ℝ := fun u v ↦ G2 q d (gap k i u v) * G2 q d (gap k j u v) with hQ
  have hQv : ∀ x, posFun 0 Q (s₀ x) (s₁ x) (s₂ x) = G2 q d (gap k i (s₁ x - s₀ x) (s₂ x - s₁ x)) *
      G2 q d (gap k j (s₁ x - s₀ x) (s₂ x - s₁ x)) := fun x ↦ by simp [posFun, hQ]
  have hQa : posFun 0 Q (s₀ a) (s₁ a) (s₂ a) ≠ 0 := by
    rw [hQv]; exact mul_ne_zero (hG0 _ hne.1) (hG0 _ hne.2)
  have hQpos : 0 < posFun 0 Q (s₀ a) (s₁ a) (s₂ a) := by
    have e := mul_pos (hG _ hne.1) (hG _ hne.2)
    have hss : (s : ℝ) * s = 1 := by
      rcases Int.natAbs_eq s with h | h <;> rw [hs] at h <;> rw [h] <;> norm_num
    have e2 : ∀ x y : ℝ, -(s * x) * -(s * y) = ((s : ℝ) * s) * (x * y) := fun x y ↦ by ring
    rwa [e2, hss, one_mul, ← hQv] at e
  have c0 := (h0 a).continuousAt
  have c1 := (h1 a).continuousAt
  have c2 := (h2 a).continuousAt
  have ev01 : ∀ᶠ x in 𝓝 a, s₀ x < s₁ x := c0.eventually_lt c1 h01
  have ev12 : ∀ᶠ x in 𝓝 a, s₁ x < s₂ x := c1.eventually_lt c2 h12
  have evQ : ∀ᶠ x in 𝓝 a, posFun 0 Q (s₀ x) (s₁ x) (s₂ x) ≠ 0 :=
    (hder s₀ s₁ s₂ a (h0 a) (h1 a) (h2 a)).2.2.1.continuousAt.eventually_ne hQa
  have hh : ∀ᶠ x in 𝓝 a, hypH d (s₀ x) (s₁ x) (s₂ x) =
      posFun (-2) (fA p q d) (s₀ x) (s₁ x) (s₂ x) /
        ((24 * p ^ 2 * G2 q d gc) * posFun 0 Q (s₀ x) (s₁ x) (s₂ x)) := by
    filter_upwards [ev01, ev12, evQ] with x hx hx' hxQ
    rw [hQv] at hxQ ⊢
    have g1 : gap k i (s₁ x - s₀ x) (s₂ x - s₁ x) ≠ 0 := fun h ↦ by
      rw [h] at hxQ; simp [G2] at hxQ
    have g2 : gap k j (s₁ x - s₀ x) (s₂ x - s₁ x) ≠ 0 := fun h ↦ by
      rw [h] at hxQ; simp [G2] at hxQ
    rw [hypH_eq_div hp.ne' hd0 hd1 hd (hG0 _ (by linarith)) (hG0 _ (by linarith))
      (hG0 _ (by linarith)), hperm x g1 g2]
    congr 1
    ring
  have hfin := deriv2_quot (p := p) (a := a) (h := fun x ↦ hypH d (s₀ x) (s₁ x) (s₂ x))
    (A := fun x ↦ posFun (-2) (fA p q d) (s₀ x) (s₁ x) (s₂ x))
    (A1 := fun x ↦ posFun (-2) A1 (s₀ x) (s₁ x) (s₂ x))
    (A2 := fun x ↦ posFun (-2) A2 (s₀ x) (s₁ x) (s₂ x))
    (Q := fun x ↦ posFun 0 Q (s₀ x) (s₁ x) (s₂ x))
    (Q1 := fun x ↦ posFun 0 Q1 (s₀ x) (s₁ x) (s₂ x))
    (Q2 := fun x ↦ posFun 0 Q2 (s₀ x) (s₁ x) (s₂ x)) (C := 24 * p ^ 2 * G2 q d gc)
    (fun y ↦ (hder s₀ s₁ s₂ y (h0 y) (h1 y) (h2 y)).1)
    (fun y ↦ (hder s₀ s₁ s₂ y (h0 y) (h1 y) (h2 y)).2.1)
    (fun y ↦ (hder s₀ s₁ s₂ y (h0 y) (h1 y) (h2 y)).2.2.1)
    (fun y ↦ (hder s₀ s₁ s₂ y (h0 y) (h1 y) (h2 y)).2.2.2) hQa
    (mul_ne_zero (by positivity) (hG0 _ hgc)) hp.ne' hh
  rw [hfin]
  have hN : N65 p (posFun (-2) (fA p q d) (s₀ a) (s₁ a) (s₂ a)) (posFun (-2) A1 (s₀ a) (s₁ a) (s₂ a))
      (posFun (-2) A2 (s₀ a) (s₁ a) (s₂ a)) (posFun 0 Q (s₀ a) (s₁ a) (s₂ a))
      (posFun 0 Q1 (s₀ a) (s₁ a) (s₂ a)) (posFun 0 Q2 (s₀ a) (s₁ a) (s₂ a)) =
      exp (((-2 : ℤ) : ℝ) * s₂ a) * N65 p (fA p q d (s₁ a - s₀ a) (s₂ a - s₁ a))
        (A1 (s₁ a - s₀ a) (s₂ a - s₁ a)) (A2 (s₁ a - s₀ a) (s₂ a - s₁ a))
        (Q (s₁ a - s₀ a) (s₂ a - s₁ a)) (Q1 (s₁ a - s₀ a) (s₂ a - s₁ a))
        (Q2 (s₁ a - s₀ a) (s₂ a - s₁ a)) := by
    simp only [posFun, N65, Int.cast_zero, zero_mul, exp_zero, one_mul]
    ring
  rw [hN]
  set E := N65 p (fA p q d (s₁ a - s₀ a) (s₂ a - s₁ a))
    (A1 (s₁ a - s₀ a) (s₂ a - s₁ a)) (A2 (s₁ a - s₀ a) (s₂ a - s₁ a))
    (Q (s₁ a - s₀ a) (s₂ a - s₁ a)) (Q1 (s₁ a - s₀ a) (s₂ a - s₁ a))
    (Q2 (s₁ a - s₀ a) (s₂ a - s₁ a)) with hE
  have hnn' : 0 ≤ (s : ℝ) * E := hnn
  have hg := hG gc hgc
  have hX := exp_pos (((-2 : ℤ) : ℝ) * s₂ a)
  have hs0 : s = 1 ∨ s = -1 := by
    rcases Int.natAbs_eq s with h | h <;> rw [hs] at h
    · exact Or.inl h
    · exact Or.inr h
  rcases hs0 with rfl | rfl
  · rw [Int.cast_one, one_mul] at hnn' hg
    refine div_nonpos_of_nonneg_of_nonpos (mul_nonneg hX.le hnn') ?_
    have : 0 ≤ p ^ 2 * (24 * p ^ 2 * -G2 q d gc) * posFun 0 Q (s₀ a) (s₁ a) (s₂ a) ^ 3 := by
      positivity
    linarith
  · rw [Int.cast_neg, Int.cast_one, neg_one_mul] at hnn' hg
    refine div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hX.le (by linarith)) ?_
    have hg' : 0 < G2 q d gc := by linarith
    positivity

theorem hypCond65_of_checks (hP : ParRep t P p q) (ht : 0 ≤ t) (hp : 0 < p) (hd : q = p * d)
    (hd0 : d ≠ 0) (hd1 : d ^ 2 ≠ 1) {s : ℤ} (hs : s.natAbs = 1)
    (hG : ∀ x : ℝ, x ≠ 0 → 0 < -(s * G2 q d x)) (hc : Checks P s) : HypCond65 d := by
  have key : ∀ a b c : ℝ, a ≠ b → b < c → c ≠ a →
      deriv (deriv fun s ↦ hypH d s b c) a - 2 * deriv (fun s ↦ hypH d s b c) a ≤ 0 := by
    intro a b c hab hbc hca
    rcases lt_trichotomy a b with h | h | h
    · refine cond65_aux hP ht hp hd hd0 hd1 hs hG (k := 0) (i := 1) (j := 2) (by omega) hc.c0
        (s₀ := fun x ↦ x) (s₁ := fun _ ↦ b) (s₂ := fun _ ↦ c) (fun y ↦ ?_) (fun y ↦ ?_)
        (fun y ↦ ?_) h hbc (gc := b - c) (by linarith) (fun x _ _ ↦ ?_) ?_
      · exact hasDerivAt_dlt y (fun _ ↦ rfl) (by simp)
      · exact hasDerivAt_dlt y (by simp) (fun _ ↦ ⟨b, rfl⟩)
      · exact hasDerivAt_dlt y (by simp) (fun _ ↦ ⟨c, rfl⟩)
      · obtain ⟨g01, g12, g02, _⟩ := gap_eval x b c
        rw [g01, g02]; ring
      · obtain ⟨g01, g12, g02, _⟩ := gap_eval a b c
        rw [g01, g02]; constructor <;> linarith
    · exact absurd h hab
    · rcases lt_trichotomy a c with h' | h' | h'
      · have e : (fun s ↦ hypH d s b c) = fun s ↦ hypH d b s c := funext fun s ↦ hypH_swap₁₂ _ _ _
        rw [e]
        refine cond65_aux hP ht hp hd hd0 hd1 hs hG (k := 1) (i := 0) (j := 2) (by omega) hc.c1
          (s₀ := fun _ ↦ b) (s₁ := fun x ↦ x) (s₂ := fun _ ↦ c) (fun y ↦ ?_) (fun y ↦ ?_)
          (fun y ↦ ?_) h h' (gc := b - c) (by linarith) (fun x _ _ ↦ ?_) ?_
        · exact hasDerivAt_dlt y (by simp) (fun _ ↦ ⟨b, rfl⟩)
        · exact hasDerivAt_dlt y (fun _ ↦ rfl) (by simp)
        · exact hasDerivAt_dlt y (by simp) (fun _ ↦ ⟨c, rfl⟩)
        · obtain ⟨g01, g12, g02, g10, _⟩ := gap_eval b x c
          rw [g10, g12, G2_neg]; ring
        · obtain ⟨g01, g12, g02, g10, _⟩ := gap_eval b a c
          rw [g10, g12]; constructor <;> linarith
      · exact absurd h'.symm hca
      · have e : (fun s ↦ hypH d s b c) = fun s ↦ hypH d b c s := funext fun s ↦ by
          rw [hypH_swap₁₂, hypH_swap₂₃]
        rw [e]
        refine cond65_aux hP ht hp hd hd0 hd1 hs hG (k := 2) (i := 0) (j := 1) (by omega) hc.c2
          (s₀ := fun _ ↦ b) (s₁ := fun _ ↦ c) (s₂ := fun x ↦ x) (fun y ↦ ?_) (fun y ↦ ?_)
          (fun y ↦ ?_) hbc h' (gc := b - c) (by linarith) (fun x _ _ ↦ ?_) ?_
        · exact hasDerivAt_dlt y (by simp) (fun _ ↦ ⟨b, rfl⟩)
        · exact hasDerivAt_dlt y (by simp) (fun _ ↦ ⟨c, rfl⟩)
        · exact hasDerivAt_dlt y (fun _ ↦ rfl) (by simp)
        · obtain ⟨g01, g12, g02, g10, g21, g20, _⟩ := gap_eval b c x
          rw [g20, g21, G2_neg, G2_neg]; ring
        · obtain ⟨g01, g12, g02, g10, g21, g20, _⟩ := gap_eval b c a
          rw [g20, g21]; constructor <;> linarith
  intro a b c hab hbc hca
  rcases lt_or_gt_of_ne hbc with h | h
  · exact key a b c hab h hca
  · have e : (fun s ↦ hypH d s b c) = fun s ↦ hypH d s c b := funext fun s ↦ hypH_swap₂₃ _ _ _
    rw [e]
    exact key a c b hca.symm h hab.symm

/-- (64) for the positions `i < j` of three ordered positions. -/
theorem cond64_aux (hP : ParRep t P p q) (ht : 0 ≤ t) (hp : 0 < p) (hd : q = p * d) (hd0 : d ≠ 0)
    (hd1 : d ^ 2 ≠ 1) (hG0 : ∀ x : ℝ, x ≠ 0 → G2 q d x ≠ 0) {i j : ℕ} (hi : i ≤ 2) (hj : j ≤ 2)
    (hc : ∃ us vs, check2 P us vs (group (num64 P i j)) = true) {σ₀ σ₁ σ₂ : ℝ} (h01 : σ₀ < σ₁)
    (h12 : σ₁ < σ₂) {s₀ s₁ s₂ r₀ r₁ r₂ : ℝ → ℝ} {a b : ℝ}
    (h0 : HasDerivAt s₀ (dlt 0 i) a) (h1 : HasDerivAt s₁ (dlt 1 i) a)
    (h2 : HasDerivAt s₂ (dlt 2 i) a) (k0 : HasDerivAt r₀ (dlt 0 j) b)
    (k1 : HasDerivAt r₁ (dlt 1 j) b) (k2 : HasDerivAt r₂ (dlt 2 j) b)
    (es : s₀ a = σ₀ ∧ s₁ a = σ₁ ∧ s₂ a = σ₂) (er : r₀ b = σ₀ ∧ r₁ b = σ₁ ∧ r₂ b = σ₂)
    (ha : gap i 2 (σ₁ - σ₀) (σ₂ - σ₁) = a - σ₂) (hb : gap j 2 (σ₁ - σ₀) (σ₂ - σ₁) = b - σ₂) :
    0 ≤ exp (-2 * a) * deriv (fun x ↦ hypH d (s₀ x) (s₁ x) (s₂ x)) a -
      exp (-2 * b) * deriv (fun x ↦ hypH d (r₀ x) (r₁ x) (r₂ x)) b := by
  obtain ⟨A1, D1, B1, E1, hder, hder', hsem⟩ := sem_num64 hP ht hp.ne' hd hi hj
  obtain ⟨us, vs, hc⟩ := hc
  have hnn := hsem.nonneg_of_check hP ht hp hd hc (u := σ₁ - σ₀) (v := σ₂ - σ₁)
    (by linarith) (by linarith)
  have hDv : ∀ x y z : ℝ, posFun 0 (fD q d) x y z = G2 q d (x - y) * G2 q d (y - z) *
      G2 q d (x - z) := fun x y z ↦ by
    obtain ⟨g01, g12, g02, _⟩ := gap_eval x y z
    simp [posFun, fD, g01, g12, g02]
  have hD0 : posFun 0 (fD q d) σ₀ σ₁ σ₂ ≠ 0 := by
    rw [hDv]
    exact mul_ne_zero (mul_ne_zero (hG0 _ (by linarith)) (hG0 _ (by linarith)))
      (hG0 _ (by linarith))
  have gen : ∀ {t₀ t₁ t₂ : ℝ → ℝ} {y : ℝ} {X Y : ℝ → ℝ → ℝ} {m : ℕ},
      HasDerivAt t₀ (dlt 0 m) y → HasDerivAt t₁ (dlt 1 m) y → HasDerivAt t₂ (dlt 2 m) y →
      (t₀ y = σ₀ ∧ t₁ y = σ₁ ∧ t₂ y = σ₂) →
      HasDerivAt (fun s ↦ posFun (-2) (fA p q d) (t₀ s) (t₁ s) (t₂ s))
          (posFun (-2) X (t₀ y) (t₁ y) (t₂ y) / p) y →
      HasDerivAt (fun s ↦ posFun 0 (fD q d) (t₀ s) (t₁ s) (t₂ s))
          (posFun 0 Y (t₀ y) (t₁ y) (t₂ y) / p) y →
      deriv (fun x ↦ hypH d (t₀ x) (t₁ x) (t₂ x)) y =
        exp (((-2 : ℤ) : ℝ) * σ₂) * (X (σ₁ - σ₀) (σ₂ - σ₁) * fD q d (σ₁ - σ₀) (σ₂ - σ₁) +
          -1 * (fA p q d (σ₁ - σ₀) (σ₂ - σ₁) * Y (σ₁ - σ₀) (σ₂ - σ₁))) /
          (p * (24 * p ^ 2) * posFun 0 (fD q d) σ₀ σ₁ σ₂ ^ 2) := by
    intro t₀ t₁ t₂ y X Y m d0 d1 d2 et hX hY
    have ev01 : ∀ᶠ x in 𝓝 y, t₀ x < t₁ x :=
      d0.continuousAt.eventually_lt d1.continuousAt (by rw [et.1, et.2.1]; exact h01)
    have ev12 : ∀ᶠ x in 𝓝 y, t₁ x < t₂ x :=
      d1.continuousAt.eventually_lt d2.continuousAt (by rw [et.2.1, et.2.2]; exact h12)
    have hh : (fun x ↦ hypH d (t₀ x) (t₁ x) (t₂ x)) =ᶠ[𝓝 y] fun x ↦
        posFun (-2) (fA p q d) (t₀ x) (t₁ x) (t₂ x) /
          ((24 * p ^ 2) * posFun 0 (fD q d) (t₀ x) (t₁ x) (t₂ x)) := by
      filter_upwards [ev01, ev12] with x hx hx'
      rw [hDv, hypH_eq_div hp.ne' hd0 hd1 hd (hG0 _ (by linarith)) (hG0 _ (by linarith))
        (hG0 _ (by linarith))]
    have hq := hasDerivAt_quot (p := p) (C := 24 * p ^ 2)
      (A := fun s ↦ posFun (-2) (fA p q d) (t₀ s) (t₁ s) (t₂ s))
      (A1 := fun s ↦ posFun (-2) X (t₀ s) (t₁ s) (t₂ s))
      (D := fun s ↦ posFun 0 (fD q d) (t₀ s) (t₁ s) (t₂ s))
      (D1 := fun s ↦ posFun 0 Y (t₀ s) (t₁ s) (t₂ s)) hX hY
      (by rw [et.1, et.2.1, et.2.2]; exact hD0) (by positivity) hp.ne' hh
    rw [hq.deriv]
    rw [et.1, et.2.1, et.2.2]
    congr 1
    simp only [posFun, Int.cast_zero, zero_mul, exp_zero, one_mul]
    ring
  have e1 := gen h0 h1 h2 es (hder s₀ s₁ s₂ a h0 h1 h2).1 (hder s₀ s₁ s₂ a h0 h1 h2).2
  have e2 := gen k0 k1 k2 er (hder' r₀ r₁ r₂ b k0 k1 k2).1 (hder' r₀ r₁ r₂ b k0 k1 k2).2
  rw [e1, e2]
  rw [ha, hb] at hnn
  have w : ∀ x : ℝ, exp (-2 * x) = exp (((-2 : ℤ) : ℝ) * σ₂) * exp (-(2 : ℤ) * (x - σ₂)) :=
    fun x ↦ by rw [← exp_add]; congr 1; push_cast; ring
  rw [w a, w b]
  set X := exp (((-2 : ℤ) : ℝ) * σ₂)
  have hX : 0 < X := exp_pos _
  have hDsq : 0 < posFun 0 (fD q d) σ₀ σ₁ σ₂ ^ 2 := by positivity
  set Y := posFun 0 (fD q d) σ₀ σ₁ σ₂ ^ 2
  refine (mul_nonneg (a := X * X / (p * (24 * p ^ 2) * Y)) (by positivity) hnn).trans_eq ?_
  ring

theorem hypCond64_of_checks (hP : ParRep t P p q) (ht : 0 ≤ t) (hp : 0 < p) (hd : q = p * d)
    (hd0 : d ≠ 0) (hd1 : d ^ 2 ≠ 1) {s : ℤ} (hG : ∀ x : ℝ, x ≠ 0 → 0 < -(s * G2 q d x))
    (hc : Checks P s) : HypCond64 d := by
  have hG0 : ∀ x : ℝ, x ≠ 0 → G2 q d x ≠ 0 := fun x hx h ↦ by
    have := hG x hx; rw [h] at this; simp at this
  have c : ∀ (i k : ℕ) (x y : ℝ), i ≠ k → HasDerivAt (fun _ : ℝ ↦ x) (dlt i k) y :=
    fun i k x y h ↦ hasDerivAt_dlt y (fun h' ↦ absurd h' h) fun _ ↦ ⟨x, rfl⟩
  have m : ∀ (k : ℕ) (y : ℝ), HasDerivAt (fun x : ℝ ↦ x) (dlt k k) y :=
    fun k y ↦ hasDerivAt_dlt y (fun _ ↦ rfl) fun h ↦ absurd rfl h
  intro a b l hab hla hlb
  rcases lt_trichotomy l a with h | h | h
  · -- `l < a < b`
    have e1 : (fun s ↦ hypH d s b l) = fun s ↦ hypH d l s b := funext fun s ↦ by
      rw [hypH_swap₂₃, hypH_swap₁₂]
    have e2 : (fun s ↦ hypH d a s l) = fun s ↦ hypH d l a s := funext fun s ↦ by
      rw [hypH_swap₂₃, hypH_swap₁₂]
    obtain ⟨g01, g12, g02, g10, g21, g20, g22⟩ := gap_eval l a b
    rw [e1, e2]
    exact cond64_aux hP ht hp hd hd0 hd1 hG0 (i := 1) (j := 2) (by omega) (by omega) hc.e0 h hab
      (s₀ := fun _ ↦ l) (s₁ := fun x ↦ x) (s₂ := fun _ ↦ b) (r₀ := fun _ ↦ l) (r₁ := fun _ ↦ a)
      (r₂ := fun x ↦ x) (c _ _ _ _ (by omega)) (m _ _) (c _ _ _ _ (by omega))
      (c _ _ _ _ (by omega)) (c _ _ _ _ (by omega)) (m _ _) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ g12
      (by rw [g22]; ring)
  · exact absurd h hla
  · rcases lt_trichotomy l b with h' | h' | h'
    · -- `a < l < b`
      have e1 : (fun s ↦ hypH d s b l) = fun s ↦ hypH d s l b := funext fun s ↦ hypH_swap₂₃ _ _ _
      have e2 : (fun s ↦ hypH d a s l) = fun s ↦ hypH d a l s := funext fun s ↦ hypH_swap₂₃ _ _ _
      obtain ⟨g01, g12, g02, g10, g21, g20, g22⟩ := gap_eval a l b
      rw [e1, e2]
      exact cond64_aux hP ht hp hd hd0 hd1 hG0 (i := 0) (j := 2) (by omega) (by omega) hc.e1 h h'
        (s₀ := fun x ↦ x) (s₁ := fun _ ↦ l) (s₂ := fun _ ↦ b) (r₀ := fun _ ↦ a) (r₁ := fun _ ↦ l)
        (r₂ := fun x ↦ x) (m _ _) (c _ _ _ _ (by omega)) (c _ _ _ _ (by omega))
        (c _ _ _ _ (by omega)) (c _ _ _ _ (by omega)) (m _ _) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ g02
        (by rw [g22]; ring)
    · exact absurd h' hlb
    · -- `a < b < l`
      obtain ⟨g01, g12, g02, g10, g21, g20, g22⟩ := gap_eval a b l
      exact cond64_aux hP ht hp hd hd0 hd1 hG0 (i := 0) (j := 1) (by omega) (by omega) hc.e2 hab h'
        (s₀ := fun x ↦ x) (s₁ := fun _ ↦ b) (s₂ := fun _ ↦ l) (r₀ := fun _ ↦ a) (r₁ := fun x ↦ x)
        (r₂ := fun _ ↦ l) (m _ _) (c _ _ _ _ (by omega)) (c _ _ _ _ (by omega))
        (c _ _ _ _ (by omega)) (m _ _) (c _ _ _ _ (by omega)) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ g02
        g12

/-- The sign of `G`. -/
theorem G2_sign {s : ℤ} (hq : 0 < q) (hd : 0 < d) (h : (s = 1 ∧ d < 1) ∨ (s = -1 ∧ 1 < d)) (x : ℝ)
    (hx : x ≠ 0) : 0 < -(s * G2 q d x) := by
  have hx' : 0 < |x| := abs_pos.2 hx
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · have : cosh (d * x) < cosh x := by
      rw [cosh_lt_cosh, abs_mul, abs_of_pos hd]; nlinarith
    rw [G2_eq]; push_cast; nlinarith
  · have : cosh x < cosh (d * x) := by
      rw [cosh_lt_cosh, abs_mul, abs_of_pos hd]; nlinarith
    rw [G2_eq]; push_cast; nlinarith

end

end WYD.Newton
