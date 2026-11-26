/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Newton.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Newton certificates: soundness

* `Rep.nonneg_of`: a packed polynomial that passes the digit test is nonnegative at every `t ≥ 0`.
* `newton_nonneg`: `f(0) ≥ 0` and `f' - n f ≥ 0` on `[0, ∞)` give `f ≥ 0` there.
* `check1_sound`, `check2_sound`: the Newton checks in one and two variables.
-/

open Polynomial

namespace WYD.Newton

/-! ### Packed polynomials -/

theorem half_pos : 0 < half := by rw [half]; positivity

theorem base_cast : (base : ℤ) = 2 * (half : ℤ) := by rw [base]; push_cast; ring

section

attribute [local irreducible] half base

theorem dig_zero (f : ℕ) : PP.dig f 0 = true := by cases f <;> rfl

theorem dig_succ {f x : ℕ} (hx : x ≠ 0) (h : PP.dig (f + 1) x = true) :
    x % base ≤ half ∧ PP.dig f (x / base) = true := by
  rw [PP.dig] at h
  have : x.beq 0 = false := by
    cases hb : x.beq 0 with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb) hx
  rw [this, Bool.cond_false, Bool.and_eq_true] at h
  exact ⟨Nat.le_of_ble_eq_true h.1, h.2⟩

theorem dig_zero_eq {x : ℕ} (h : PP.dig 0 x = true) : x = 0 := Nat.eq_of_beq_eq_true h

theorem eq_zero_of_mul_add {y r h : ℤ} (hr : |r| < h) (e : y * (2 * h) + r = 0) :
    y = 0 ∧ r = 0 := by
  rw [abs_lt] at hr
  have hy : y = 0 := by
    rcases lt_trichotomy y 0 with h1 | h1 | h1
    · have : y * (2 * h) ≤ -1 * (2 * h) := mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
    · exact h1
    · have : 1 * (2 * h) ≤ y * (2 * h) := mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
  subst hy
  exact ⟨rfl, by omega⟩

theorem dig_sound (N : ℕ) : ∀ R : ℤ[X], R.natDegree ≤ N → (∀ i, |R.coeff i| < (half : ℤ)) →
    ∀ f x : ℕ, (x : ℤ) = R.eval (base : ℤ) → PP.dig f x = true → ∀ i, 0 ≤ R.coeff i := by
  have hb := base_cast
  have hh : (0 : ℤ) < (half : ℤ) := by exact_mod_cast half_pos
  induction N with
  | zero =>
    intro R hR _ f x hx _ i
    rw [eq_C_of_natDegree_le_zero hR] at hx ⊢
    rw [eval_C] at hx
    rw [coeff_C]
    split
    · rw [← hx]; positivity
    · exact le_rfl
  | succ N ih =>
    intro R hR hc f x hx hd i
    have hdeg : R.divX.natDegree ≤ N := by rw [natDegree_divX_eq_natDegree_tsub_one]; omega
    have hdc : ∀ i, |R.divX.coeff i| < (half : ℤ) := fun i ↦ by rw [coeff_divX]; exact hc _
    have hev : R.eval (base : ℤ) = R.divX.eval (base : ℤ) * (base : ℤ) + R.coeff 0 := by
      conv_lhs => rw [← divX_mul_X_add R]
      simp
    have h0 := hc 0
    -- the constant coefficient is nonnegative and the quotient is the packed `divX`
    have key : 0 ≤ R.coeff 0 ∧
        ∃ f' x' : ℕ, (x' : ℤ) = R.divX.eval (base : ℤ) ∧ PP.dig f' x' = true := by
      generalize R.divX.eval (base : ℤ) = y at *
      by_cases hx0 : x = 0
      · subst hx0
        have e : y * (base : ℤ) + R.coeff 0 = 0 := by rw [← hev, ← hx]; rfl
        rw [hb] at e
        obtain ⟨e1, e2⟩ := eq_zero_of_mul_add h0 e
        exact ⟨e2.ge, 0, 0, by rw [e1]; rfl, dig_zero 0⟩
      cases f with
      | zero => exact absurd (dig_zero_eq hd) hx0
      | succ f =>
        obtain ⟨hd1, hd2⟩ := dig_succ hx0 hd
        rw [abs_lt] at h0
        have hx' : (x : ℤ) = R.coeff 0 + y * (base : ℤ) := by rw [hx, hev]; ring
        have hmod : ((x % base : ℕ) : ℤ) = (R.coeff 0) % (base : ℤ) := by
          rw [Int.natCast_mod, hx', Int.add_mul_emod_self_right]
        have hd1' : ((x % base : ℕ) : ℤ) ≤ (half : ℤ) := by exact_mod_cast hd1
        have hr : 0 ≤ R.coeff 0 := by
          by_contra hneg
          push Not at hneg
          have e : (R.coeff 0) % (base : ℤ) = R.coeff 0 + (base : ℤ) := by
            rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
          omega
        refine ⟨hr, f, x / base, ?_, hd2⟩
        rw [Int.natCast_div, hx', Int.add_mul_ediv_right _ _ (by omega),
          Int.ediv_eq_zero_of_lt hr (by omega), zero_add]
    obtain ⟨hr, f', x', hx', hd'⟩ := key
    cases i with
    | zero => exact hr
    | succ i =>
      have := ih R.divX hdeg hdc f' x' hx' hd' i
      rwa [coeff_divX] at this

end

/-- `a` represents the value `x` at `t` of a polynomial with integer coefficients. -/
def Rep (t : ℝ) (a : PP) (x : ℝ) : Prop :=
  ∃ P Q : ℕ[X], ((P.eval base : ℕ) : ℤ) - ((Q.eval base : ℕ) : ℤ) = a.1 ∧
    P.eval 1 + Q.eval 1 ≤ a.2 ∧ aeval t P - aeval t Q = x

section Rep

variable {t x y : ℝ} {a b : PP}

theorem Rep.add (ha : Rep t a x) (hb : Rep t b y) : Rep t (a.add b) (x + y) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := ha
  obtain ⟨P', Q', h1', h2', h3'⟩ := hb
  refine ⟨P + P', Q + Q', ?_, ?_, ?_⟩
  · change _ = a.1 + b.1
    simp only [eval_add]; push_cast; linarith
  · change _ ≤ a.2 + b.2
    simp only [eval_add]; omega
  · simp only [map_add]; linarith

theorem Rep.mul (ha : Rep t a x) (hb : Rep t b y) : Rep t (a.mul b) (x * y) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := ha
  obtain ⟨P', Q', h1', h2', h3'⟩ := hb
  refine ⟨P * P' + Q * Q', P * Q' + Q * P', ?_, ?_, ?_⟩
  · change _ = a.1 * b.1
    simp only [eval_add, eval_mul]; push_cast; rw [← h1, ← h1']; ring
  · change _ ≤ a.2 * b.2
    simp only [eval_add, eval_mul]
    calc _ = (eval 1 P + eval 1 Q) * (eval 1 P' + eval 1 Q') := by ring
      _ ≤ _ := Nat.mul_le_mul h2 h2'
  · simp only [map_add, map_mul]; rw [← h3, ← h3']; ring

theorem rep_int (t : ℝ) (n : ℤ) : Rep t (n, n.natAbs) n := by
  refine ⟨C n.toNat, C (-n).toNat, ?_, ?_, ?_⟩
  · simp only [eval_C]; exact Int.toNat_sub_toNat_neg n
  · simp only [eval_C]; omega
  · rw [aeval_C, aeval_C]; change ((n.toNat : ℕ) : ℝ) - (((-n).toNat : ℕ) : ℝ) = n
    have := Int.toNat_sub_toNat_neg n
    have h : (((n.toNat : ℤ) - ((-n).toNat : ℤ) : ℤ) : ℝ) = n := by rw [this]
    rw [← h]; push_cast; rfl

theorem Rep.smul (n : ℤ) (ha : Rep t a x) : Rep t (PP.smul n a) (n * x) := (rep_int t n).mul ha

theorem rep_zero (t : ℝ) : Rep t PP.zero 0 := by simpa [PP.zero] using rep_int t 0

theorem rep_one (t : ℝ) : Rep t (1, 1) 1 := by simpa using rep_int t 1

theorem coeff_le_eval_one (P : ℕ[X]) (i : ℕ) : P.coeff i ≤ P.eval 1 := by
  rw [eval_eq_sum_range]
  by_cases h : i ≤ P.natDegree
  · simp only [one_pow, mul_one]
    exact Finset.single_le_sum (f := fun i ↦ P.coeff i) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact Nat.zero_le _

theorem Rep.congr (ha : Rep t a x) (h : x = y) : Rep t a y := h ▸ ha

/-- A packed polynomial that passes the digit test is nonnegative at every `t ≥ 0`. -/
theorem Rep.nonneg_of (ha : Rep t a x) (ht : 0 ≤ t) (hn : a.nonneg = true) : 0 ≤ x := by
  obtain ⟨P, Q, h1, h2, h3⟩ := ha
  obtain ⟨n, m⟩ := a
  cases n with
  | negSucc n => simp [PP.nonneg] at hn
  | ofNat n =>
    rw [PP.nonneg, Bool.and_eq_true, Nat.ble_eq] at hn
    set R : ℤ[X] := P.map (Nat.castRingHom ℤ) - Q.map (Nat.castRingHom ℤ) with hR
    have hcoef : ∀ i, R.coeff i = (P.coeff i : ℤ) - (Q.coeff i : ℤ) := fun i ↦ by
      simp [hR, coeff_sub, coeff_map]
    have hc : ∀ i, |R.coeff i| < (half : ℤ) := fun i ↦ by
      have e1 := coeff_le_eval_one P i
      have e2 := coeff_le_eval_one Q i
      have e3 : m + 1 ≤ half := hn.1
      have e4 : P.eval 1 + Q.eval 1 ≤ m := h2
      rw [hcoef, abs_lt]
      omega
    have hev : ((n : ℕ) : ℤ) = R.eval (base : ℤ) := by
      have e : ∀ S : ℕ[X], (S.map (Nat.castRingHom ℤ)).eval (base : ℤ) = ((S.eval base : ℕ) : ℤ) :=
        fun S ↦ by
          have := eval_map_apply (f := Nat.castRingHom ℤ) (p := S) base
          rwa [eq_natCast, eq_natCast] at this
      rw [hR, eval_sub, e, e]
      exact h1.symm
    have hnn := dig_sound R.natDegree R le_rfl hc 200 n hev hn.2
    have hx : aeval t R = x := by
      rw [← h3, hR, map_sub]
      have e : ∀ S : ℕ[X], aeval t (S.map (Nat.castRingHom ℤ)) = aeval t S := fun S ↦ by
        rw [aeval_def, aeval_def, eval₂_map]
        congr 1
      rw [e, e]
    rw [← hx, aeval_eq_sum_range]
    exact Finset.sum_nonneg fun i _ ↦ by
      rw [zsmul_eq_mul]
      have := hnn i
      positivity

theorem Rep.eq_zero_of (ha : Rep t a x) (ht : 0 ≤ t) (hz : isZero a = true) : x = 0 := by
  rw [isZero, Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq] at hz
  have e : ∀ b : PP, b.1 = 0 → b.2 + 1 ≤ half → b.nonneg = true := by
    rintro ⟨n, m⟩ h1 h2
    simp only at h1 h2
    subst h1
    change (Nat.ble (m + 1) half && PP.dig 200 0) = true
    rw [dig_zero, Bool.and_true, Nat.ble_eq]
    exact h2
  have h1 := ha.nonneg_of ht (e a hz.1 hz.2)
  have h2 := (ha.smul (-1)).nonneg_of ht (e _ (by
    change Int.mul (-1) a.1 = 0
    rw [hz.1]; rfl) (by
    change Nat.mul 1 a.2 + 1 ≤ _
    rw [show Nat.mul 1 a.2 = a.2 from Nat.one_mul _]; exact hz.2))
  push_cast at h2
  linarith

end Rep

/-! ### The Newton check -/

/-- `f(0) ≥ 0` and `f' - n f ≥ 0` on `[0, ∞)` give `f ≥ 0`. -/
theorem newton_nonneg {f f' : ℝ → ℝ} {n : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : 0 ≤ f 0)
    (h : ∀ x, 0 ≤ x → 0 ≤ f' x - n * f x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hd : ∀ x, HasDerivAt (fun y ↦ Real.exp (-n * y) * f y)
      (Real.exp (-n * x) * (f' x - n * f x)) x := fun x ↦ by
    have e := (((hasDerivAt_id x).const_mul (-n)).exp).mul (hf x)
    refine e.congr_deriv ?_
    simp only [id]
    ring
  have hm : MonotoneOn (fun y ↦ Real.exp (-n * y) * f y) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ ↦ (hd y).continuousAt.continuousWithinAt)
      (fun y _ ↦ (hd y).differentiableAt.differentiableWithinAt) fun y hy ↦ ?_
    rw [interior_Ici, Set.mem_Ioi] at hy
    rw [(hd y).deriv]
    exact mul_nonneg (Real.exp_pos _).le (h y hy.le)
  have h1 := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [mul_zero, Real.exp_zero, one_mul] at h1
  exact nonneg_of_mul_nonneg_right (h0.trans h1) (Real.exp_pos _)

/-- The exponent of a node. -/
def nval (p q : ℝ) (n : Node) : ℝ := n.1 * p + n.2 * q

/-- `p` and `q` are the values at `t` of the parameters. -/
structure ParRep (t : ℝ) (P : Par) (p q : ℝ) : Prop where
  hp : Rep t P.p p
  hq : Rep t P.q q

theorem ParRep.lin {t p q : ℝ} {P : Par} (h : ParRep t P p q) (i j : ℤ) :
    Rep t (P.lin i j) (i * p + j * q) := (h.hp.smul i).add (h.hq.smul j)

section Check

variable {t p q : ℝ} {P : Par}

/-- `l` represents the one-variable exponential polynomial `f`, with derivative `f'`. -/
inductive Sem1 (t p q : ℝ) : List (Node × PP) → (ℝ → ℝ) → Prop
  | nil : Sem1 t p q [] fun _ ↦ 0
  | cons {x : Node × PP} {l : List (Node × PP)} {c : ℝ} {g : ℝ → ℝ} : Rep t x.2 c →
      Sem1 t p q l g → Sem1 t p q (x :: l) fun u ↦ c * Real.exp (nval p q x.1 * u) + g u

theorem Sem1.sum {l : List (Node × PP)} {f : ℝ → ℝ} (h : Sem1 t p q l f) :
    Rep t (sumPP l) (f 0) := by
  induction h with
  | nil => exact rep_zero t
  | cons hx _ ih => simpa [sumPP] using hx.add ih

theorem Sem1.step (hP : ParRep t P p q) (n : Node) {l : List (Node × PP)} {f : ℝ → ℝ}
    (h : Sem1 t p q l f) : ∃ g f' : ℝ → ℝ, Sem1 t p q (step P n l) g ∧
      (∀ u, HasDerivAt f (f' u) u) ∧ ∀ u, f' u - nval p q n * f u = g u := by
  induction h with
  | nil => exact ⟨_, fun _ ↦ 0, Sem1.nil, fun u ↦ hasDerivAt_const u 0, fun u ↦ by simp⟩
  | @cons x l c g hx hl ih =>
    obtain ⟨g₀, f', h1, h2, h3⟩ := ih
    have hd : ∀ u, HasDerivAt (fun u ↦ c * Real.exp (nval p q x.1 * u) + g u)
        (c * (Real.exp (nval p q x.1 * u) * nval p q x.1) + f' u) u := fun u ↦ by
      have e := (((hasDerivAt_id u).const_mul (nval p q x.1)).exp.const_mul c).add (h2 u)
      refine (e.congr_deriv ?_)
      simp only [id, mul_one]
    have hcons : Sem1 t p q ((x.1, (P.lin (x.1.1 - n.1) (x.1.2 - n.2)).mul x.2) :: Newton.step P n l)
        (fun u ↦ ((((x.1.1 - n.1 : ℤ) : ℝ) * p + ((x.1.2 - n.2 : ℤ) : ℝ) * q) * c) *
          Real.exp (nval p q x.1 * u) + g₀ u) := Sem1.cons ((hP.lin _ _).mul hx) h1
    have hval : ∀ u, c * (Real.exp (nval p q x.1 * u) * nval p q x.1) + f' u -
        nval p q n * (c * Real.exp (nval p q x.1 * u) + g u) =
        ((((x.1.1 - n.1 : ℤ) : ℝ) * p + ((x.1.2 - n.2 : ℤ) : ℝ) * q) * c) *
          Real.exp (nval p q x.1 * u) + g₀ u := fun u ↦ by
      rw [← h3 u, nval, nval]; push_cast; ring
    by_cases h00 : x.1.1 - n.1 = 0 ∧ x.1.2 - n.2 = 0
    · refine ⟨g₀, _, ?_, hd, fun u ↦ ?_⟩
      · rw [Newton.step, h00.1, h00.2]
        exact h1
      · rw [hval u, h00.1, h00.2]; simp
    · refine ⟨_, _, ?_, hd, hval⟩
      rw [Newton.step]
      have : stepAux P x (Newton.step P n l) (x.1.1 - n.1) (x.1.2 - n.2) =
          (x.1, (P.lin (x.1.1 - n.1) (x.1.2 - n.2)).mul x.2) :: Newton.step P n l := by
        generalize x.1.1 - n.1 = i at *
        generalize x.1.2 - n.2 = j at *
        unfold stepAux
        split
        · exact absurd ⟨rfl, rfl⟩ h00
        · rfl
      rw [this]
      exact hcons

theorem check1_sound (hP : ParRep t P p q) (ht : 0 ≤ t) (ns : List Node) :
    ∀ {l : List (Node × PP)} {f : ℝ → ℝ}, Sem1 t p q l f → check1 P ns l = true →
      ∀ u, 0 ≤ u → 0 ≤ f u := by
  induction ns with
  | nil =>
    intro l f h hc u _
    cases h with
    | nil => exact le_rfl
    | cons => simp [check1] at hc
  | cons n ns ih =>
    intro l f h hc u hu
    rw [check1, Bool.and_eq_true] at hc
    obtain ⟨g, f', h1, h2, h3⟩ := h.step hP n
    refine newton_nonneg (n := nval p q n) h2 (h.sum.nonneg_of ht hc.1) (fun x hx ↦ ?_) hu
    rw [h3]
    exact ih h1 hc.2 x hx

/-- The rows represent the two-variable exponential polynomial `f`. -/
inductive Sem2 (t p q : ℝ) : List (Node × List (Node × PP)) → (ℝ → ℝ → ℝ) → Prop
  | nil : Sem2 t p q [] fun _ _ ↦ 0
  | cons {r : Node × List (Node × PP)} {rs : List (Node × List (Node × PP))} {f : ℝ → ℝ}
      {g : ℝ → ℝ → ℝ} : Sem1 t p q r.2 f → Sem2 t p q rs g →
      Sem2 t p q (r :: rs) fun u v ↦ f u * Real.exp (nval p q r.1 * v) + g u v

theorem Sem2.sum {rows : List (Node × List (Node × PP))} {f : ℝ → ℝ → ℝ} (h : Sem2 t p q rows f) :
    Sem1 t p q (rows.map fun r ↦ (r.1, sumPP r.2)) (f 0) := by
  induction h with
  | nil => exact Sem1.nil
  | @cons r rs f g hf _ ih => exact Sem1.cons (x := (r.1, sumPP r.2)) hf.sum ih

theorem Sem2.step (hP : ParRep t P p q) (n : Node) {rows : List (Node × List (Node × PP))}
    {f : ℝ → ℝ → ℝ} (h : Sem2 t p q rows f) : ∃ g f' : ℝ → ℝ → ℝ,
      Sem2 t p q (rows.map fun r ↦ (r.1, Newton.step P n r.2)) g ∧
      (∀ v u, HasDerivAt (fun u ↦ f u v) (f' u v) u) ∧
      ∀ v u, f' u v - nval p q n * f u v = g u v := by
  induction h with
  | nil => exact ⟨_, fun _ _ ↦ 0, Sem2.nil, fun _ u ↦ hasDerivAt_const u 0, fun _ u ↦ by simp⟩
  | @cons r rs f g hf _ ih =>
    obtain ⟨g₀, f', h1, h2, h3⟩ := ih
    obtain ⟨k, k', j1, j2, j3⟩ := hf.step hP n
    refine ⟨fun u v ↦ k u * Real.exp (nval p q r.1 * v) + g₀ u v,
      fun u v ↦ k' u * Real.exp (nval p q r.1 * v) + f' u v,
      Sem2.cons (r := (r.1, Newton.step P n r.2)) j1 h1,
      fun v u ↦ ((j2 u).mul_const _).add (h2 v u), fun v u ↦ ?_⟩
    simp only [← h3, ← j3]; ring

theorem check2_sound (hP : ParRep t P p q) (ht : 0 ≤ t) (us vs : List Node) :
    ∀ {rows : List (Node × List (Node × PP))} {f : ℝ → ℝ → ℝ}, Sem2 t p q rows f →
      check2 P us vs rows = true → ∀ u v, 0 ≤ u → 0 ≤ v → 0 ≤ f u v := by
  induction us with
  | nil =>
    intro rows f h hc u v _ _
    rw [check2] at hc
    have : f u v = 0 := by
      induction h with
      | nil => rfl
      | @cons r rs f g hf _ ih =>
        rw [List.all_cons, Bool.and_eq_true] at hc
        have h0 : f u = 0 := by
          generalize hl : r.2 = l at hf hc
          cases hf with
          | nil => rfl
          | cons => simp at hc
        change f u * _ + g u v = 0
        rw [ih hc.2, h0, zero_mul, zero_add]
    exact this.ge
  | cons n us ih =>
    intro rows f h hc u v hu hv
    rw [check2, Bool.and_eq_true] at hc
    obtain ⟨g, f', h1, h2, h3⟩ := h.step hP n
    refine newton_nonneg (f := fun u ↦ f u v) (n := nval p q n) (h2 v)
      (check1_sound hP ht vs h.sum hc.1 v hv) (fun x hx ↦ ?_) hu
    rw [h3]
    exact ih h1 hc.2 x v hx hv

end Check

end WYD.Newton
