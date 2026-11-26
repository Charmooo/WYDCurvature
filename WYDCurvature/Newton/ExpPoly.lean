/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Newton.Sound

/-!
# Exponential polynomials in two gaps: the meaning of the operations

`Sem t d a f` says that the list `a` represents `f(u, v) = ∑ c e^{(mi + mj d)u + (ni + nj d)v}`, the
packed coefficients being taken at `t`. The operations of `WYD.Newton` are sums, products and
derivatives (`Sem.add`, `Sem.mul`, `Sem.der`), and a successful Newton check gives `f ≥ 0` on the
quadrant (`Sem.nonneg_of_check`).
-/

open Real

namespace WYD.Newton

section

variable {t d : ℝ}

/-- The exponential of a term. -/
noncomputable def Term.ev (d : ℝ) (x : Term) (u v : ℝ) : ℝ :=
  exp ((x.mi + x.mj * d) * u + (x.ni + x.nj * d) * v)

/-- `a` represents `f`. -/
inductive Sem (t d : ℝ) : EP → (ℝ → ℝ → ℝ) → Prop
  | nil : Sem t d [] fun _ _ ↦ 0
  | cons {x : Term} {l : EP} {c : ℝ} {g : ℝ → ℝ → ℝ} : Rep t x.c c → Sem t d l g →
      Sem t d (x :: l) fun u v ↦ c * x.ev d u v + g u v

theorem Sem.congr {a : EP} {f g : ℝ → ℝ → ℝ} (h : Sem t d a f) (e : ∀ u v, f u v = g u v) :
    Sem t d a g := by
  have : f = g := funext fun u ↦ funext fun v ↦ e u v
  exact this ▸ h

theorem Sem.append {a b : EP} {f g : ℝ → ℝ → ℝ} (ha : Sem t d a f) (hb : Sem t d b g) :
    Sem t d (a ++ b) fun u v ↦ f u v + g u v := by
  induction ha with
  | nil => exact hb.congr fun u v ↦ (zero_add _).symm
  | cons hx _ ih => exact (Sem.cons hx ih).congr fun u v ↦ (add_assoc _ _ _).symm

theorem Term.ev_eq_of_same {x y : Term} (h : x.same y = true) (u v : ℝ) :
    x.ev d u v = y.ev d u v := by
  simp only [Term.same, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [Term.ev, Term.ev, h.1.1.1, h.1.1.2, h.1.2, h.2]

theorem Sem.merge (n : ℕ) : ∀ {a b : EP} {f g : ℝ → ℝ → ℝ}, Sem t d a f → Sem t d b g →
    Sem t d (merge n a b) fun u v ↦ f u v + g u v := by
  induction n with
  | zero => intro a b f g ha hb; exact ha.append hb
  | succ n ih =>
    intro a b f g ha hb
    cases ha with
    | nil => exact hb.congr fun u v ↦ (zero_add _).symm
    | @cons x xs c f' hx hxs =>
      cases hb with
      | nil =>
        rw [Newton.merge]
        · exact (Sem.cons hx hxs).congr fun u v ↦ (add_zero _).symm
        · simp
      | @cons y ys c' g' hy hys =>
        rw [Newton.merge]
        cases h1 : Nat.blt x.key y.key with
        | true =>
          rw [Bool.cond_true]
          exact (Sem.cons hx (ih hxs (Sem.cons hy hys))).congr fun u v ↦ by ring
        | false =>
          rw [Bool.cond_false]
          cases h2 : Nat.blt y.key x.key with
          | true =>
            rw [Bool.cond_true]
            exact (Sem.cons hy (ih (Sem.cons hx hxs) hys)).congr fun u v ↦ by ring
          | false =>
            rw [Bool.cond_false]
            cases h3 : x.same y with
            | true =>
              rw [Bool.cond_true]
              refine (Sem.cons (x := { x with c := x.c.add y.c }) (hx.add hy) (ih hxs hys)).congr
                fun u v ↦ ?_
              have e : Term.ev d { x with c := x.c.add y.c } u v = x.ev d u v := rfl
              have e' := Term.ev_eq_of_same h3 (d := d) u v
              simp only [e, ← e']
              ring
            | false =>
              rw [Bool.cond_false]
              exact (Sem.cons hx (Sem.cons hy (ih hxs hys))).congr fun u v ↦ by ring

theorem Sem.add {a b : EP} {f g : ℝ → ℝ → ℝ} (ha : Sem t d a f) (hb : Sem t d b g) :
    Sem t d (a.add b) fun u v ↦ f u v + g u v := ha.merge _ hb

/-- A list of lists represents a sum. -/
inductive SemL (t d : ℝ) : List EP → (ℝ → ℝ → ℝ) → Prop
  | nil : SemL t d [] fun _ _ ↦ 0
  | cons {a : EP} {l : List EP} {f g : ℝ → ℝ → ℝ} : Sem t d a f → SemL t d l g →
      SemL t d (a :: l) fun u v ↦ f u v + g u v

theorem SemL.congr {a : List EP} {f g : ℝ → ℝ → ℝ} (h : SemL t d a f)
    (e : ∀ u v, f u v = g u v) : SemL t d a g := by
  have : f = g := funext fun u ↦ funext fun v ↦ e u v
  exact this ▸ h

theorem SemL.flatten {l : List EP} {f : ℝ → ℝ → ℝ} (h : SemL t d l f) : Sem t d l.flatten f := by
  induction h with
  | nil => exact Sem.nil
  | cons ha _ ih => exact ha.append ih

theorem SemL.mergePairs : ∀ {l : List EP} {f : ℝ → ℝ → ℝ}, SemL t d l f →
    SemL t d (mergePairs l) f
  | [], _, h => h
  | [_], _, h => h
  | _ :: _ :: _, _, SemL.cons ha (SemL.cons hb hl) =>
    (SemL.cons (ha.add hb) hl.mergePairs).congr fun _ _ ↦ add_assoc _ _ _

theorem SemL.mergeAll (n : ℕ) : ∀ {l : List EP} {f : ℝ → ℝ → ℝ}, SemL t d l f →
    Sem t d (mergeAll n l) f := by
  induction n with
  | zero =>
    intro l f h
    cases h with
    | nil => exact Sem.nil
    | @cons a l f g ha hl =>
      cases hl with
      | nil => exact ha.congr fun u v ↦ (add_zero _).symm
      | cons hb hl => exact SemL.flatten (SemL.cons ha (SemL.cons hb hl))
  | succ n ih =>
    intro l f h
    cases h with
    | nil => exact Sem.nil
    | @cons a l f g ha hl =>
      cases hl with
      | nil => exact ha.congr fun u v ↦ (add_zero _).symm
      | cons hb hl => exact ih (SemL.mergePairs (SemL.cons ha (SemL.cons hb hl)))

theorem Term.ev_mul (x y : Term) (u v : ℝ) : (x.mul y).ev d u v = x.ev d u v * y.ev d u v := by
  rw [Term.ev, Term.ev, Term.ev, ← exp_add]
  congr 1
  simp only [Term.mul]
  push_cast
  ring

theorem Sem.mulTerm {x : Term} {c : ℝ} (hx : Rep t x.c c) {b : EP} {g : ℝ → ℝ → ℝ}
    (hb : Sem t d b g) : Sem t d (b.map fun y ↦ x.mul y) fun u v ↦ c * x.ev d u v * g u v := by
  induction hb with
  | nil => exact Sem.nil.congr fun u v ↦ (mul_zero _).symm
  | @cons y l c' g' hy _ ih =>
    refine (Sem.cons (x := x.mul y) (hx.mul hy) ih).congr fun u v ↦ ?_
    rw [Term.ev_mul]; ring

theorem Sem.mul {a b : EP} {f g : ℝ → ℝ → ℝ} (ha : Sem t d a f) (hb : Sem t d b g) :
    Sem t d (a.mul b) fun u v ↦ f u v * g u v := by
  refine SemL.mergeAll 20 ?_
  induction ha with
  | nil => exact SemL.nil.congr fun u v ↦ (zero_mul _).symm
  | cons hx _ ih =>
    exact (SemL.cons (Sem.mulTerm hx hb) ih).congr fun u v ↦ (add_mul _ _ _).symm

theorem Sem.smul {a : EP} {f : ℝ → ℝ → ℝ} {c : PP} {r : ℝ} (hc : Rep t c r) (ha : Sem t d a f) :
    Sem t d (a.smul c) fun u v ↦ r * f u v := by
  induction ha with
  | nil => exact Sem.nil.congr fun u v ↦ (mul_zero _).symm
  | @cons x l c' g hx _ ih =>
    refine (Sem.cons (x := { x with c := c.mul x.c }) (hc.mul hx) ih).congr fun u v ↦ ?_
    rw [show Term.ev d { x with c := c.mul x.c } u v = x.ev d u v from rfl]; ring

theorem Sem.clean (ht : 0 ≤ t) {a : EP} {f : ℝ → ℝ → ℝ} (ha : Sem t d a f) :
    Sem t d a.clean f := by
  induction ha with
  | nil => exact Sem.nil
  | @cons x l c g hx _ ih =>
    rw [EP.clean]
    cases h : isZero x.c with
    | true =>
      rw [Bool.cond_true]
      have := hx.eq_zero_of ht h
      exact ih.congr fun u v ↦ by rw [this, zero_mul, zero_add]
    | false => exact Sem.cons hx ih

/-! ### The formal derivative -/

/-- The function of three positions: `e^{wσ₂} f(σ₁ - σ₀, σ₂ - σ₁)`. -/
noncomputable def posFun (w : ℤ) (f : ℝ → ℝ → ℝ) (s₀ s₁ s₂ : ℝ) : ℝ :=
  exp (w * s₂) * f (s₁ - s₀) (s₂ - s₁)

/-- `∂σ_i/∂σ_k`. -/
def dlt (i k : ℕ) : ℝ := if i = k then 1 else 0

variable {p q : ℝ} {P : Par}

theorem Term.rep_lin (hP : ParRep t P p q) (hd : q = p * d) {k : ℕ} (hk : k ≤ 2) (w : ℤ)
    (x : Term) : Rep t (x.lin P k w) (p * (w * dlt 2 k + (x.mi + x.mj * d) * (dlt 1 k - dlt 0 k) +
      (x.ni + x.nj * d) * (dlt 2 k - dlt 1 k))) := by
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl | rfl
  · refine (hP.lin (-x.mi) (-x.mj)).congr ?_
    simp only [dlt, hd]; push_cast; norm_num; ring
  · refine (hP.lin (x.mi - x.ni) (x.mj - x.nj)).congr ?_
    simp only [dlt, hd]; push_cast; norm_num; ring
  · refine (hP.lin (x.ni + w) x.nj).congr ?_
    simp only [dlt, hd]; push_cast; norm_num; ring

theorem Sem.der (hP : ParRep t P p q) (hp : p ≠ 0) (hd : q = p * d) {k : ℕ} (hk : k ≤ 2) (w : ℤ)
    {a : EP} {f : ℝ → ℝ → ℝ} (ha : Sem t d a f) : ∃ g, Sem t d (a.der P k w) g ∧
      ∀ (s₀ s₁ s₂ : ℝ → ℝ) (y : ℝ), HasDerivAt s₀ (dlt 0 k) y → HasDerivAt s₁ (dlt 1 k) y →
        HasDerivAt s₂ (dlt 2 k) y → HasDerivAt (fun s ↦ posFun w f (s₀ s) (s₁ s) (s₂ s))
          (posFun w g (s₀ y) (s₁ y) (s₂ y) / p) y := by
  induction ha with
  | nil =>
    refine ⟨_, Sem.nil, fun s₀ s₁ s₂ y _ _ _ ↦ ?_⟩
    simpa [posFun] using hasDerivAt_const y (0 : ℝ)
  | @cons x l c f' hx _ ih =>
    obtain ⟨g, h1, h2⟩ := ih
    refine ⟨_, Sem.cons (x := { x with c := (x.lin P k w).mul x.c })
      ((Term.rep_lin hP hd hk w x).mul hx) h1, fun s₀ s₁ s₂ y e0 e1 e2 ↦ ?_⟩
    have hl := h2 s₀ s₁ s₂ y e0 e1 e2
    have hE : HasDerivAt (fun s ↦ (w : ℝ) * s₂ s + ((x.mi + x.mj * d) * (s₁ s - s₀ s) +
        (x.ni + x.nj * d) * (s₂ s - s₁ s))) (w * dlt 2 k + ((x.mi + x.mj * d) *
        (dlt 1 k - dlt 0 k) + (x.ni + x.nj * d) * (dlt 2 k - dlt 1 k))) y :=
      (e2.const_mul _).add (((e1.sub e0).const_mul _).add ((e2.sub e1).const_mul _))
    have h := (hE.exp.const_mul c).add hl
    have hfun : (fun s ↦ posFun w (fun u v ↦ c * x.ev d u v + f' u v) (s₀ s) (s₁ s) (s₂ s)) =
        fun s ↦ c * exp ((w : ℝ) * s₂ s + ((x.mi + x.mj * d) * (s₁ s - s₀ s) +
          (x.ni + x.nj * d) * (s₂ s - s₁ s))) + posFun w f' (s₀ s) (s₁ s) (s₂ s) := by
      funext s
      rw [posFun, posFun, Term.ev, exp_add ((w : ℝ) * s₂ s)]; ring
    rw [hfun]
    refine h.congr_deriv ?_
    rw [posFun, posFun, Term.ev, exp_add ((w : ℝ) * s₂ y)]
    field_simp
    ring

/-! ### The check -/

theorem Sem1.congr {l : List (Node × PP)} {f g : ℝ → ℝ} (h : Sem1 t p q l f)
    (e : ∀ u, f u = g u) : Sem1 t p q l g := by
  have : f = g := funext e
  exact this ▸ h

theorem Sem2.congr {l : List (Node × List (Node × PP))} {f g : ℝ → ℝ → ℝ} (h : Sem2 t p q l f)
    (e : ∀ u v, f u v = g u v) : Sem2 t p q l g := by
  have : f = g := funext fun u ↦ funext fun v ↦ e u v
  exact this ▸ h

theorem Sem.group (hd : q = p * d) {a : EP} {f : ℝ → ℝ → ℝ} (ha : Sem t d a f) :
    Sem2 t p q (group a) fun u v ↦ f (p * u) (p * v) := by
  induction ha with
  | nil => exact Sem2.nil
  | @cons x l c g hx _ ih =>
    have hev : ∀ u v, x.ev d (p * u) (p * v) =
        exp (nval p q (x.mi, x.mj) * u) * exp (nval p q (x.ni, x.nj) * v) := fun u v ↦ by
      rw [Term.ev, nval, nval, ← exp_add, hd]; congr 1; ring
    have hnew : Sem1 t p q [((x.mi, x.mj), x.c)] fun u ↦ c * exp (nval p q (x.mi, x.mj) * u) + 0 :=
      Sem1.cons (x := ((x.mi, x.mj), x.c)) hx Sem1.nil
    rw [Newton.group]
    generalize Newton.group l = rows at ih
    generalize hG : (fun u v ↦ g (p * u) (p * v)) = G at ih
    have hG' : ∀ u v, g (p * u) (p * v) = G u v := fun u v ↦ by rw [← hG]
    cases ih with
    | nil =>
      refine (Sem2.cons (r := ((x.ni, x.nj), [((x.mi, x.mj), x.c)])) hnew Sem2.nil).congr
        fun u v ↦ ?_
      simp only [hev, hG']; ring
    | @cons r rs f' g' hf hg =>
      change Sem2 t p q (bif decide (r.1.1 = x.ni) && decide (r.1.2 = x.nj) then _ else _) _
      cases h : decide (r.1.1 = x.ni) && decide (r.1.2 = x.nj) with
      | true =>
        rw [Bool.cond_true]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        have hr : r.1 = (x.ni, x.nj) := Prod.ext h.1 h.2
        refine (Sem2.cons (r := (r.1, ((x.mi, x.mj), x.c) :: r.2))
          (Sem1.cons (x := ((x.mi, x.mj), x.c)) hx hf) hg).congr fun u v ↦ ?_
        simp only [hev, hG', hr]; ring
      | false =>
        rw [Bool.cond_false]
        refine (Sem2.cons (r := ((x.ni, x.nj), [((x.mi, x.mj), x.c)])) hnew
          (Sem2.cons hf hg)).congr fun u v ↦ ?_
        simp only [hev, hG']; ring

/-- A successful Newton check gives nonnegativity on the quadrant. -/
theorem Sem.nonneg_of_check (hP : ParRep t P p q) (ht : 0 ≤ t) (hp : 0 < p) (hd : q = p * d)
    {a : EP} {f : ℝ → ℝ → ℝ} (ha : Sem t d a f) {us vs : List Node}
    (hc : check2 P us vs (Newton.group a) = true) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ f u v := by
  have h := check2_sound hP ht us vs (ha.group hd) hc (u / p) (v / p) (by positivity) (by positivity)
  simpa [mul_div_cancel₀ _ hp.ne'] using h

end

end WYD.Newton
