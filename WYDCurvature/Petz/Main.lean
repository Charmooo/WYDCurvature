/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import WYDCurvature.Petz.Dittmann.Inequalities
import WYDCurvature.Petz.ForMathlib.Gibbs
import WYDCurvature.Petz.KuboMori.Resolvent

/-!
# Petz's conjecture for the Kubo–Mori metric

**The scalar curvature of the Bogoliubov–Kubo–Mori metric increases under mixing**: for faithful
density matrices `ρ`, `ϱ` of the same size, if the eigenvalues of `ρ` are majorized by those of `ϱ`
(`ρ` is more mixed than `ϱ`), then `S(ϱ) ≤ S(ρ)`. This is Petz's Conjecture 6.3 (Petz 1994,
p. 791: "the scalar curvature is monotone with respect to the 'more mixed' partial ordering of
density matrices"), in Dittmann's notation his (60), `ρ ≻ ϱ ⟹ S_ρ ≥ S_ϱ`, and Gibilisco–Isola's
Conjecture 8.2 ("the scalar curvature of BKM metric is a Schur-increasing function"). As a
consequence the scalar curvature is largest at the trace state `1/n`, where Petz computed it
(his Theorem 6.2): `S(1/n) = (n² − 1)(n² − 4)/8`.

The strict form is proved too: `S(ϱ) < S(ρ)` whenever, in addition, the spectra of `ρ` and `ϱ`
differ. Petz's condition (ii) (p. 791) and Andai's Conjecture 2.1 are written with a strict
inequality but no such proviso; taken literally they fail at `ρ = ϱ`, since "more mixed" is
reflexive. With the proviso they hold. Of Dittmann's four inequalities only (62) needs to be
strict for this, and it is (`bkmHsDeriv_ineq62_pos`).

The Kubo–Mori metric is the monotone metric of the operator monotone function
`f(t) = (t − 1)/log t`, and the Hessian of `ρ ↦ Tr ρ log ρ`, the negative of the von Neumann
entropy. Petz conjectured that its scalar curvature increases under mixing (Petz 1994; Hiai, Petz
and Tóth 1996), having verified the `2 × 2` case. His reading: through the volume of small
geodesic balls, the scalar curvature measures the average statistical uncertainty of a state,
which should grow under coarse graining (as recounted by Andai 2003 and Gibilisco–Isola 2004). In
particular, the scalar curvature of a Gibbs state is an increasing function of the temperature
(Petz 1994, p. 792), his condition (i), which he derives from the conjecture through the
majorization ordering of Gibbs states (p. 791). Dittmann computed the scalar
curvature in closed form and reduced the conjecture to the concavity of one function `hs` of three
variables, which he checked numerically but did not prove. The conjecture was first solved by Sra
(2026), albeit without an accompanying Lean certification. Here a slightly different proof is
formalized: Dittmann's closed form, and the four consequences (62)–(65) of his concavity that the
reduction uses.

The statement uses four definitions:
* `PetzCurvature.bkmForm` (`KuboMori/Form.lean`): the BKM metric at a positive definite matrix
  `ρ`, `(A, B) ↦ ∫₀¹ Re tr(A R B R) ds` with `R = ((1 - s) ρ + s)⁻¹`. It equals the usual
  resolvent integral `∫₀^∞ Re tr(A (ρ + t)⁻¹ B (ρ + t)⁻¹) dt` for all matrices `A`, `B`
  (`PetzCurvature.bkmForm_eq_integral_resolvent`, `KuboMori/Resolvent.lean`). At `ρ = diag(λ)`
  it is `∑ᵢⱼ (log λᵢ - log λⱼ)/(λᵢ - λⱼ) Re(Aᵢⱼ Bⱼᵢ)`, with `1/λᵢ` where `λᵢ = λⱼ`
  (`PetzCurvature.bkmForm_diagonal`, `PetzCurvature.bkmIntegral₂_eq_bkm`).
* `PetzCurvature.bkmChart (tracelessHermitian d) ρ` (`KuboMori/Chart.lean`): that metric on the
  density matrices near `ρ`, in the chart `z ↦ ρ + z` by traceless Hermitian matrices `z`.
* `PetzCurvature.Curvature.scalarCurvature` (`Curvature/Basic.lean`): the scalar curvature of a
  metric in a chart, from its Christoffel and Riemann maps.
* `IsMajorizedBy` (`ForMathlib/Majorization.lean`): majorization of real vectors.

The proof is Dittmann's: his Theorem 2 gives the scalar curvature as a sum over triples of
eigenvalues of one function `hs` (`KuboMori/ScalarCurvature.lean`), his Theorem 3 reduces the
conjecture to four inequalities (62)–(65) for `hs` (`Dittmann/Mixing.lean`), and the inequalities
are proved in `Dittmann/Plane.lean` and `Dittmann/Inequalities.lean` from kernel-checked sign
certificates.

## Main statements

* `PetzCurvature.scalarCurvature_bkmChart_le_of_isMajorizedBy`: **Petz's conjecture**.
* `PetzCurvature.scalarCurvature_bkmChart_lt_of_isMajorizedBy`: its strict form, for spectra
  that differ.
* `PetzCurvature.scalarCurvature_bkmChart_traceState`: the scalar curvature at the trace state,
  `(n² − 1)(n² − 4)/8` (Petz's Theorem 6.2, Dittmann's Corollary 3).
* `PetzCurvature.scalarCurvature_bkmChart_le_traceState`: the trace state has the largest scalar
  curvature among the faithful states.
* `PetzCurvature.antitoneOn_scalarCurvature_bkmChart_gibbsState`: Petz's condition (i). The scalar
  curvature of the Gibbs state `e^{-βH} / Tr e^{-βH}` decreases in the inverse temperature `β ≥ 0`.

## References

* [D. Petz, *Geometry of canonical correlation on the state space of a quantum system*][petz1994]
* F. Hiai, D. Petz and G. Tóth, *Curvature in the geometry of canonical correlation*, Studia Sci.
  Math. Hungar. 32 (1996) 235–249.
* A. Andai, *On the monotonicity conjecture for the curvature of the Kubo–Mori metric*,
  arXiv:math-ph/0310064.
* P. Gibilisco and T. Isola, *On the monotonicity of scalar curvature in classical and quantum
  information geometry*, J. Math. Phys. 46 (2005), arXiv:math-ph/0407007.
* [J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the
  Kubo–Mori metric*][dittmann1999]
* S. Sra, *A Proof of Petz's Conjecture on the Scalar Curvature of the Kubo–Mori Metric*,
  preprint v1, 9 October 2026, https://suvrit.github.io/papers/kubo-metric/.
-/

namespace PetzCurvature

open PetzCurvature.Curvature in
open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **Petz's conjecture**: the scalar curvature of the Kubo–Mori metric increases under mixing.
For faithful density matrices `ρ`, `ϱ` of the same size with the eigenvalues of `ρ` majorized by
those of `ϱ` (`ρ` more mixed than `ϱ`), `S(ϱ) ≤ S(ρ)`: Dittmann's Theorem 3 with his four
inequalities proved. -/
theorem scalarCurvature_bkmChart_le_of_isMajorizedBy {d : Type*} [Fintype d] [DecidableEq d]
    {ρ ϱ : Matrix d d ℂ} (hρ : ρ.PosDef) (hϱ : ϱ.PosDef) (hρtr : ρ.trace = 1)
    (hϱtr : ϱ.trace = 1)
    (hmix : IsMajorizedBy (hρ.1.eigenvalues ∘ (Fintype.equivFin d).symm)
      (hϱ.1.eigenvalues ∘ (Fintype.equivFin d).symm)) :
    scalarCurvature (bkmChart (tracelessHermitian d) ϱ) 0 ≤
      scalarCurvature (bkmChart (tracelessHermitian d) ρ) 0 :=
  scalarCurvature_bkmChart_le_of_isMajorizedBy_of_dittmann dittmannInequalities hρ hϱ hρtr hϱtr
    hmix

open PetzCurvature.Curvature in
open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **Petz's conjecture, strict form**: the scalar curvature of the Kubo–Mori metric increases
strictly under proper mixing. For faithful density matrices `ρ`, `ϱ` of the same size with the
eigenvalues of `ρ` majorized by those of `ϱ`, and spectra that differ (no relabeling of the
eigenvalues of `ρ` gives those of `ϱ`), `S(ϱ) < S(ρ)`: Dittmann's Theorem 3 with (62)–(65) proved
and (62) strict. -/
theorem scalarCurvature_bkmChart_lt_of_isMajorizedBy {d : Type*} [Fintype d] [DecidableEq d]
    {ρ ϱ : Matrix d d ℂ} (hρ : ρ.PosDef) (hϱ : ϱ.PosDef) (hρtr : ρ.trace = 1)
    (hϱtr : ϱ.trace = 1)
    (hmix : IsMajorizedBy (hρ.1.eigenvalues ∘ (Fintype.equivFin d).symm)
      (hϱ.1.eigenvalues ∘ (Fintype.equivFin d).symm))
    (hne : ∀ σ : Equiv.Perm d, hρ.1.eigenvalues ∘ σ ≠ hϱ.1.eigenvalues) :
    scalarCurvature (bkmChart (tracelessHermitian d) ϱ) 0 <
      scalarCurvature (bkmChart (tracelessHermitian d) ρ) 0 :=
  scalarCurvature_bkmChart_lt_of_isMajorizedBy_of_dittmann dittmannInequalities
    (fun _ _ hx hxy ↦ bkmHsDeriv_ineq62_pos hx hxy) hρ hϱ hρtr hϱtr hmix hne

/-! ### The trace state -/

section TraceState

open PetzCurvature.Curvature Finset

variable {d : Type*} [Fintype d] [DecidableEq d]

open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **The scalar curvature at the trace state** `1/n` of `n` levels is `(n² − 1)(n² − 4)/8`
(Petz 1994, Theorem 6.2; Dittmann, Corollary 3). It is `0` for qubits and positive for `n ≥ 3`. -/
theorem scalarCurvature_bkmChart_traceState [Nonempty d] :
    scalarCurvature (bkmChart (tracelessHermitian d) ((Fintype.card d : ℂ)⁻¹ • 1)) 0 =
      ((Fintype.card d : ℝ) ^ 2 - 1) * ((Fintype.card d : ℝ) ^ 2 - 4) / 8 := by
  set n := Fintype.card d
  have hn : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have e : ((n : ℂ)⁻¹ • 1 : Matrix d d ℂ) = Matrix.diagonal fun _ ↦ (((n : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Matrix.smul_one_eq_diagonal]
    push_cast
    rfl
  rw [e, scalarCurvature_bkmChart_tracelessHermitian_eq_hs (fun _ ↦ inv_pos.2 hn)
    (by simp [n, hn.ne'])]
  simp only [bkmHs_self (inv_pos.2 hn), sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **The trace state has the largest scalar curvature**: for every faithful density matrix `ρ` of
`n` levels, `S(ρ) ≤ (n² − 1)(n² − 4)/8 = S(1/n)` (`scalarCurvature_bkmChart_traceState`). This is
the consequence of Petz's conjecture he states after it (Petz 1994, p. 792), since the trace state
is majorized by every state (`isMajorizedBy_const`). -/
theorem scalarCurvature_bkmChart_le_traceState {ρ : Matrix d d ℂ} (hρ : ρ.PosDef)
    (htr : ρ.trace = 1) :
    scalarCurvature (bkmChart (tracelessHermitian d) ρ) 0 ≤
      ((Fintype.card d : ℝ) ^ 2 - 1) * ((Fintype.card d : ℝ) ^ 2 - 4) / 8 := by
  set n := Fintype.card d
  have hne : Nonempty d := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Matrix.trace] at htr
  have hn : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  set l := hρ.1.eigenvalues
  have hsum : ∑ i, (l ∘ (Fintype.equivFin d).symm) i = n * (n : ℝ)⁻¹ := by
    rw [mul_inv_cancel₀ hn.ne']
    change ∑ i, l ((Fintype.equivFin d).symm i) = 1
    rw [Equiv.sum_comp (Fintype.equivFin d).symm l]
    have h : ((∑ i, l i : ℝ) : ℂ) = 1 := by
      rw [← htr, hρ.1.trace_eq_sum_eigenvalues, Complex.ofReal_sum]
      rfl
    exact_mod_cast h
  have h : curvSum (l ∘ (Fintype.equivFin d).symm) ≤ curvSum (fun _ : Fin n ↦ (n : ℝ)⁻¹) :=
    curvSum_le_of_isMajorizedBy dittmannInequalities (fun _ ↦ inv_pos.2 hn)
      (fun _ ↦ hρ.eigenvalues_pos _) (isMajorizedBy_const hsum)
  rw [curvSum_comp_equiv] at h
  have hc : curvSum (fun _ : Fin n ↦ (n : ℝ)⁻¹) = -(n : ℝ) ^ 4 / 8 + (n : ℝ) ^ 2 / 8 := by
    simp only [curvSum, bkmHs_self (inv_pos.2 hn), sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
  rw [hc] at h
  rw [scalarCurvature_bkmChart_eq_hs hρ htr]
  simp only [curvSum] at h
  have e : -(n : ℝ) ^ 4 / 8 + (n : ℝ) ^ 2 / 8 + ((n : ℝ) ^ 2 - 1) * ((n : ℝ) ^ 2 - 2) / 4 =
      ((n : ℝ) ^ 2 - 1) * ((n : ℝ) ^ 2 - 4) / 8 := by ring
  linarith

end TraceState

/-! ### Gibbs states -/

section Gibbs

open PetzCurvature.Curvature

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The **Gibbs state** `e^{-βH} / Tr e^{-βH}` of a Hamiltonian `H` at inverse temperature `β`,
Petz's `R_β(H)` (Petz 1994, (3.1)). The exponential is the continuous functional calculus. -/
noncomputable def gibbsState (H : Matrix d d ℂ) (β : ℝ) : Matrix d d ℂ :=
  (cfc (fun x ↦ Real.exp (-(β * x))) H).trace⁻¹ • cfc (fun x ↦ Real.exp (-(β * x))) H

/-- In an eigenbasis of `H`, the Gibbs state is diagonal, carrying the Gibbs distribution of the
eigenvalues of `H`. -/
theorem gibbsState_eq {H : Matrix d d ℂ} (hH : H.IsHermitian) (β : ℝ) :
    gibbsState H β = unitaryConjL hH.eigenvectorUnitary.2
      (Matrix.diagonal fun i ↦ (gibbsDist hH.eigenvalues β i : ℂ)) := by
  set U := hH.eigenvectorUnitary
  have hc := hH.cfc_eq fun x ↦ Real.exp (-(β * x))
  have htr : (cfc (fun x ↦ Real.exp (-(β * x))) H).trace =
      ((∑ j, Real.exp (-(β * hH.eigenvalues j)) : ℝ) : ℂ) := by
    rw [hc, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem U.2, Matrix.one_mul, Matrix.trace_diagonal]
    simp
  rw [gibbsState, htr, hc, Matrix.IsHermitian.cfc, ← map_smul, Unitary.conjStarAlgAut_apply,
    unitaryConjL_apply, ← Matrix.diagonal_smul]
  congr 3
  ext i
  simp [gibbsDist, div_eq_inv_mul]

open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **Petz's condition (i): the scalar curvature of a Gibbs state increases with the
temperature.** For a Hamiltonian `H`, the scalar curvature of the Kubo–Mori metric at the Gibbs
state `e^{-βH} / Tr e^{-βH}` decreases in the inverse temperature `β ≥ 0` (Petz 1994, p. 791;
p. 792 for the reading in terms of temperature). As Petz says, it follows from the conjecture
because heating mixes: for `0 ≤ β₁ ≤ β₂`, the Gibbs state at `β₁` is more mixed than the one at
`β₂` (`isMajorizedBy_gibbsDist`). -/
theorem antitoneOn_scalarCurvature_bkmChart_gibbsState {H : Matrix d d ℂ} (hH : H.IsHermitian) :
    AntitoneOn (fun β ↦ scalarCurvature (bkmChart (tracelessHermitian d) (gibbsState H β)) 0)
      (Set.Ici 0) := by
  intro β₁ h₁ β₂ _ h₁₂
  rcases isEmpty_or_nonempty d with hd | hd
  · simp only [Subsingleton.elim (gibbsState H β₂) (gibbsState H β₁), le_refl]
  set E := hH.eigenvalues
  have hS : ∀ β, scalarCurvature (bkmChart (tracelessHermitian d) (gibbsState H β)) 0 =
      curvSum (gibbsDist E β) +
        ((Fintype.card d : ℝ) ^ 2 - 1) * ((Fintype.card d : ℝ) ^ 2 - 2) / 4 := fun β ↦ by
    rw [gibbsState_eq hH, scalarCurvature_bkmChart_unitaryConjL _
      (posDef_diagonal_ofReal (gibbsDist_pos E β)),
      scalarCurvature_bkmChart_tracelessHermitian_eq_hs (gibbsDist_pos E β) (sum_gibbsDist E β)]
    rfl
  have hmix := isMajorizedBy_gibbsDist (E ∘ (Fintype.equivFin d).symm) h₁ h₁₂
  rw [gibbsDist_comp_equiv, gibbsDist_comp_equiv] at hmix
  have h : curvSum (gibbsDist E β₂ ∘ (Fintype.equivFin d).symm) ≤
      curvSum (gibbsDist E β₁ ∘ (Fintype.equivFin d).symm) :=
    curvSum_le_of_isMajorizedBy dittmannInequalities (fun _ ↦ gibbsDist_pos E β₁ _)
      (fun _ ↦ gibbsDist_pos E β₂ _) hmix
  rw [curvSum_comp_equiv, curvSum_comp_equiv] at h
  simp only [hS]
  linarith

end Gibbs

end PetzCurvature
