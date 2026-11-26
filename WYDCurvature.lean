import WYDCurvature.Paper.Definitions
import WYDCurvature.Paper.Conjecture81
import WYDCurvature.Paper.Theorem61
import WYDCurvature.KuboMori

/-!
# The scalar curvature of the Wigner–Yanase–Dyson metrics

Gibilisco–Isola, *On the monotonicity of scalar curvature in classical and quantum information
geometry*, J. Math. Phys. 46 (2005), math-ph/0407007.

The paper's definitions are in `WYDCurvature/Paper/Definitions.lean`, which imports no part of the proof.

* `WYD.Paper.conjecture81`: Conjecture 8.1 (`Paper/Conjecture81.lean`).
* `WYD.Paper.wyd_schurIncreasing_all`: the scalar curvature of `WYD(p)` is Schur-increasing on the
  faithful states for every `p ≤ -1` and every `p ≥ 1/2` (`KuboMori.lean`; `p = 1` is Petz's
  conjecture, proved in PetzCurvature, whose modules are in `WYDCurvature/Petz`).
* `WYD.Paper.wyd_strictly_all`: strictly, for those `p` other than `p = 2`, where it is constant.
* `WYD.Theorem61.theorem61`: Theorem 6.1, `f_p` is (normalized symmetric) operator monotone iff
  `p ≤ -1` or `p ≥ 1/2` (`Paper/Theorem61.lean`).

The proof, by part: `Metric/` (the metric in logarithmic coordinates), `Curvature/` (its scalar
curvature in closed form), `Dittmann/` (the reduction to Dittmann's inequalities (62)–(65), and (62),
(63)), `Newton/` ((64), (65) by Newton certificates checked in the kernel), `Main.lean` (the curvature
theorem for `β ∈ [-1, 2] \ {0, ½, 1}`), `OperatorMonotone/` (for Theorem 6.1), `ForMathlib/`.
`scripts/Audit.lean` prints the axioms of the main theorems.
-/
