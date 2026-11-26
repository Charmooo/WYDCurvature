import WYDCurvature.Literal
import WYDCurvature.Final
import WYDCurvature.KuboMori
import WYDCurvature.Theorem61

/-!
# The scalar curvature of the Wigner–Yanase–Dyson metrics

Gibilisco–Isola, *On the monotonicity of scalar curvature in classical and quantum information
geometry*, J. Math. Phys. 46 (2005), math-ph/0407007.

* `WYD.Literal.conjecture81`: Conjecture 8.1, with the paper's definitions (`Literal.lean`).
* `WYD.Literal.wyd_schurIncreasing_all`: the scalar curvature of `WYD(p)` is Schur-increasing on the
  faithful states for every `p ≤ -1` and every `p ≥ 1/2` (`KuboMori.lean`; `p = 1` is Petz's
  conjecture, proved in PetzCurvature, whose modules are in `WYDCurvature/Petz`).
* `WYD.Literal.wyd_strictly_all`: strictly, for those `p` other than `p = 2`, where it is constant.
* `WYD.Theorem61.theorem61`: Theorem 6.1, `f_p` is (normalized symmetric) operator monotone iff
  `p ≤ -1` or `p ≥ 1/2`.

`scripts/Audit.lean` prints the axioms of each.
-/
