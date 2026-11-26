# WYDCurvature

A Lean 4 / Mathlib formalization of **Conjecture 8.1** of Gibilisco and Isola, *On the monotonicity
of scalar curvature in classical and quantum information geometry*, J. Math. Phys. 46 (2005)
(arXiv:math-ph/0407007). The conjecture says the scalar curvature of the Wigner–Yanase–Dyson
metric WYD(p) is Schur-increasing on the faithful states for p just above 1. Here it is proved for
**every p ≤ −1 and every p ≥ ½**, for every n, and strictly for p ≠ 2. The paper's Theorem 6.1,
that these are exactly the p for which `f_p` is operator monotone, is proved as well.

## Main results

| Lean name | Statement |
|---|---|
| `WYD.Literal.conjecture81` | Conjecture 8.1, with the paper's definitions (`WYDCurvature/Literal.lean`) |
| `WYD.Literal.wyd_schurIncreasing_all` | Schur-increasing for every `p ≤ -1` and `p ≥ 1/2`, all `n` |
| `WYD.Literal.wyd_strictly_all` | the same, strictly, for `p ≠ 2` (at `p = 2` the curvature is constant) |
| `WYD.Theorem61.theorem61` | Theorem 6.1: `f_p` is (normalized symmetric) operator monotone iff `p ≤ -1 ∨ 1/2 ≤ p` |

`Literal.lean` states everything with the paper's own objects: `f_p` (Definition 6.1), the
Morozova–Chentsov function, `c_f(L_ρ, R_ρ)`, the WYD(p) metric on the faithful states (Definition 6.2)
and its scalar curvature. All of them depend only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); `scripts/Audit.lean` prints them. There is no `sorry`,
`native_decide`, `set_option` or `axiom` in the library.

The case p = 1 (the Kubo–Mori metric, `f_1 = f_∞`) is Petz's conjecture, proved in
[PetzCurvature](https://github.com/Charmooo/PetzCurvature). Its own modules are included in
`WYDCurvature/Petz` (from PetzCurvature commit `4ff69a7`, Lean 4.36.0) with only their imports
changed, so that they build on [AlphaCurvature](https://github.com/Charmooo/AlphaCurvature)'s copies
of the shared files; the two libraries cannot be imported together.

## Building

Lean 4.36.0, Mathlib `v4.36.0`, AlphaCurvature as a Lake dependency.

```
lake exe cache get
lake build
```

A full build after `cache get` takes about 11 minutes on an 18-core machine. The certificate modules
are the heavy part: twelve Newton certificates `C64_*`, `C65_*` (about 4–5 GB each) and the two halves
of PetzCurvature's Dittmann certificate (about 9 GB each). They import each other in a chain, so Lake
checks them one at a time whatever the job count; the import adds nothing to the proofs. Peak memory
of a single Lean process is about 9 GB.

Checks after building:

```
python3 scripts/replay.py 12          # every module of WYDCurvature and AlphaCurvature through the kernel again
lake env lean scripts/Audit.lean      # axioms of the main theorems
```

`scripts/replay1.lean` is `leanchecker`'s `replayFromImports` for exactly one module; `replay.py`
runs it module by module under a memory cap.

## How the proof goes

`docs/reduction.tex` (and `.pdf`) is the human-readable proof. In short:

* WYD(p), β = 1/p, is the pullback of a constant pairing by ρ ↦ (ρ^β, ρ^{1−β}), which gives a closed form
  for the scalar curvature through a Gauss equation. Schur-monotonicity then reduces to Dittmann's four
  inequalities (62)–(65) for an explicit kernel `hs_β`, as in PetzCurvature.
* (62) and (63) are proved by hand (for (63), an autonomous ODE system and two barrier arguments).
* (64) and (65): the cleared numerators are exponential polynomials. In Newton form on their own exponents,
  with d = t/(1+t) or (3+t)/(1+t), every Newton coefficient is a polynomial in t with nonnegative integer
  coefficients. The kernel checks this (`WYDCurvature/Newton*.lean`, `C6*.lean`).
  `scripts/certs/gencert.py` regenerates the twelve certificate files byte for byte (needs `python-flint`).
* Theorem 6.1: 1/f_p is an average over [0,1]² of inverses of weighted operator geometric means of
  operator monotone functions (`GeomMean.lean`, `OpMono.lean`, `Theorem61.lean`). The "only if" half uses
  1×1 matrices.

## Layout

| path | contents |
|---|---|
| `WYDCurvature/Literal.lean` | the statements with the paper's definitions |
| `WYDCurvature/Final.lean` | the curvature theorem for β ∈ [−1, 2] \ {0, ½, 1} |
| `WYDCurvature/KuboMori.lean` | p = 1, joined from PetzCurvature; the whole range |
| `WYDCurvature/Theorem61.lean` | Theorem 6.1 |
| `WYDCurvature/Petz/` | PetzCurvature's modules |
| `docs/` | `reduction.tex`, the written proof |
| `scripts/` | replay, audit, certificate generator |

## Authors

Adam Bornemann, with Claude (Anthropic). Apache 2.0, see `LICENSE`.
