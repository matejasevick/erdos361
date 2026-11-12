# Erdős Problem #361 in Lean 4: forbidden subset sums in a linear range

This repository contains the Lean 4 / Mathlib formalization that accompanies the paper

> *Forbidden subset sums in a linear range: an inverse theorem and the Erdős–Graham irregularity
> problem* (Mateo Matijasevick, 2026). LaTeX source, figure and PDF are in `paper/`.

For `c > 0` let `f_c(n)` be the largest size of a set `A ⊆ {1, …, ⌊cn⌋}` such that `n` is not a
sum of distinct elements of `A`. Erdős and Graham asked whether `f_c(n)` depends on `n` in an
irregular way ([Erdős Problem #361](https://www.erdosproblems.com/361)). The paper proves that
`f_c(n) = ⌊cn⌋ − ⌈n/2⌉` for `c ≥ 1`. For `0 < c < 1`, `f_c(n)/n` has `lim sup` equal to `c/2`
and different limits along different arithmetic classes of `n`. In particular, `f_c(n)/n`
converges if and only if `c ≥ 1`. The upper bounds come from an inverse theorem: for `q` the
least positive integer not dividing `s`, every `A ⊆ [1, E]` with `|A| ≥ E/q + εT` has a subset
summing to `sT` whenever `2^(q−2)·E ≤ sT` and `T` is large.

## What is machine-checked

The eleven statements below are stated in `Challenge.lean` (namespace `Erdos361.Statement`) and
proved in `Solution.lean`. Each depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

| Lean statement | Content | Paper | Proved in |
| --- | --- | --- | --- |
| `erdos361_cge1` | `F M n = M − ⌈n/2⌉` for `1 ≤ n ≤ M` | Thm 1.1 | `Erdos361/Core.lean` |
| `erdos361_cge1_limit` | `f_c(n)/n → c − 1/2` for `c ≥ 1` | Thm 1.1 | `Erdos361/Asymptotics.lean` |
| `erdos361_irregular` | `f_c(n)/n` does not converge, `0 < c < 1` | Cor 1.5, via §6 | `Erdos361/Core.lean` |
| `erdos361_upper_half` | `f_c(n) ≤ (c/2 + ε)·n` for large `n`, `0 < c ≤ 1` | Thm 1.4(i) | `Erdos361/Asymptotics.lean` |
| `erdos361_odd_limit` | `f_c(n)/n → c/2` along odd `n`, `0 < c ≤ 1` | Thm 1.4(i) | `Erdos361/Asymptotics.lean` |
| `erdos361_mod6_limit_low` | `f_c(n)/n → c/3` along `n ≡ 2, 4 (mod 6)`, `0 < c ≤ 1/2` | Thm 1.4(ii), `q = 3` | `Erdos361/Asymptotics.lean` |
| `erdos361_mod6_limit_high` | `f_c(n)/n → 2c/3 − 1/6` along `n ≡ 2, 4 (mod 6)`, `1/2 < c < 1` | Thm 1.4(ii), `q = 3` | `Erdos361/Asymptotics.lean` |
| `erdos361_two_limit_points` | two distinct limit points of `f_c(n)/n`, `0 < c < 1` | Cor 1.5, `q ∈ {2, 3}` | `Erdos361/Asymptotics.lean` |
| `inverse_s1` | `A ⊆ [1, E]`, `|A| ≥ (1/2 + ε)E` ⇒ every `t ∈ [E, KE]` is a subset sum | Thm 1.2, `q = 2` | `Erdos361/Asymptotics.lean` |
| `inverse_s2` | `A ⊆ [1, E]`, `|A| ≥ (1/3 + ε)E` ⇒ every even `t ∈ [2E, KE]` is a subset sum | Thm 1.2, `q = 3` | `Erdos361/Asymptotics.lean` |
| `inverse_s2_restricted` | the same for even `t ∈ (2E, 3E)` with `3 ∤ t` | Thm 1.2, `s = 2` | `Erdos361/InverseMain.lean` |

`inverse_s1` and `inverse_s2` are stated for an arbitrary target `t`. They give the
representation statement of Theorem 1.2 for every `s` with `snd(s) ∈ {2, 3}` (that is, every
`s` not divisible by 6), by the short deduction in §8 of the paper. Not formalized:
- Theorem 1.2 for `q ≥ 4`, and its bound on the number of summands;
- Theorem 1.4(ii) for `q ≥ 4`;
- Corollary 1.6, Proposition 3.1 and the numerics of §7.

## Trusted surface

- `Erdos361/Statement.lean` defines `Avoids`, `Avoiders`, `F` and `Fc` and imports only Mathlib.
- `Challenge.lean` imports only Mathlib. It repeats these four definitions verbatim and states the
  eleven theorems with `sorry`.
- `Solution.lean` proves each statement by a single term from the development and prints its
  axioms.

The development contains no `axiom`, `sorry`, `native_decide`, `unsafe` or `extern`, and declares
no instances, coercions or notation.

## Layout

```
Erdos361/Statement.lean    the four trusted definitions
Erdos361/Core.lean         c ≥ 1 formula; non-convergence via bounded zero-sums
                           (Dias da Silva–Hamidoune from Mathlib's Combinatorial Nullstellensatz)
Erdos361/GoodCore.lean     good cores: greedy independent sets and Roth's theorem
Erdos361/Covering.lean     covering lemma: h-fold sums of dense sets (elementary route)
Erdos361/Freiman.lean      Freiman's 3k−3 theorem, proved from scratch
Erdos361/InverseGlue.lean  distinctification; the s = 2 statement with its inputs as hypotheses
Erdos361/InverseMain.lean  the s = 2 statement on (2E, 3E), unconditional
Erdos361/Asymptotics.lean  inverse theorems for q ∈ {2, 3}, constructions, limits of f_c(n)/n
Erdos361.lean              build root
Challenge.lean             the eleven statements, without proofs
Solution.lean              the eleven statements, proved by term assignment
CheckOriginal.lean         axiom report for the main theorems of Core and InverseMain
comparator/                Comparator configurations (all.json: all eleven statements)
checks/                    Python scripts for the source-level checks in VERIFICATION.md
paper/                     the paper: LaTeX source, figure, PDF
build.ps1, RUN_BUILD.cmd   Windows build, one module at a time, with logs
build.sh                   the same for Linux / macOS / WSL
```

## Building

The toolchain is Lean 4.31.0 (`lean-toolchain`) with Mathlib `v4.31.0` (commit `fabf563a`,
pinned in `lake-manifest.json`). You need `elan` and `git`.

```bash
lake exe cache get              # Mathlib build cache
lake build                      # the development (library Erdos361)
lake build Challenge Solution
lake env lean Solution.lean     # prints the axioms of the eleven statements
```

A full build takes about two hours on an 8 GB machine. Lake builds modules in parallel by
default, and each Lean process loads all of Mathlib. On machines with little memory, use
`build.sh` or, on Windows, `RUN_BUILD.cmd`; both build one module at a time and write one log
per step.

[Comparator](https://github.com/leanprover/comparator) runs on Linux only:
`lake env <path-to-comparator> comparator/all.json`.

## Verification record

`VERIFICATION.md` records a complete build of this repository. It gives the exit code of every
step, all axiom reports, the sha256 of every compiled file, and the source-level checks made in
place of Comparator: statement identity between `Challenge.lean` and `Solution.lean`, and a scan
for constructs that could change the meaning of the statements.
