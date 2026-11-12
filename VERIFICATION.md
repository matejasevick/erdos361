# Verification record

This file records a complete build of this repository from source, the axiom reports of the
statements it proves, and the source-level checks made in place of Comparator. Every claim below
is taken from the build logs or from the output of the scripts in `checks/`. Section 7 lists what
was not run.

## Summary

- **Build.** On 11–12 November 2026 every module of this repository was compiled from source with
  Lean 4.31.0 and Mathlib `v4.31.0` (commit `fabf563a`), one module at a time, by `build.ps1`.
  All 15 steps exited with code 0, and no step reported an error.
- **Axioms.** For each of the eleven statements of `Challenge.lean`, `#print axioms` applied to its
  proof in `Solution.lean` reports exactly `[propext, Classical.choice, Quot.sound]`. The same
  holds for the four main theorems of the development and for the 49 `#print axioms` commands
  inside its modules.
- **Statements.** After removal of comments, the eleven statements of `Solution.lean` are
  identical, character for character, to those of `Challenge.lean`. The definitions in
  `Challenge.lean` are identical to those of `Erdos361/Statement.lean`.
- **Sources.** The development contains no `axiom`, `sorry`, `admit`, `native_decide`, `unsafe`,
  `extern`, `implemented_by`, `opaque`, metaprogramming, instances, coercions or notation. The
  only `sorry`s in the repository are the eleven in `Challenge.lean`.
- **Files.** The compiled files were byte-identical to the files of this repository. Their SHA-256
  hashes are listed in §6.

## 1. Environment

| | |
| --- | --- |
| Machine | Windows, 12 logical processors, 7.7 GB of memory (0.7 GB free at the start) |
| Lean | `Lean (version 4.31.0, x86_64-w64-windows-gnu, commit 68218e876d2a38b1985b8590fff244a83c321783, Release)` |
| Mathlib | commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag `v4.31.0`), pinned in `lake-manifest.json` |
| Mathlib build files | the official cache, through `lake exe cache get` ("No files to download", "Already decompressed 8542 file(s)") |
| Started | 2026-11-11T19:32:47 (local time) |
| Finished | 2026-11-12T09:42:44 (local time) |

`build.ps1` copies the repository to `C:\erdos361-build`, after deleting everything there except
the downloaded dependencies (`.lake\packages`: Mathlib and the packages it requires). No build
product of this repository therefore survived from an earlier run, and every module was compiled
in this run: the log of each module's own step reports `Built <module>`, and later steps report the
module as `Replayed`.

## 2. Steps

| Step | Command | Exit code | Wall-clock time (s) |
| --- | --- | ---: | ---: |
| 01_toolchain | `elan toolchain install leanprover/lean4:v4.31.0 & lean --version` | 0 | 1 |
| 02_cache_get | `lake exe cache get` | 0 | 119 |
| 03_1 | `lake build Erdos361.Statement` | 0 | 413 |
| 03_2 | `lake build Erdos361.Core` | 0 | 47 327 |
| 03_3 | `lake build Erdos361.GoodCore` | 0 | 405 |
| 03_4 | `lake build Erdos361.Covering` | 0 | 235 |
| 03_5 | `lake build Erdos361.Freiman` | 0 | 248 |
| 03_6 | `lake build Erdos361.InverseGlue` | 0 | 236 |
| 03_7 | `lake build Erdos361.InverseMain` | 0 | 273 |
| 03_8 | `lake build Erdos361.Asymptotics` | 0 | 321 |
| 04_root | `lake build Erdos361` | 0 | 295 |
| 05_challenge | `lake build Challenge` | 0 | 288 |
| 06_solution | `lake build Solution` | 0 | 295 |
| 07_axioms_original | `lake env lean CheckOriginal.lean` | 0 | 262 |
| 08_axioms_solution | `lake env lean Solution.lean` | 0 | 278 |

Every `lake build` step ends with `Build completed successfully`. Most of the time of each step is
spent loading Mathlib: the module `Erdos361.Statement`, which contains only the four trusted
definitions, took 386 s to build. Step 03_2 ran overnight, and its wall-clock time (13 h 9 min)
does not measure the cost of the proofs: `Erdos361/Core.lean` is byte-identical to the file that
compiled in 582 s in an earlier run on the same computer.

## 3. Axiom reports

Step 08, `lake env lean Solution.lean`, verbatim:

```
'Erdos361.Statement.erdos361_cge1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.Statement.erdos361_cge1_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.Statement.erdos361_irregular' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.Statement.erdos361_upper_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.Statement.erdos361_odd_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.Statement.erdos361_mod6_limit_low' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.Statement.erdos361_mod6_limit_high' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.Statement.erdos361_two_limit_points' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.Statement.inverse_s1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.Statement.inverse_s2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.Statement.inverse_s2_restricted' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Step 07, `lake env lean CheckOriginal.lean`, verbatim:

```
'Erdos361.erdos361_cge1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361.erdos361_irregular' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361InverseMain.inverse_restricted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos361Freiman.freiman_3k3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The modules themselves contain 49 `#print axioms` commands: 5 in `GoodCore`, 15 in `Covering`, 21
in `Freiman`, 6 in `InverseGlue` and 2 in `InverseMain`. Every one of them reports
`[propext, Classical.choice, Quot.sound]`. No axiom report in any log mentions `sorryAx` or any
other axiom. The three axioms are those on which Lean's foundations and Mathlib rest:
propositional extensionality, the axiom of choice and the soundness of quotients.

## 4. Errors and warnings

No step reported an error. The logs contain 96 distinct warnings. Each is counted once here,
although Lake repeats the warnings of the modules it replays.

| Warning | Count |
| --- | ---: |
| `declaration uses 'sorry'` in `Challenge.lean`, one per statement (intended: this file states the theorems without proof) | 11 |
| deprecated tactic `push_neg` (Mathlib suggests `push Not`) | 49 |
| deprecated lemma `Finset.filter_card_add_filter_neg_card_eq_card` | 7 |
| deprecated lemmas `MvPolynomial.totalDegree_finset_sum` (4) and `MvPolynomial.totalDegree_finset_prod` (4) | 8 |
| unused variable (linter) | 17 |
| linter suggestion to use `simp` instead of `simpa` | 4 |

The 85 warnings outside `Challenge.lean` are in `Core` (22), `GoodCore` (3), `Covering` (5),
`Freiman` (34), `InverseGlue` (8) and `Asymptotics` (13); `Statement`, `InverseMain` and `Solution`
have none. None of them affects what is proved. A deprecated name still refers to a proved theorem
of Mathlib `v4.31.0`, a deprecated tactic still runs, and the linters concern style only. They
would become errors only if a later version of Mathlib removed the deprecated names.

## 5. Source checks

The scripts in `checks/` read the Lean sources and need no Lean installation. They were run with
Python 3 on this repository (`python3 -I -B checks/<script>.py .`). All comparisons are made after
removal of comments and collapsing of whitespace.

**`compare_statements.py`.**

- The definitions block of `Challenge.lean` (392 characters) is identical to that of
  `Erdos361/Statement.lean`, and both files begin with `import Mathlib` and
  `set_option autoImplicit false`.
- `Challenge.lean` and `Solution.lean` each contain 11 theorems, with the same names in the same
  order, and each statement is identical in the two files.
- In both files the theorems are stated in the same context: `namespace Erdos361.Statement`,
  `open Filter Topology`, `open scoped Pointwise`.
- Each proof in `Solution.lean` is a single term from the development:

| Statement | Proved by |
| --- | --- |
| `erdos361_cge1` | `Erdos361.erdos361_cge1` |
| `erdos361_cge1_limit` | `Erdos361Asymptotics.Fc_limit_cge1` |
| `erdos361_irregular` | `Erdos361.erdos361_irregular` |
| `erdos361_upper_half` | `Erdos361Asymptotics.Fc_upper_s1` |
| `erdos361_odd_limit` | `Erdos361Asymptotics.Fc_limit_odd` |
| `erdos361_mod6_limit_low` | `Erdos361Asymptotics.Fc_limit_mod6_low` |
| `erdos361_mod6_limit_high` | `Erdos361Asymptotics.Fc_limit_mod6_high` |
| `erdos361_two_limit_points` | `Erdos361Asymptotics.Fc_two_limit_points` |
| `inverse_s1` | `Erdos361Asymptotics.inverse_s1` |
| `inverse_s2` | `Erdos361Asymptotics.inverse_s2` |
| `inverse_s2_restricted` | `Erdos361InverseMain.inverse_restricted` |

- Outside the eleven theorems, `Solution.lean` contains only its import, `set_option autoImplicit
  false`, the namespace and `open` commands, and eleven `#print axioms` commands.

**`list_declarations.py`.** The development has 169 declarations: 66 in `Erdos361`, 40 in
`Erdos361Asymptotics`, 24 in `Erdos361Freiman`, 22 in `Erdos361Covering`, 10 in
`Erdos361InverseGlue`, 2 in `Erdos361InverseMain`, and 5 at the root (`greedy_indep`,
`hypergraph_indep`, `good_core_split`, `roth_small_nat`, `good_core_exists`). There are no
`export` commands. The script flags every declaration in a namespace that is open or enclosing
where the statements are elaborated, and every declaration whose last name component is an
identifier of the statements. It flags only the four trusted definitions
`Erdos361.Statement.Avoids`, `Avoiders`, `F` and `Fc` themselves, and `Erdos361InverseGlue.Avoids`,
an auxiliary definition in a namespace that `Solution.lean` neither opens nor encloses. The
identifiers of the statements therefore resolve to the trusted definitions.

**`scan_sources.py`.** In `Erdos361/*.lean`, `Erdos361.lean`, `Solution.lean`, `Challenge.lean` and
`CheckOriginal.lean` there are:

- no options that affect the kernel or the level of trust (`debug.*`, `trustCompiler`,
  `backward.*`, `Elab.*`, `compiler.*`); the options set are `maxHeartbeats` (between 400000 and
  4000000), `autoImplicit false` and `relaxedAutoImplicit false`;
- no `axiom`, `sorry`, `admit` or `sorryAx`, apart from the 11 `sorry`s of `Challenge.lean`;
- no `native_decide`, `ofReduceBool` or `ofReduceNat`;
- no `unsafe`, `@[extern]`, `implemented_by` or `opaque`;
- no metaprogramming (`import Lean`, `run_cmd`, `run_elab`, `run_meta`, `#eval`, `elab`, `macro`,
  `macro_rules`, `syntax`, `addDecl`);
- no instances or instance attributes, and no `notation`, `infix`, `prefix`, `postfix`, coercion
  attributes, `unif_hint` or `default_instance`;
- no scoped or local commands other than `open scoped Classical` and `open scoped Pointwise`.

**Step 09 (hygiene).** A case-insensitive search of `Erdos361/*.lean` and `Solution.lean` for
`sorry`, `native_decide` and lines beginning with `axiom ` found a single line, the comment
`Axiom footprint of every theorem …` at `Solution.lean:9`.

## 6. Files

The build directory received 34 files: the 33 files of this repository at the time of the build,
and a Python bytecode cache (`checks/__pycache__/_common.cpython-310.pyc`) left by an earlier run
of the check scripts, which git ignores and the build does not use. The SHA-256 hashes computed in
the build directory after the build (step 10) agree with those of the repository files.

Four documentation files were edited after the build and are not used by it: `README.md` and
`formalization.yaml` (author name), and `paper/erdos361_paper.tex` and `paper/erdos361_paper.pdf`
(author name and §8). This file was added after the build. The other 29 files are unchanged since
the build:

```
04f604dec5b7110b89afd51f362454758d84110b6f7be15be128c5203498218b  .gitignore
0e5ebe74ca80222ba5f5d45f344284d81997bff0ab70fdd79164b79e629eeeff  Challenge.lean
9c3cdba8b9eb6730a24160d3db87324f842b9d21f61c53d12d2f15ae440bb314  CheckOriginal.lean
5794c3a21b00fd79424e75bd8d7537091360ce9ec32dd9223c8247fadbe13413  Erdos361.lean
575910efc82177ff44180b6c16310aecc1ad92622946ceedeb02ed272ec7770e  Erdos361/Asymptotics.lean
7cb8c04f2b110a86fd20b440429d64d17a4ba68c56cb993f4c84106f198aa6c0  Erdos361/Core.lean
51c37fc674656c1e40bdd00cc04b250f39bf248091a2bc747d744ed84faa065a  Erdos361/Covering.lean
469c0645f0afccbfda4b122ecc3a3d4111f8a01fb4894af0785ed70d0f63ea93  Erdos361/Freiman.lean
ce1dbaa219d14729372905630676f884cd20fccef68d8f88f224a8a8316408ac  Erdos361/GoodCore.lean
42c96bdc807cd57c96f79a4fcaf3da201d1c95250c18a0e1573015f06ca06d95  Erdos361/InverseGlue.lean
2eca88636a707ac274498d0fbc00d0241dc02b29a1b9dfca7b25cc5caaa9668b  Erdos361/InverseMain.lean
64c5036bb0b528caa3c254eea3e0a13bc1e19d7b241e969953c4d5238f2dc235  Erdos361/Statement.lean
8e84c12607b066ed68b1b58b5cdbd27687424ff8b5585dd17820e86271c67ca1  RUN_BUILD.cmd
2439d44e389724582dcf2d6b89f01902e29813784dccdcfb2a52c6c500984db7  Solution.lean
8e666f79fe1fa82f334b0c0e153aefa8abb841ed2c2c74729d307b97289a26fd  build.ps1
c36a36265886c93608c31dbf9bd0af8e61cc2121e4a84217d0aae987709ff16a  build.sh
c052c4483c2164e6e788429e7e273c33241080f35bf122cbabf3ebcb59550347  checks/_common.py
f0ddd29c81bb34bfb694ab47db8724290fa8ea1c49dd50e68006b9b4cbc3dfc6  checks/compare_statements.py
0913b710dc9be4ae5e918a43aa474b1a6649ff3448d0e3692acb7a397347b929  checks/list_declarations.py
0bcac8724631ed27327ea957fca387174b1af7fc1c98216906926ee1c3215e35  checks/scan_sources.py
b72351095f0fa5d6954ca1a4533eb58e488c9b521116cdaaa87eec8406815619  comparator/all.json
efbecc9b6050886ecd12e294b000eaf4a6d5de600eb0a4cebcd4f094166fb66e  comparator/erdos361_asymptotics.json
c24d4c638d7d3e4fc1eeefbb388f49a3a9f5455cf4168b3551aa00dbd5026e4d  comparator/erdos361_cge1.json
0443051516ea3f99975ba6c2b24f7877564fd3b1de5f4f25b3294a2f0de53170  comparator/erdos361_inverse_restricted.json
f6a6d769fbe17448f357c67d15f12ac8f31c3f640d737425ee7f3a9b6deffaf5  comparator/erdos361_irregular.json
882a7b5c59369effa87c4492ed0e9339c487a25c4d8b2c734701a4535adb25a0  lake-manifest.json
7dc27f6fdd4cfd65834d64227197f6b994ec3ca730f12bc7af7da9a5f41c5c77  lakefile.toml
efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee  lean-toolchain
b22650aaa48e08dc748f1e9e604fe6a6803729672668d5526d778ea95faa076a  paper/fig_fc.pdf
```

To check them, run `sha256sum -c` on these lines, or `Get-FileHash -Algorithm SHA256` in
PowerShell.

## 7. Not covered by this record

- Comparator (configurations in `comparator/`) was not run, because it requires Linux.
- No negative control was run, that is, no deliberately weakened or falsified statement was
  checked to fail.
- The thresholds in the statements are existential (`∃ E₀`, `∃ N₀`), not explicit.

## 8. Reproduction

```bash
lake exe cache get                     # Mathlib build cache
lake build                             # the development (library Erdos361)
lake build Challenge Solution
lake env lean Solution.lean            # axiom reports of the eleven statements
lake env lean CheckOriginal.lean       # axiom reports of four main theorems of the development
python3 -I -B checks/compare_statements.py .
python3 -I -B checks/list_declarations.py .
python3 -I -B checks/scan_sources.py .
```

On Windows, `RUN_BUILD.cmd` runs the steps of §2 one at a time and writes one log per step to the
folder `erdos361-build-logs` next to the repository. `build.sh` does the same on Linux, macOS or
WSL, with the logs in `logs/`.
