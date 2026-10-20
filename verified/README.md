# Complete APSP word-RAM proof

**Joshua Wharton · QFEX · [joshua@qfex.com](mailto:joshua@qfex.com)**

The final theorem proves deterministic integer APSP in

$$O\!\left(n^{1497780383/500000000}\right)=O\!\left(n^{2.995560766}\right).$$

It uses the exact `EndStatement.APSP` problem definition: directed graphs with polynomially bounded integer weights and no negative cycles, reachability and distance outputs, and the fixed-width word-RAM instruction set. For every input-magnitude exponent, the theorem provides one finite program, a word-width constant, and a natural-valued time bound valid for every admissible instance and every sufficiently large allowed word width.

The closed theorem is [Race.bound](Submission.lean):

```lean
theorem Race.bound :
    EndStatement.APSP.SolvedInTime
      ((1497780383 : Rat) / 500000000)
```

There are no unproved oracle, implementation, correctness, word-size, or execution-cost hypotheses in this theorem. The exponent **2.9929479187094** in the separate numerical project is a faster conditional bound; this theorem does not prove that exponent.

## What changes

This is a parameter refinement of **Li Xuanji's** complete batched APSP implementation and proof, following **Hrishik Sai Bojnal's** numerical refinement to exponent 2.99556085. The inherited compiler, algorithm, memory layouts, and correctness proofs retain their original attribution.

| Quantity | Earlier verified refinement | This refinement |
| --- | ---: | ---: |
| Tensor depth multiplier `c` | `20` | `20` |
| Query threshold `theta` | `56569/500000` | `5656907/50000000` |
| Block exponent `sigma` | `336175/10000000` | `3361758/100000000` |
| Final exponent | `2.99556085` | `2.995560766` |

The decrease in the exponent is exactly **0.000000084**. This is an asymptotic improvement; no practical speedup or global optimality is claimed.

The new parameters appear in the actual program as well as the analysis. Their larger integer constants require adjusted word bounds and constant allowances for parameter computation. The full execution proofs check these changes.

`Batch/Numbers.lean` proves the real logarithm and entropy bounds using forty terms of a positive atanh series, exact rational arithmetic, and Mathlib's remainder theorem. The proved bounds are `Gamma > 0.06602549498`, `q < 0.43397449436`, and `19 log(3)/log(4) < 15.057143757`. Every later asymptotic margin is propagated through the oracle, filtering host, APSP reduction, and word-RAM theorem.

## Build and verify

The project pins Lean **4.33.1**, Mathlib commit **`0df444a360eaa60ab8c11dca51a86af692955474`**, and all transitive dependencies. Install Lean through [Elan](https://github.com/leanprover/elan), then run from this directory:

```bash
lake exe cache get
python3 verify.py
```

The cache command obtains precompiled public Mathlib dependencies. `verify.py` builds this project's complete source proof and then checks:

1. The compiler is the pinned Lean version.
2. `Submission/EndStatement.lean` has the canonical challenge SHA-256 digest.
3. `Race.bound` has the exact rational `EndStatement.APSP.SolvedInTime` type declared in `manifest.json`.
4. Its transitive axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.
5. Every dependency source checkout matches its pinned commit and has no source changes, before and after the build.
6. The proof sources and configuration remain unchanged during verification.

The audit rejects admitted proofs, native decision axioms, and custom axioms. It checks the final algorithm theorem, including all of its proof dependencies.

The [recorded local verification](verification.txt) passed on 20 October 2026 after the complete 401-module build. [verification.json](verification.json) records the compiler version, exact theorem, audit result, and SHA-256 hashes of all 408 checked proof and configuration files. The [independent GitHub Actions run](https://github.com/JoshuaQFEX/apsp-bound/actions/runs/39424373480) at candidate commit `5028b65cf2a467c00a0cfe43127306e1de941614` also passed the complete-proof job. The mathematical sources in that candidate are the same as this release; the local record additionally covers the cached-group build helper and its verifier snapshot entry.

For a direct build without the extra audit:

```bash
lake build
```

On a machine with limited available memory, build the local modules in dependency order before running the final audit:

```bash
python3 scripts/build_sequential.py
python3 verify.py
```

This invokes ordinary Lake builds with one local module at a time and retains all dependency and content-hash checks. It resumes from valid cached results without treating file existence as proof that a module is current. CI uses this mode.

For faster resumption of an interrupted local build, use `python3 scripts/build_cached_groups.py` before `python3 verify.py`. That helper validates groups of existing artifacts with ordinary `lake --no-build build` commands and builds any stale module normally. It retains the same dependency and content-hash checks and does not alter build traces.

## Proof chain

| Source area | Established fact |
| --- | --- |
| `Batch/OProg`, `Batch/ORun*` | The finite counting-oracle program executes correctly with concrete step bounds |
| `Batch/ONeedPoly` | Its values, addresses, memory use, and call depth satisfy polynomial resource bounds |
| `Batch/Numbers`, `Batch/OBound` | The new real estimates imply the tighter bound for that program's execution |
| `Filter2/Host*`, `Filter2/Final` | Deterministic filtering implements all-edges Exact Triangle with the required cost |
| `Filter2/Chain` and inherited reductions | Correct min-plus and APSP programs, layouts, and running-time transfers |
| `Lang/Compiler/*` | Simulation by the challenge's fixed-width word RAM |
| `Submission.lean` | The closed exact challenge theorem |

`Submission/EndStatement.lean` is unchanged. Its SHA-256 digest is:

```text
4291e3f05781cea42f9d672ff73ceac1f6d1a0c3021038e94372fa8f7e1ad987
```

## Provenance and attribution

The source baseline is [`bigospeedrun/verifier`](https://github.com/bigospeedrun/verifier/tree/319252b348e254a4257cdc69805fd6eec3f5cd94/submissions/apsp/fringewidth-apsp-299556085), commit **`319252b348e254a4257cdc69805fd6eec3f5cd94`**, directory `submissions/apsp/fringewidth-apsp-299556085`. It contains Hrishik Sai Bojnal's refinement of Li Xuanji's submission #6, which extends the Anthropic `formal-math/3sum-apsp` development at commit `e1a4e6508154ea59f030480661590a9fe3018011`, based on the paper by Josh Alman and Virginia Vassilevska Williams.

The new rational parameters, strengthened numerical bounds, and corresponding proof modifications are attributed to **Joshua Wharton, QFEX**. Changed files identify the modifications in their headers. [MODIFICATIONS.md](MODIFICATIONS.md) records the changed files; original copyright and license notices are preserved in [LICENSE](LICENSE), [NOTICE](NOTICE), and the inherited source files. AI assistance was used in preparing and reviewing this refinement.

This repository provides a reproducible proof. Local compilation and auditing do not mean that Big O Speedrun has reviewed, accepted, or listed this new result.
