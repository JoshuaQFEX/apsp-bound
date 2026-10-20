# Word-RAM refinement of the upstream sparse local row

Author: Joshua Wharton, QFEX, joshua@qfex.com.

**Verification status:** all five upstream modules, the actual machine refinement, and the final transitive-axiom audit passed with exit status 0. The audit checked 746 declarations and permitted only `propext`, `Classical.choice`, and `Quot.sound`. The full successful per-module transcript is preserved in `verification.txt`.

## The integration claim

`LowRowRefinement.lean` connects the existing finite Light program in `LowRowMachine.lean` to the actual imported definition `ThinMatrix.SparseLocalForms.localRow`. Its task specifies the output in terms of that upstream definition; it does not replace the row by another locally defined formula.

An input consists of four physical integer arrays, a destination array, a modulus `q`, and an auxiliary width. The explicit layout equation is `n = width * q`. The precondition is inherited from the checked machine task: source arrays have their stated lengths and contents, their words satisfy the input bound, the destination lies below the free pointer, the destination is disjoint from every source, and `q ≤ n`. Source arrays may alias one another. These are physical layout and input-value premises, with no execution or correctness premise.

The postcondition preserves memory outside the destination and requires, for every retained auxiliary degree and residue,

```lean
μ' (dst + (degree.val * q + residue.val)) =
  ThinMatrix.SparseLocalForms.localRow normal row
    (listGrid data q width) degree residue
```

The program executes the four scalar terms for each cell. The normal `H(z)` row reads its third source at the previous auxiliary degree, with zero at degree zero. Every other term reads the current degree. The checked flattening identity preserves the residue when implementing this shift.

The public interfaces are:

| Declaration | Contract |
| --- | --- |
| `output_eq_localRow` | Every physical output expression equals the upstream row coefficient. |
| `rowValue_eq_localRow` | The list-based machine postcondition equals the upstream row coefficient. |
| `output_eq_denseLocalRow` | The physical output equals the upstream materialized nested-array row. |
| `solves_in` | The existing procedure satisfies the upstream-shaped task in any program containing that procedure. |
| `solves` | The singleton program satisfies the task, with no procedure-availability premise. |
| `allProgram_solves` | The fixed twelve-procedure program implements all six rows in both orientations. |
| `solvedIn` | The actual task is solved within the real-valued allowance `64 * n + 8`. |
| `time_le_materializeScalarCost` | Actual machine time is at most five times the upstream scalar-site counter, plus eight. |

The operational theorem uses the challenge framework's genuine `Light.Solves` relation, including correctness under appended procedures, machine limits, memory framing, and its step semantics. Its resource requirement is the already proved `LowRowMachine.need`: word bound `8 * U + 2`, zero additional cells, and zero additional call depth. The destination is preallocated by the input precondition. `need_polynomial` is inherited from the checked machine module.

The cost comparison is explicit:

```text
time (width * q) = 64 * (width * q) + 8
materializeScalarCost q width normal row = 14 * q * width
time (width * q) ≤ 5 * materializeScalarCost q width normal row + 8
```

The left side is a proved execution bound. No assumption equating an abstract scalar counter with machine execution is used.

## Preserved upstream source and compatibility

The upstream pin is `225c37476e31bdb27594953cc1f7738496fb4afc` of `https://github.com/shreshth-s/thin-matrix-results`. `pinned_upstream/` contains exact source snapshots. `upstream/` contains the copies actually checked by Lean.

`SparseLocalForms.lean` is byte-identical to its pinned original. All mathematical definitions and theorem statements in its four upstream dependencies are unchanged. The complete differences are recorded in `upstream_adaptations.patch`:

- Four broad imports are replaced by `ThinMatrixLocalImports`.
- One proof in `CoefficientBounds.LeafNode.eval_bound` replaces a failing rewrite on lambda operands with explicit equality transport using the same proved `mul_eq_convolution` theorem. The new proof uses `congrArg` and `Eq.mp`; it introduces no additional mathematical premise.

`ThinMatrixLocalImports.lean` imports only already available Mathlib modules. It also restores old coefficient-read notation for `AddMonoidAlgebra` by defining the coercion to be its existing `coeff` field, supplies three aliases to existing coefficient-evaluation lemmas, and derives the Fin-indexed `Vector.ofFn` read rule from the existing `GetElem` theorem. Addition, multiplication, casts, and cyclic arithmetic are not redefined by this compatibility layer.

`verify_upstream_integrity.py` checks exact SHA-256 hashes, compares the source snapshots, and permits only import-line changes and the explicitly whitelisted proof adaptation. It also checks the helper's recorded hash. The integrity check is a source provenance check; the Lean kernel check establishes the proofs.

`LowRowRefinementAudit.lean` examines the transitive axioms of all imported `ThinMatrix` declarations and all machine/refinement declarations. It rejects any axiom except `propext`, `Classical.choice`, and `Quot.sound`, and rejects an empty audit. The final operational task and `Solves` theorems are included.

## Portable reproduction

The relevant pins are:

| Dependency | Pin |
| --- | --- |
| Lean | `4.33.1` |
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` |
| Challenge `formal-math` dependency | `e1a4e6508154ea59f030480661590a9fe3018011` |
| Thin-matrix upstream | `225c37476e31bdb27594953cc1f7738496fb4afc` |

The publication layout places this directory at `apsp-bound/machine/refinement`, with the already checked `LowRowMachine.lean` and `LowRowSemantics.lean` in its parent `machine` directory. `prepare_upstream.py` validates the exact upstream commit, compares all five original source snapshots with the checkout, checks both base-source hashes, and prepares an isolated subproject at `machine/apsp-low-row-refinement` inside that checkout. It preserves the original upstream project and uses a separate Lake configuration and build directory. If the pinned upstream machine project already has a dependency package cache, the subproject can reuse it.

With Git, Python 3, Bash, and Elan installed, run these commands from the root of the published `apsp-bound` repository:

```bash
elan toolchain install leanprover/lean4:v4.33.1
git clone https://github.com/shreshth-s/thin-matrix-results thin-matrix-upstream
git -C thin-matrix-upstream checkout --detach 225c37476e31bdb27594953cc1f7738496fb4afc
python3 machine/refinement/prepare_upstream.py thin-matrix-upstream
cd thin-matrix-upstream/machine/apsp-low-row-refinement
lake update
bash build_refinement.sh
```

An existing checkout at the same pin can be passed to `prepare_upstream.py` instead. The script refuses to overwrite different existing source files. Its package manifest and toolchain come from the pinned upstream machine project; the subproject's `lakefile.toml` repeats the exact Mathlib and challenge dependency pins.

`build_refinement.sh` first checks that all dependency revisions still match the pinned manifest. It requests the Mathlib cache for the explicit 67-module root list, covering the actual dependency closure instead of requesting every Mathlib module. It then offers all 25 challenge modules and all 10 local modules to Lake in dependency order. Each command is an ordinary explicit module build, so Lake's normal source and dependency validation remains enabled. The local package passes `-j1` to Lean. The final namespace audit is run explicitly again, even if a previous build was cached. All output, including diagnostics, is retained in `verification/refinement-build.log`.

The saved verification was performed with the same source bytes, compiler version, and dependency revisions using an already populated workspace. The portable preparation and build files reorganize those checked inputs; a second cold build of this publication layout has not been claimed.

### Recorded elaboration diagnostics

The successful `SparseLocalForms` invocation emitted nonfatal `PANIC at Lean.Expr.appArg!` and `PANIC at Lean.Expr.appFn!` diagnostics from the upstream simplifier during tactic elaboration. The process returned exit status 0 and produced its compiled module. The later operational bridge and full transitive-axiom audit also returned 0. The actual successful dependency transcript, including those diagnostics, is retained in `verification.txt`; that dependency invocation was not diagnostic-free. No diagnostic suppression is part of the reproduction procedure.

`publication_files.txt` is the exact publication whitelist for this directory. It excludes the local preparation helper, cached build products, obsolete import-only artifacts, and failed diagnostic transcripts. `verification_manifest.json` records hashes of the audited source bytes and the successful compiled modules. The earlier local preparation wrapper is not needed by the portable instructions and is excluded from publication.

## Remaining scope

This integration closes the former gap between copied coefficient formulas and the actual imported upstream local-row definition. It is one component of the faster APSP construction. It does not establish the complete APSP runtime bound.

The bridge does not yet import `ThinMatrix.BinaryLowEncoder.rowBlock`. That module's dependency closure pulls in the much larger arithmetic and controller stack. A later integration can compose the present `output_eq_denseLocalRow` theorem with its existing `rowBlock_view` theorem after that stack is checked in the same model.

The full faster theorem still requires the physical shared cache, fast cyclic arithmetic, the high-query evaluator, and their integration into a complete all-edges oracle and APSP solver with its execution-derived runtime bound. Those are separate obligations; none is assumed or hidden inside this row task.
