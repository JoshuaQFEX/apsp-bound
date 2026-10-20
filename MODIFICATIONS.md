# Modifications to the verified APSP baseline

Joshua Wharton · QFEX · joshua@qfex.com

The source baseline is the complete `fringewidth-apsp-299556085` submission at `bigospeedrun/verifier` commit `319252b348e254a4257cdc69805fd6eec3f5cd94`. Original license and copyright notices remain in the files. This refinement changes 17 of its 401 Lean source files.

The query cutoff changes from `56569/500000` to `5656907/50000000`; the block exponent changes from `336175/10000000` to `3361758/100000000`. The tensor depth multiplier remains 20. The code constants, time bounds, and word bounds are changed together. Six real logarithm enclosures and new entropy estimates justify the tighter exponent. The final exact challenge theorem improves `2.99556085` to `2.995560766`.

No instruction semantics, input constraints, output conditions, graph definition, or runtime definition is changed. The source of `Submission/EndStatement.lean` is byte-for-byte unchanged.

## Modified Lean files

- `Submission/ThreeSumApsp/Batch/Final.lean`
- `Submission/ThreeSumApsp/Batch/Numbers.lean`
- `Submission/ThreeSumApsp/Batch/OBound.lean`
- `Submission/ThreeSumApsp/Batch/ONeedPoly.lean`
- `Submission/ThreeSumApsp/Batch/OParams.lean`
- `Submission/ThreeSumApsp/Batch/OProg.lean`
- `Submission/ThreeSumApsp/Batch/ORunParams.lean`
- `Submission/ThreeSumApsp/Batch/OSetup.lean`
- `Submission/ThreeSumApsp/Filter2/Asymp.lean`
- `Submission/ThreeSumApsp/Filter2/Chain.lean`
- `Submission/ThreeSumApsp/Filter2/Defs.lean`
- `Submission/ThreeSumApsp/Filter2/Final.lean`
- `Submission/ThreeSumApsp/Filter2/HostMain.lean`
- `Submission/ThreeSumApsp/Filter2/HostMath.lean`
- `Submission/ThreeSumApsp/Filter2/HostTime.lean`
- `Submission/ThreeSumApsp/Filter2/HostTop.lean`
- `Submission.lean`

## Supporting files

`manifest.json` records the new rational bound. The toolchain, Lake files, `verify.py`, documentation, and `provenance.json` make the full proof independently reproducible. `provenance.json` records the original and modified SHA-256 hashes for each changed Lean file. It is provenance metadata, not a premise of any theorem.

The complete program, compiler, and inherited proof remain attributed to Li Xuanji, Hrishik Sai Bojnal, Anthropic, and the original paper authors, as detailed in the README. The new parameter refinement and proof modifications are attributed to Joshua Wharton, QFEX. AI assistance was used in preparing and reviewing these changes.
