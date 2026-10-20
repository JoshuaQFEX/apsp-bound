# Candidate complete APSP proof — verification in progress

Joshua Wharton · QFEX · joshua@qfex.com

This work branch contains the proposed complete `EndStatement.APSP.SolvedInTime (1497780383/500000000)` proof. The full source build and final transitive-axiom audit are in progress. Do not treat this branch as a completed verification until both succeed.

The candidate retunes Li Xuanji's complete algorithm, following Hrishik Sai Bojnal's numerical refinement. All inherited credits and license notices are retained. The candidate exponent is2.995560766; it does not prove the separate, faster2.9929479187094 bound.

Use the pinned Lean4.33.1 toolchain and run:

```bash
lake exe cache get
python3 scripts/build_sequential.py
python3 verify.py
```

`Submission/EndStatement.lean` is unchanged. `verify.py` checks its canonical digest, the exact rational theorem type, source pins, and the final theorem's transitive axioms.
