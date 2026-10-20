/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

APSP in time O(n^2.995560766) on the word-RAM of `EndStatement`.

This is the proof of Li Xuanji (GitHub: ldct), bigospeedrun/verifier pull request #6, commit
a6e77d9a122e9e3137afbf2e1ac310b2032447f4, which extends the Lean development of anthropics/formal-math
(3sum-apsp, commit e1a4e6508154ea59f030480661590a9fe3018011, by Anthropic, after the paper of Josh Alman
and Virginia Vassilevska Williams, arXiv:2610.06783) with deterministic prime-by-prime filtering,
two-digit residue lifting and batched tensor slots. This refinement follows the sharper numerical certificate by Hrishik Sai Bojnal (fringewidth),
which proved exponent 2.99556085. It changes the executable rational parameters to c = 20,
θ = 5656907/50000000 and σ = 0.03361758, tightens the proved logarithm enclosures, and adjusts
all concrete word/time bounds and asymptotic absorptions to prove exponent 2.995560766.

Parameter and numerical refinement by Joshua Wharton, QFEX <joshua@qfex.com>, 2026.
All inherited credits, license notices, algorithms, and canonical EndStatement definitions
are retained. The proof targets the complete fixed-width word-RAM EndStatement, not only a
numerical feasibility ledger.
-/
import Submission.EndStatement
import Submission.ThreeSumApsp.Batch.Final

theorem Race.bound : EndStatement.APSP.SolvedInTime ((1497780383 : Rat) / 500000000) := by
  have h : ((1497780383 : Rat) / 500000000) = (2.995560766 : ℚ) := by norm_num
  rw [h]
  exact apsp_2995560766
