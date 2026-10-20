/-
Author: Joshua Wharton, QFEX, joshua@qfex.com.
Audit all imported upstream declarations and the new operational refinement.
-/
import LowRowRefinement
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants do
    if (`ThinMatrix).isPrefixOf name || (`Light.LowRowRefinement).isPrefixOf name ||
        (`Light.LowRowMachine).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} used by {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "No upstream or refinement declarations loaded; audit would be empty"
  logInfo m!"Upstream/refinement axiom audit passed for {checked} declarations. Allowed axioms: propext, Classical.choice, Quot.sound."
