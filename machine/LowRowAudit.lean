/-
Author: Joshua Wharton, QFEX, joshua@qfex.com.

Build-time audit of the transitive axioms of every declaration in the
low-row machine namespace. This inspection adds no mathematical premise.
-/
import LowRowSemantics
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants do
    if (`Light.LowRowMachine).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} used by {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "No LowRowMachine declarations were loaded; audit would be empty"
  logInfo m!"Axiom audit passed for {checked} declarations. Allowed axioms: propext, Classical.choice, Quot.sound."
