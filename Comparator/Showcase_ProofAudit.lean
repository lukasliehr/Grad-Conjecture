import Showcase_WithProofs
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let environment ← getEnv
  let roots := #[``Grad.Showcase.same_moduli_class_iff,
    ``Grad.Showcase.equilibria_with_exact_cyclic_symmetry]
  for name in roots do
    let some info := environment.find? name | throwError "Missing showcase theorem: {name}"
    logInfo ("SHOWCASE_TYPE " ++ name.toString ++ " " ++ reprStr info.type)
    let axioms ← Lean.collectAxioms name
    for dependency in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "Unapproved showcase axiom: {dependency}"
    logInfo m!"SHOWCASE_AXIOMS {name} {axioms}"
  let mut checked : NameSet := {}
  let mut pending := roots
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless checked.contains name do
      checked := checked.insert name
      let some info := environment.find? name | throwError "Missing dependency: {name}"
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe or partial dependency: {name}"
      if let .axiomInfo _ := info then
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains name do
          throwError "Unapproved axiom declaration: {name}"
      pending := pending ++ info.type.getUsedConstants
      -- Include theorem proofs and opaque bodies, not only reducible definitions.
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  logInfo m!"SHOWCASE_TRANSITIVE_SAFE {checked.size}"
  logInfo "SHOWCASE_PROOF_AUDIT_COMPLETE"
