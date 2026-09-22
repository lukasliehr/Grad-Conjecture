import Showcase
import Lean

open Lean Elab Command
run_cmd do
  let environment ← getEnv
  for name in #[``Grad.Showcase.same_moduli_class_iff,
      ``Grad.Showcase.equilibria_with_exact_cyclic_symmetry] do
    let some info := environment.find? name | throwError "Missing showcase theorem: {name}"
    logInfo ("SHOWCASE_TYPE " ++ name.toString ++ " " ++ reprStr info.type)
