# Verification

The exact main theorem is proved:

```lean
Grad.OriginalMainConsumer.actualOriginal_mainTheorem :
  Grad.MainTarget.mainTheoremStatement
```

Its source is [AKEH11ExactOriginalMain.lean](../LeanCode/Applications/MHS/AKEH11ExactOriginalMain.lean). It has no analytic, inverse, family or geometry premise. The root [Showcase_WithProofs.lean](../Showcase_WithProofs.lean) derives the paper-facing formulation from this theorem.

## Toolchain and proof dependencies

The library contains **5,839 project modules** and uses **Lean 4.33.1** with Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The exact toolchain and dependency revisions are pinned in `lean-toolchain` and `lake-manifest.json`. [MODULES.tsv](../LeanCode/MODULES.tsv) records the source path and SHA-256 hash of each project module.

The full project dependency closure has been compiled successfully. The proved showcase's transitive audit checks **111,648 declarations**, including theorem and opaque bodies. Both public theorems depend on exactly:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

The audit rejects any other axiom, including `sorryAx`, and any unsafe or partial dependency. [Showcase_ProofAudit.lean](Showcase_ProofAudit.lean) uses Lean's `collectAxioms` and traverses constant types and values with `allowOpaque := true`.

## Agreement of the two showcases

[Showcase.lean](../Showcase.lean) displays the definitions and theorem statements using only Mathlib imports. Its two presentation proofs intentionally use `sorry`. [Showcase_WithProofs.lean](../Showcase_WithProofs.lean) supplies the actual proofs and does not import the presentation file.

The comparator verifies **64 declarations**, including definition values, structure constructors and projections, and both public theorem types. It imports a namespace-renamed presentation copy and compares it with the proved environment by Lean definitional equality. This covers the paper-facing abbreviations, including `ModuliSpace`.

[Showcase_StatementEquivalence.lean](Showcase_StatementEquivalence.lean) additionally proves that the grouped main conclusion is equivalent to its fully expanded formulation.

The presentation and its namespace-renamed copy have placeholders only for the two displayed proofs. They are not dependencies of the proved main theorem. The proof audit imports only the proved companion.

## Reproducing the checks

Use the build instructions in the [root README](../README.md#build) and the commands in [Comparator/README.md](README.md#run-the-checks). The checks include the source hashes, the module-to-file mapping, declaration agreement, statement equivalence and proof dependencies.

The formalization covers Theorem 1.1 and its referenced definitions. See [PAPER_CORRESPONDENCE.md](PAPER_CORRESPONDENCE.md) for the mathematical interpretation and scope.
