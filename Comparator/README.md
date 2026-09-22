# Showcase comparison and proof audit

This directory checks the correspondence between the root `Showcase.lean`
and `Showcase_WithProofs.lean`. It reuses the project's existing Lean checks;
it does not require a separate comparator package or external comparator CLI.

| File | Check |
| --- | --- |
| [Showcase_SurfaceCheck.lean](Showcase_SurfaceCheck.lean) | Extracts the two presentation theorem types |
| [Showcase_ProofAudit.lean](Showcase_ProofAudit.lean) | Extracts the proved theorem types and traverses their transitive types and proof bodies |
| [Showcase_DefinitionSurface.lean](Showcase_DefinitionSurface.lean) | Copy of the presentation in disjoint validation namespaces |
| [Showcase_DefinitionCheck.lean](Showcase_DefinitionCheck.lean) | Lean definitional-equality checks for 64 declarations, including definitions, constructors, projections and theorem types |
| [Showcase_StatementEquivalence.lean](Showcase_StatementEquivalence.lean) | Proves that the grouped main conclusion is equivalent to its preceding expanded formulation |
| [LakeLayoutCheck.lean](LakeLayoutCheck.lean) | Checks Lake's actual resolution of all 5,839 relocated modules without building their proofs |

The definition check compares the contents of definitions, not just their
names. The audit includes theorem and opaque bodies (`allowOpaque := true`),
rejects unsafe and partial dependencies, and permits only `propext`,
`Classical.choice`, and `Quot.sound`. It uses Lean's `collectAxioms` as well.
The presentation's intentional `sorry` proofs never enter the proved audit.

The printed theorem types agree after normalizing the `ModuliSpace`
abbreviation; the stronger definitional-equality check is performed inside
Lean. This matters because the companion reuses the library's original
definitions rather than redefining them.

## Run the checks

After installing the pinned toolchain and fetching Mathlib's cache as described
in the root README, run these commands from the repository root:

```sh
lake build Showcase
lake build Showcase_WithProofs
lake build Comparator
```

The comparator target checks the definitions and theorem types inside Lean,
proves equivalence with the expanded statement, and audits the proved
theorems' transitive dependencies. Lake builds any missing dependencies and
reuses outputs that are already up to date.

To check that Lake resolves all 5,839 module names to their recorded source
paths, run:

```sh
lake env lean --run Comparator/LakeLayoutCheck.lean
```

The source hashes and the namespace-renamed comparison copy can also be
checked without executing Lean:

```sh
python3 Comparator/check_sources.py
```

These checks use the files and dependency pins in this repository.

## Maintaining the comparison

When changing `Showcase.lean`, regenerate `Showcase_DefinitionSurface.lean`
by replacing `Grad.Showcase` with `Grad.ShowcaseSurface.Public`, then
`Grad.MainTarget` with `Grad.ShowcaseSurface.MainTarget`. The source check
rejects a stale comparison copy. Update the list of compared declarations
if the public definitions change.

Run `python3 Comparator/check_sources.py` for a source-only integrity check
on any machine. It executes no Lean. Mathematical changes to the accepted
library require fresh validation, not merely an updated hash manifest.

See [VERIFICATION.md](VERIFICATION.md) for the verification scope and
[PAPER_CORRESPONDENCE.md](PAPER_CORRESPONDENCE.md) for the interpretation of
the paper's statement in Lean.
