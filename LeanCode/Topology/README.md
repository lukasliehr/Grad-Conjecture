# Topology and non-isolation

A continuous injective curve from a subset of the real line into any topological space has non-isolated image points at interior parameter values. Every neighborhood of such an image point contains the image of a different parameter. This theorem needs no separation axiom on the target.

The remaining modules define and analyze the paper's configuration quotient and regularity topology. They establish that quotient equality is exactly the stated equivalence relation. These definitions are specific to the moduli problem, while the curve non-isolation argument is general.

## Entry files

- [ModuliCurveNonisolation.lean](ModuliCurveNonisolation.lean): The general continuous-curve non-isolation theorem.
- [RelatedEquivalence.lean](RelatedEquivalence.lean): Equivalence relation and quotient equality.
- [ModuliTopology.lean](ModuliTopology.lean): The topology on the configuration quotient.
- [ReparametrizationRegularity.lean](ReparametrizationRegularity.lean): Regularity under reparametrization.

See the [library guide](../README.md) for imports and the source map.
