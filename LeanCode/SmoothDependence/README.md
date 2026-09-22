# Smooth dependence

These three general modules treat a family of normed spaces indexed by regularity. A continuous solution branch, a candidate derivative, and a two-scale remainder estimate imply differentiability in every grade. If each derivative can be realized as a sufficiently smooth map of the parameter and a higher-grade branch value, an induction gives smoothness in every grade.

The regularity spaces and parameter space are abstract in these statements. Neither differentiability nor smoothness of the branch is silently assumed. The remainder bounds and smooth realizations are the explicit analytic obligations for an application. The original MHS branch is assembled in `AKCT4OriginalNewtonParameterSmoothness`, in the supporting physical analysis.

## Entry files

- [AKCT1BranchDerivativeLowAbsorption.lean](AKCT1BranchDerivativeLowAbsorption.lean): Absorb the low-grade remainder and obtain the derivative.
- [AKCT2FiniteInputSmoothBranchBootstrap.lean](AKCT2FiniteInputSmoothBranchBootstrap.lean): Bootstrap through finite-input derivative realizations.
- [AKCT3ContinuousBranchInverseRemainder.lean](AKCT3ContinuousBranchInverseRemainder.lean): Combined all-grade differentiability and smoothness theorem.

See the [library guide](../README.md) for imports and the source map.
