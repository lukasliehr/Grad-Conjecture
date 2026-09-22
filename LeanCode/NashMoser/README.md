# Nash–Moser iteration

The numerical and iteration layer is formulated using explicit hypotheses on residual decay, correction estimates and smoothing errors. It includes a guarded iteration, bootstrap estimates, uniform summable tails, convergence in completed regularity spaces, and compatibility of those limits.

The exact-zero theorem shows that the limit solves the original equation when the mapping is realized continuously in the chosen completed space. This separates the convergence argument from the estimates needed for a particular equation.

These are reusable components of a Nash–Moser proof. This folder does not claim a single packaged Hamilton theorem for arbitrary tame Fréchet spaces. The MHS application supplies the inverse and remainder estimates elsewhere in the library.

## Entry files

- [GuardedNewtonIteration.lean](GuardedNewtonIteration.lean): The guarded iteration and its invariant domain.
- [NewtonConvergence.lean](NewtonConvergence.lean): Uniform summability and quantitative correction tails.
- [NewtonGradeLimits.lean](NewtonGradeLimits.lean): Convergence in complete grades and compatibility under inclusions.
- [NewtonExactZero.lean](NewtonExactZero.lean): Decay of the residual and the exact-zero conclusion.

See the [library guide](../README.md) for imports and the source map.
