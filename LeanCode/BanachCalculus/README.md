# Banach calculus

Let Fₙ be smooth maps on an open subset of a real Banach space. If, locally around each point and at each derivative order, the norms of the derivatives have summable uniform majorants, their series converges locally uniformly. The sum of the j-th derivatives is continuous and has derivative given by the sum of the (j+1)-st derivatives, with the natural insertion of the first direction.

The series interface states the precise hypotheses; the proof file establishes them using Mathlib's calculus and infinite-series theorems. The adapter files provide the completion data and multilinear slots consumed by the application; an interface declaration alone is not an additional unconditional existence theorem.

## Entry files

- [BanachCalcSeriesInterface.lean](BanachCalcSeriesInterface.lean): The locally summable majorants and operator-series statements.
- [BanachCalcSeriesProof.lean](BanachCalcSeriesProof.lean): Locally uniform convergence and termwise Fréchet differentiation.
- [BanachCalcSeriesConsumer.lean](BanachCalcSeriesConsumer.lean): Consumer of the proved series results.
- [BanachAdapterInterface.lean](BanachAdapterInterface.lean): Data for the finite-loss completion adapter.

See the [library guide](../README.md) for imports and the source map.
