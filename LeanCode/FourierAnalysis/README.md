# Fourier analysis and smoothing

The library constructs Fourier regularity spaces and proves interpolation between their norms. For integer grades r < s < t, the interpolation theorem has constant one and exponent (s-r)/(t-r).

The smoothing family is a smooth Fourier cutoff. Its estimates control the gain of regularity, the approximation error, and derivatives with respect to the smoothing scale. Later modules transfer this construction to the weighted ambient and constrained state spaces used by the paper. The Fourier estimates are broader than those application-specific state constructions.

## Entry files

- [JInterpolation.lean](JInterpolation.lean): The constant-one Fourier norm interpolation inequality.
- [SM1Cutoff.lean](SM1Cutoff.lean): Construction of the smooth cutoff.
- [SM4CutoffBounds.lean](SM4CutoffBounds.lean): Smoothing and approximation bounds.
- [SM5DerivativeBounds.lean](SM5DerivativeBounds.lean): Bounds for derivatives in the smoothing scale.
- [SM19SmoothConvergence.lean](SM19SmoothConvergence.lean): Smooth dependence on scale and convergence of the smoothing family.

See the [library guide](../README.md) for imports and the source map.
