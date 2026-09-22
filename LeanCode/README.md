# Proof library

Start with the root [proved showcase](../Showcase_WithProofs.lean) for the paper's result. For reusable mathematics, the principal entry points are:

| Topic | Content |
| --- | --- |
| [NashMoser](NashMoser/README.md) | Guarded Newton iteration, decay, summable corrections, compatible limits, exact zeros |
| [SmoothDependence](SmoothDependence/README.md) | Differentiability and smoothness of branches across regularity spaces |
| [FourierAnalysis](FourierAnalysis/README.md) | Fourier norms, interpolation, smoothing and approximation |
| [AnalyticAlgebras](AnalyticAlgebras/README.md) | Analytic weights, convolution estimates, Neumann and perturbation inverses |
| [BanachCalculus](BanachCalculus/README.md) | Smooth operator series and termwise differentiation |
| [Topology](Topology/README.md) | Configuration quotients, moduli topology and non-isolation |
| [Applications/MHS](Applications/MHS/README.md) | The paper's definitions and the assembled main theorem |
| [Internal](Internal/README.md) | Supporting functional, nonlinear and physical analysis |

The topic folders contain the proof sources, with each module included once.
The general results still have dependencies elsewhere in this package. These
folders are mathematical entry points, not independently packaged libraries.
Some constructions, especially the constrained smoothing and configuration
spaces, are specific to the present application.

## Module names and imports

File locations have changed; Lean module names have not. For example:

```lean
import NewtonGradeLimits
import AKCT3ContinuousBranchInverseRemainder
import BanachCalcSeriesProof
```

Lake uses the source roots registered in the root `lakefile.toml` to find these
modules in the topic folders. Unchanged modules can reuse matching compiled
`.olean` files with the pinned toolchain and dependencies.

[MODULES.tsv](MODULES.tsv) maps every one of the 5,839 module names to its
current path and SHA-256 hash. Names with historical prefixes remain
unchanged to preserve imports and proof outputs; the topic guides provide
descriptive entry points. No unproved blueprint units or exploratory files
are needed to compile the main result.
