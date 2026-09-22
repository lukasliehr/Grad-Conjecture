# Analytic weights and inverses

This topic contains the phase-weight estimates used in the analytic norms, translation and convolution estimates, and general inverse constructions.

For a bounded endomorphism T of a Banach space with norm less than one, the Neumann series gives both inverse identities for 1-T and the bound 1/(1-‖T‖). The perturbation module applies this construction around an existing inverse. These operator results are independent of the MHS equation. The phase-weight definitions are those selected for the paper.

Only modules in the accepted main-theorem dependency closure are included here. Historical alternative convolution-inverse developments remain in the local development archive.

## Entry files

- [Grad/Foundations/NeumannInverse.lean](Grad/Foundations/NeumannInverse.lean): Two-sided Banach-space Neumann inverse and norm estimate.
- [Grad/Foundations/PerturbationInverse.lean](Grad/Foundations/PerturbationInverse.lean): Perturbation of an invertible bounded linear operator.
- [AW1Submultiplicative.lean](AW1Submultiplicative.lean): Submultiplicativity of the analytic weights.
- [AW2Proof.lean](AW2Proof.lean): Parameter calculus for the weights.
- [PA7EnvelopeConvolution.lean](PA7EnvelopeConvolution.lean): Convolution estimates on square-summable sequences.

See the [library guide](../README.md) for imports and the source map.
