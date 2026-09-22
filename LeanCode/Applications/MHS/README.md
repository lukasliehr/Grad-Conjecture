# The MHS application

This folder contains the paper-facing definitions, geometric assembly and the exact main theorem. The public theorem

```lean
Grad.OriginalMainConsumer.actualOriginal_mainTheorem :
  Grad.MainTarget.mainTheoremStatement
```

has no analytic, inverse, family or geometry premise. Its statement includes the MHS equations, boundary tangency, the round critical axis, the magnetic zero set, nested pressure tori, the full signed stabilizer, and smooth non-isolated curves in the configuration moduli spaces.

The root `Showcase_WithProofs.lean` presents the result with the paper's notation. Detailed nonlinear and inverse estimates remain in `Internal/`, and the generic iteration and regularity results have their own topic folders.

## Entry files

- [MainStatement.lean](MainStatement.lean): Exact target definitions and statement.
- [AKEH11ExactOriginalMain.lean](AKEH11ExactOriginalMain.lean): Unconditional exact main theorem.
- [ModuliCurveAssembly.lean](ModuliCurveAssembly.lean): Assembly of the moduli curve conclusion.

See the [library guide](../../README.md) for imports and the source map.
