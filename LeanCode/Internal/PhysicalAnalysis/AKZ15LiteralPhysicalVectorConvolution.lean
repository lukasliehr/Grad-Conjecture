import AKZ14ExactOriginalScalarPhysicalConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)

/-- Full original convolution by the literal Fourier coefficients of F^-T.
The common radial storage and the original phase are removed exactly once. -/
theorem physicalUFromCovariant_actualConvolution (covariant : DivisionRow 3 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => matrixMultiplicationEntry 3 3
        (fun row column => physicalMatrixScalar parameters (originalInverseTransposeFamily parameters length epsilon base)
          (originalInverseTransposeFamily_coherent parameters length rho epsilon base small) row column 0
          (collarRadius lower positive bounded radius).val)
        shift (twoFrequencyTranslation shift mode)
        (originalRowCoefficient parameters power lower covariant radius (twoFrequencyTranslation shift mode)))
        (originalRowCoefficient parameters power lower
          (physicalUFromCovariant parameters length rho epsilon base small power lower positive bounded covariant) radius mode) :=
  originalMatrixBulkAction_physical parameters (originalInverseTransposeFamily parameters length epsilon base)
    (originalInverseTransposeFamily_coherent parameters length rho epsilon base small) power lower positive bounded covariant

end Grad.ActualPhysicalField
