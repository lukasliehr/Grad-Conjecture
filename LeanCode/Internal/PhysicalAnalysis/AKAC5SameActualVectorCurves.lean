import AKAC4SamePhysicalHilbertCurves
import AKZ15LiteralPhysicalVectorConvolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularWeightedSmoothness Grad.AnnularGeneralSourceRegularity Grad.PhaseAlgebra Grad.AnnularCurrentLow
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualPhysicalField
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation

def SmoothLowPhysicalRow.matrixAction {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output) (coherent : FamilyCoherent family)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {row : DivisionRow input lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive
      (originalMatrixBulkAction parameters family coherent 0 lower positive bounded.le row) :=
  curves.action parameters lower positive bounded _
    (originalMatrixRadialKernel_regular parameters family coherent)
    (originalMatrixRadialKernel_conjugated_smooth parameters family coherent lower positive bounded)

/-- The SAME completed physical U=F^-T w has actual all-grade smooth curves,
with the common rho and analytic phase used exactly once. -/
def SmoothLowPhysicalRow.physicalU (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {covariant : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive covariant) :
    SmoothLowPhysicalRow parameters lower positive
      (physicalUFromCovariant parameters length rho epsilon base small 0 lower positive bounded.le covariant) :=
  curves.matrixAction parameters (originalInverseTransposeFamily parameters length epsilon base)
    (originalInverseTransposeFamily_coherent parameters length rho epsilon base small) lower positive bounded

end Grad.ActualSmoothPhysicalField
