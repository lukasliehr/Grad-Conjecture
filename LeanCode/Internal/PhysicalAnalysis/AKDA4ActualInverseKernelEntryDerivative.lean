import AKDA3ActualMatrixOperatorDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness

/-- The ordered kernel appearing in the derivative of the SAME inverse.
Both inverse factors are the existing full-kernel inverse at this radius. -/
def negativeInverseDerivativeKernel {dimension : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (kernel slope : RadialKernel parameters radius dimension dimension)
    (low : ℝ) (small : low < 1)
    (lowBound : fullKernelMoment (radialKernelParameters parameters radius) 0 kernel ≤ low) :
    RadialKernel parameters radius dimension dimension :=
  let inverse := fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) kernel low lowBound small
  fullKernelNeg (fullKernelComposition inverse (fullKernelComposition slope inverse))

/-- Exact inverse-entry derivative at every original full Fourier cell.
This transports the proved operator resolvent derivative through a bounded
entry observation and uses the literal ordered full-kernel product. -/
theorem actualNegativeInverseKernel_hasDerivWithinAt {dimension : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius dimension dimension)
    (smooth : SmoothPolynomialFamily parameters lower positive bounded kernel)
    (low : ℝ) (small : low < 1)
    (lowBound : ∀ radius, fullKernelMoment (radialKernelParameters parameters radius) 0 (kernel radius) ≤ low)
    (base : ℝ) (inside : base ∈ Icc lower 1)
    (slope : RadialKernel parameters (collarRadius lower positive bounded base) dimension dimension)
    (derivative : HasDerivWithinAt (radialPolynomialAction parameters lower positive bounded kernel 0)
      (polynomialKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded base)) 0 slope)
      (Icc lower 1) base) (shift input : ℤ × ℤ) :
    HasDerivWithinAt (fun point =>
      (fullKernelNegativeIdentityInverse (radialKernelParameters parameters (collarRadius lower positive bounded point))
        (kernel (collarRadius lower positive bounded point)) low (lowBound _) small).entry shift input)
      ((negativeInverseDerivativeKernel parameters (collarRadius lower positive bounded base)
        (kernel (collarRadius lower positive bounded base)) slope low small (lowBound _)).entry shift input)
      (Icc lower 1) base := by
  let inverse := actualPolynomialNegativeInverse parameters lower positive bounded kernel low small lowBound
  have inverseDerivative := actualPolynomialNegativeInverse_hasDerivWithinAt parameters lower positive bounded
    kernel smooth low small lowBound base inside
    (polynomialKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded base)) 0 slope) derivative
  have sameSlope : polynomialKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded base)) 0
      (negativeInverseDerivativeKernel parameters (collarRadius lower positive bounded base)
        (kernel (collarRadius lower positive bounded base)) slope low small (lowBound _)) =
      (-((inverse base).comp (polynomialKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded base)) 0 slope))).comp
        (inverse base) := by
    simp only [negativeInverseDerivativeKernel,polynomialKernelAction_neg,polynomialKernelAction_comp]
    change -(inverse base).comp ((polynomialKernelAction _ 0 slope).comp (inverse base)) = _
    rw [ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_assoc]
  change HasDerivWithinAt inverse
    ((-((inverse base).comp (polynomialKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded base)) 0 slope))).comp
      (inverse base)) (Icc lower 1) base at inverseDerivative
  rw [← sameSlope] at inverseDerivative
  have observed := ((fourierEntryObservation ((twoFrequencyTranslation shift).symm input) input).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt
    base inverseDerivative
  change HasDerivWithinAt
    (fun point => fourierEntryObservation ((twoFrequencyTranslation shift).symm input) input (inverse point))
    (fourierEntryObservation ((twoFrequencyTranslation shift).symm input) input
      (polynomialKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded base)) 0
        (negativeInverseDerivativeKernel parameters (collarRadius lower positive bounded base)
          (kernel (collarRadius lower positive bounded base)) slope low small (lowBound _))))
    (Icc lower 1) base at observed
  simpa only [inverse,actualPolynomialNegativeInverse,radialPolynomialAction,fourierEntryObservation_kernel] using observed

end Grad.OriginalCartesianTameEstimate
