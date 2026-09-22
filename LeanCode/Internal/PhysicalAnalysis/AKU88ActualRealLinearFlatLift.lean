import AKU83ActualSourceLinearity
import AKU87OriginalReferenceNormPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.NonlinearDivision
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ExhaustionSourceAllocation
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.ConstrainedTransfer Grad.ChartAxisLift Grad.ChartAxisProjections

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
  (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)

def originalRealFiniteLiftStateLinear : SmoothQuotient parameters →ₗ[ℝ] Grad.SmoothingFamily.StateCore parameters :=
  (0 : SmoothQuotient parameters →ₗ[ℝ] Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean 2)).prod
    ((((toPhysicalCore parameters).restrictScalars ℝ).comp
      (originalRealFiniteLiftULinear parameters length rho epsilon field low)).prod
        (originalRealFiniteLiftSLinear parameters length rho epsilon field low))

theorem originalRealFiniteLiftStateLinear_apply (source : SmoothQuotient parameters) :
    originalRealFiniteLiftStateLinear parameters length rho epsilon field low source =
      originalRealFiniteLiftState parameters length rho epsilon field low source := by
  change (0,toPhysicalCore parameters (finiteRealCore (originalFiniteLiftULinear parameters length rho epsilon field low source)),
    finiteRealCore (originalFiniteLiftSLinear parameters length rho epsilon field low source)) = _
  rw [originalFiniteLiftULinear_apply,originalFiniteLiftSLinear_apply]
  rfl

variable (positive : 0 < length) (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
  (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (base : RealJointCore parameters reference insideR)
  (actualLow : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) rho base.1 6 ≤
    originalCubicLowRadius parameters length)

def actualFiniteRawReferenceLinear : OriginalFlatSource parameters length →ₗ[ℝ] Grad.SmoothingFamily.StateCore parameters :=
  ((coreTransfer parameters seed insideS reference insideR).restrictScalars ℝ).comp
    ((originalRealFiniteLiftStateLinear parameters length rho base.1
      (actualFiniteCurrentField parameters reference insideR seed insideS base) actualLow).comp
        ((sourceSmoothRange parameters).subtype.comp (OriginalFlatSource parameters length).subtype))

include positive in
theorem actualFiniteRawReferenceLinear_apply (source : OriginalFlatSource parameters length) :
    actualFiniteRawReferenceLinear parameters length rho reference insideR seed insideS base actualLow source =
      (actualFiniteReferenceLift parameters length rho positive reference insideR seed insideS base actualLow source).val := by
  change coreTransfer parameters seed insideS reference insideR
    (originalRealFiniteLiftStateLinear parameters length rho base.1 _ actualLow source.val.val) = _
  rw [originalRealFiniteLiftStateLinear_apply]
  rfl

def actualFiniteReferenceLinear : OriginalFlatSource parameters length →ₗ[ℝ] stateSmoothRange parameters reference insideR :=
  (actualFiniteRawReferenceLinear parameters length rho reference insideR seed insideS base actualLow).codRestrict
    (stateSmoothRange parameters reference insideR) (fun source => by
      rw [actualFiniteRawReferenceLinear_apply parameters length rho positive reference insideR seed insideS base actualLow source]
      exact (actualFiniteReferenceLift parameters length rho positive reference insideR seed insideS base actualLow source).property)

theorem actualFiniteReferenceLinear_apply (source : OriginalFlatSource parameters length) :
    actualFiniteReferenceLinear parameters length rho positive reference insideR seed insideS base actualLow source =
      actualFiniteReferenceLift parameters length rho positive reference insideR seed insideS base actualLow source := by
  apply Subtype.ext
  exact actualFiniteRawReferenceLinear_apply parameters length rho positive reference insideR seed insideS base actualLow source

/-- The finite jet lift is a real linear map on the original real flat
source, valued in the original real smooth flat domain at the reference. -/
def actualFiniteFlatLiftLinear : OriginalFlatSource parameters length →ₗ[ℝ]
    LinearMap.ker (realChartKappa parameters reference insideR) :=
  (actualFiniteReferenceLinear parameters length rho positive reference insideR seed insideS base actualLow).codRestrict
    (LinearMap.ker (realChartKappa parameters reference insideR)) (fun source => by
      rw [actualFiniteReferenceLinear_apply]
      exact actualFiniteReferenceLift_flat parameters length rho positive reference insideR seed insideS base actualLow source)

theorem actualFiniteFlatLiftLinear_apply (source : OriginalFlatSource parameters length) :
    (actualFiniteFlatLiftLinear parameters length rho positive reference insideR seed insideS base actualLow source).val =
      actualFiniteReferenceLift parameters length rho positive reference insideR seed insideS base actualLow source :=
  actualFiniteReferenceLinear_apply parameters length rho positive reference insideR seed insideS base actualLow source

end Grad.FinitePhysicalJetLift
