import AKU85ActualCurrentSpecialization
import AKU82ActualJCSourcePayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.NonlinearDivision
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ExhaustionSourceAllocation
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.ConstrainedTransfer Grad.ChartAxisLift Grad.ChartAxisProjections

variable (parameters : PhaseParameters) (length rho : ℝ) (positive : 0 < length)
  (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
  (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (base : RealJointCore parameters reference insideR)
  (low : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) rho base.1 6 ≤
    originalCubicLowRadius parameters length)

abbrev OriginalFlatSource (parameters : PhaseParameters) (length : ℝ) :=
  LinearMap.ker (realExtraction parameters length)

def actualFiniteReferenceLift (source : OriginalFlatSource parameters length) : stateSmoothRange parameters reference insideR :=
  originalRealFiniteLiftAtReference parameters length rho base.1
    (actualFiniteCurrentField parameters reference insideR seed insideS base)
    (actualFiniteCurrentField_axis_zero parameters reference insideR seed insideS base) low source.val.val
    ((source_isFlat_iff_kernel length positive source.val).mpr source.property) reference insideR seed insideS

def actualFiniteSourceResidual (source : OriginalFlatSource parameters length) : SmoothQuotient parameters :=
  originalRealFiniteLiftResidual parameters length rho base.1
    (actualFiniteCurrentField parameters reference insideR seed insideS base)
    (actualFiniteCurrentScalar parameters reference insideR seed insideS base) low source.val.val

theorem actualFiniteReferenceLift_flat (source : OriginalFlatSource parameters length) :
    actualFiniteReferenceLift parameters length rho positive reference insideR seed insideS base low source ∈
      LinearMap.ker (realChartKappa parameters reference insideR) :=
  originalRealFiniteLift_reference_flat parameters length rho base.1 _ _ low source.val.val
    ((source_isFlat_iff_kernel length positive source.val).mpr source.property) reference insideR seed insideS

theorem actualFiniteReferenceLift_forward
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) (source : OriginalFlatSource parameters length) :
    (literalPhysicalSmoothForward parameters length reference insideR seed insideS base axis
      (actualFiniteReferenceLift parameters length rho positive reference insideR seed insideS base low source)).val =
    quotientRowsDerivative parameters length 1
      ((base.1 : ℂ),planarReferenceCore parameters+actualFiniteCurrentField parameters reference insideR seed insideS base,
        actualFiniteCurrentScalar parameters reference insideR seed insideS base)
      ![(0,originalRealFiniteLiftU parameters length rho base.1
          (actualFiniteCurrentField parameters reference insideR seed insideS base) low source.val.val,
        originalRealFiniteLiftS parameters length rho base.1
          (actualFiniteCurrentField parameters reference insideR seed insideS base) low source.val.val)] := by
  change quotientRowsDerivative parameters length 1
    (physicalReferenceState parameters reference insideR seed insideS (realJointCoreToJoint parameters reference insideR base))
    (fun _ => physicalFixedReferenceFamily parameters reference insideR seed insideS 1
      (realJointCoreToJoint parameters reference insideR base)
      (fun _ => realJointCoreToJoint parameters reference insideR
        (0,actualFiniteReferenceLift parameters length rho positive reference insideR seed insideS base low source))) = _
  rw [actualFiniteCurrentState_eq]
  have first := originalRealFiniteLift_physical_first parameters length rho base.1
    (actualFiniteCurrentField parameters reference insideR seed insideS base)
    (actualFiniteCurrentField_axis_zero parameters reference insideR seed insideS base) low source.val.val
    ((source_isFlat_iff_kernel length positive source.val).mpr source.property) reference insideR seed insideS base
  change physicalFixedReferenceFamily parameters reference insideR seed insideS 1
    (realJointCoreToJoint parameters reference insideR base)
    (fun _ => realJointCoreToJoint parameters reference insideR
      (0,actualFiniteReferenceLift parameters length rho positive reference insideR seed insideS base low source)) = _ at first
  rw [first]
  congr 1
  funext index
  fin_cases index
  rfl

theorem actualFiniteSourceResidual_literal
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) (source : OriginalFlatSource parameters length) :
    actualFiniteSourceResidual parameters length rho reference insideR seed insideS base low source =
      (source.val - literalPhysicalSmoothForward parameters length reference insideR seed insideS base axis
        (actualFiniteReferenceLift parameters length rho positive reference insideR seed insideS base low source)).val := by
  change _ = source.val.val - _
  rw [actualFiniteReferenceLift_forward parameters length rho positive reference insideR seed insideS base low axis source]
  rfl

include positive in
theorem actualFiniteSourceResidual_isFlat
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) (source : OriginalFlatSource parameters length) :
    IsFlat (actualFiniteSourceResidual parameters length rho reference insideR seed insideS base low source) := by
  rw [actualFiniteSourceResidual_literal parameters length rho positive reference insideR seed insideS base low axis source]
  have sourceFlat := (source_isFlat_iff_kernel length positive source.val).mpr source.property
  have outputFlat : IsFlat
      (literalPhysicalSmoothForward parameters length reference insideR seed insideS base axis
        (actualFiniteReferenceLift parameters length rho positive reference insideR seed insideS base low source)).val := by
    apply (source_isFlat_iff_kernel length positive _).mpr
    exact (realExtraction_forward length positive reference insideR seed insideS base axis _).trans
      (actualFiniteReferenceLift_flat parameters length rho positive reference insideR seed insideS base low source)
  apply (flatSourceProjection_range _).mp
  exact (LinearMap.range (flatSourceProjection (parameters := parameters))).sub_mem
    ((flatSourceProjection_range _).mpr sourceFlat) ((flatSourceProjection_range _).mpr outputFlat)


include positive in
theorem actualFiniteSourceResidual_higherVanishing
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) (source : OriginalFlatSource parameters length) :
    SourceHigherVanishing (actualFiniteSourceResidual parameters length rho reference insideR seed insideS base low source) :=
  originalRealFiniteLiftResidual_higherVanishing parameters length rho base.1 positive _ _
    (actualFiniteCurrentField_axis_zero parameters reference insideR seed insideS base)
    (actualFiniteCurrent_real parameters reference insideR seed insideS base axis) low source.val.val
    ((source_isFlat_iff_kernel length positive source.val).mpr source.property)
    ((mem_sourceSmoothRange parameters source.val.val).mp source.val.property).2

end Grad.FinitePhysicalJetLift
