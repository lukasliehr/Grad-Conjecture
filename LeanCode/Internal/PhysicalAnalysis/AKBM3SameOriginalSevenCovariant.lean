import AKBM2SameSmoothSevenPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8≤originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (total vector : ACore parameters 3) (scalar : ACore parameters 1)

def originalKernelSevenCurves :=
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi total vector scalar)
  let pressure := (originalRawFluxCurves parameters length rho epsilon base small lower positive bounded
    (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
  originalSmoothSevenCurves pressure xi bounded

theorem originalKernelSevenCurves_negative (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace (originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar) radius=
      sevenSlotFlatten _ 0 0 (tupleNormalizedInput parameters lower positive
        (originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar) radius) := by
  rw [originalKernelTuple_normalizedInput]
  exact originalSmoothSevenCurves_negative _ _ bounded radius

theorem originalKernelSevenCurves_covariant (compact : ℝ) (state : RetainedInverseState parameters length compact)
    (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace
      ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).covariant
        parameters length compact lower positive bounded state.val) radius=
      tupleCovariantTrace parameters length compact lower positive state
        (originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar) radius := by
  have action := originalCurveNegativeTrace_action parameters lower positive bounded
    (fun r => radialNormalizedCovariantKernel parameters length compact state.val.val r state.val.property)
    (radialNormalizedCovariantKernel_regular parameters length compact state.val)
    (radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded)
    (originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar) radius
  change originalCurveNegativeTrace
    ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).covariant
      parameters length compact lower positive bounded state.val) radius=_ at action
  rw [action,originalKernelSevenCurves_negative]
  simp only [tupleCovariantTrace,radialCovariantKernel,fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply,radialSevenSlotKernel_action,tupleNormalizedInput]

/-- Negative Fourier equality determines the SAME full smooth field. -/
theorem originalCurveFullField_eq_of_negative {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {firstRow secondRow : DivisionRow dimension lower}
    (first : SmoothLowPhysicalRow parameters lower positive firstRow)
    (second : SmoothLowPhysicalRow parameters lower positive secondRow) (bounded : lower<1)
    (radius : Icc lower (1 : ℝ))
    (same : originalCurveNegativeTrace first radius=originalCurveNegativeTrace second radius) (angles : ℝ×ℝ) :
    first.fullField bounded (radius.val,angles)=second.fullField bounded (radius.val,angles) := by
  apply congrFun (first.fullField_eq_of_doubleCoefficient bounded radius.val radius.property _
    (second.fullField_continuous_angles bounded radius.val radius.property)
    (fun axial polar => second.fullField_angular_periodic bounded radius.val axial polar)
    (fun polar axial => second.fullField_cell_periodic bounded radius.val polar axial) _) angles
  intro mode
  have coefficients := congrArg (fun trace => negativeTraceCoefficient _ 0 0 trace mode) same
  rw [originalCurveNegativeTrace_coefficient first bounded radius,
    originalCurveNegativeTrace_coefficient second bounded radius] at coefficients
  rw [← first.fullField_doubleCoefficient bounded radius.val radius.property mode]
  exact coefficients.symm

end Grad.OriginalKernelHomogeneousGraph
