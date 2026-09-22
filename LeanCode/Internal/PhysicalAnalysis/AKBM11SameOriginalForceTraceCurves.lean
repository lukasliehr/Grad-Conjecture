import AKBM6ActualCurveAngularDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ActualPolarEquations Grad.AnnularCurrentLow
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

theorem originalKernelSevenCurves_rotated (compact : ℝ) (state : RetainedInverseState parameters length compact)
    (radius : Icc lower (1 : ℝ)) :
    originalCurveNegativeTrace
      ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).rotatedCovariant
        parameters length compact lower positive bounded state.val) radius=
      tupleRotatedCovariantTrace parameters length compact lower positive state
        (originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar) radius := by
  have action := originalCurveNegativeTrace_action parameters lower positive bounded
    (fun r => radialNormalizedRotatedCovariantKernel parameters length compact state.val.val r state.val.property)
    (radialNormalizedRotatedCovariantKernel_regular parameters length compact state.val)
    (radialNormalizedRotatedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded)
    (originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar) radius
  change originalCurveNegativeTrace
    ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).rotatedCovariant
      parameters length compact lower positive bounded state.val) radius=_ at action
  rw [action,originalKernelSevenCurves_negative]
  simp only [tupleRotatedCovariantTrace,radialRotatedCovariantKernel,fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply,radialSevenSlotKernel_action,tupleNormalizedInput]


theorem originalKernelSevenCurves_lowPhysical (compact : ℝ) (state : RetainedInverseState parameters length compact)
    (row : Fin 3) (radius : Icc lower (1:ℝ)) :
    originalCurveNegativeTrace
      ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).lowPhysicalCurves
        parameters length compact lower positive bounded state row) radius=
      tuplePhysicalRowTrace parameters length compact lower positive state
        (originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar) radius row := by
  have action := originalCurveNegativeTrace_action parameters lower positive bounded
    (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row)
    (sameFullPhysicalRows_conjugated_smooth parameters length compact state lower positive bounded row)
    (originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar) radius
  change originalCurveNegativeTrace
    ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).lowPhysicalCurves
      parameters length compact lower positive bounded state row) radius=_ at action
  rw [action,originalKernelSevenCurves_negative]
  rfl

theorem originalKernelSevenCurves_covariantAngular (compact : ℝ) (state : RetainedInverseState parameters length compact)
    (radius : ℝ) (inside : radius∈Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle =>
      ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).covariant
        parameters length compact lower positive bounded state.val).fullField bounded (radius,angle,axial))
      (((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).rotatedCovariant
        parameters length compact lower positive bounded state.val).fullField bounded (radius,polar,axial)) polar := by
  apply originalSmoothCurve_angular_of_negative _ _ bounded _ radius inside polar axial
  intro query
  rw [originalKernelSevenCurves_covariant,originalKernelSevenCurves_rotated]
  exact tupleCovariantTrace_derivative parameters length compact lower positive state _ query

end Grad.OriginalKernelHomogeneousGraph
