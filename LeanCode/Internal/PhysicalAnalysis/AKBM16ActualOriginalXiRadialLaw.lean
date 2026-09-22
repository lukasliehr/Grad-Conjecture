import AKBM15ActualOriginalThirdForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ActualPolarEquations Grad.ActualCartesianEquations Grad.SourceCollarFullSource
open Grad.NonlinearRange
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelRetainedDecay Grad.Constraints Grad.Cor18
open Grad.OriginalKernelCovariantRecovery Grad.AnnularPhysicalReconstruction Grad.ActualDeterminantEquations
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.SourceCollar Grad.FinitePhysicalJetLift

variable (parameters : PhaseParameters) (compact : ℝ) (nonzero : parameters.length≠0)
    (state : RetainedInverseState parameters parameters.length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      originalCoefficientLowRadius parameters parameters.length)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon : ℂ))
    (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (toPhysicalCore parameters vector))
    (homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=0)


include nonzero sameBase sameEpsilon constrained homogeneous



/-- The already proved original F1=0 supplies the genuine radial law of
this same original Xi field, at both endpoints of the closed collar. -/
theorem originalHomogeneous_xiRadial (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ) :
    let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
    let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar
    HasDerivWithinAt (fun location => xi.fullField bounded (location,angles))
      ((seven.lowPhysicalCurves parameters parameters.length compact lower positive bounded state 0).meanFree.fullField bounded (radius,angles))
      (Icc lower 1) radius := by
  dsimp only
  let xiCore := originalKernelXi physicalState.2.1 vector scalar
  let xi := originalCoreLowCurves parameters lower positive bounded xiCore
  let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  let j := seven.lowPhysicalCurves parameters parameters.length compact lower positive bounded state 0
  let tuple := originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  apply samePhysical_radialDerivative xi j.meanFree bounded _ radius inside angles
  intro mode location included
  let r : Icc lower (1:ℝ) := ⟨location,included⟩
  have trace : originalCurveNegativeTrace j.meanFree r=forceMeanFreeTrace _ 0 0
      (tupleFirstRowTrace parameters parameters.length compact lower positive state tuple r) := by
    rw [originalCurveNegativeTrace_meanFree,originalKernelSevenCurves_lowPhysical,tuplePhysicalRowTrace_first]
  have coefficient := congrArg (fun trace => negativeTraceCoefficient _ 0 0 trace mode) trace
  rw [originalCurveNegativeTrace_coefficient j.meanFree bounded r,
    j.meanFree.fullField_doubleCoefficient bounded location included mode,
    forceMeanFreeTrace,angularMeanFreeKernel,scalarModeDiagonalKernel_action_coefficient] at coefficient
  have zero := originalHomogeneous_tupleF1_zero parameters compact nonzero state small insideSeed lower positive bounded physicalState
    sameBase sameEpsilon vector scalar constrained homogeneous r mode
  change derivWithin (fun query => originalPhysicalCoefficient (xi.fullField bounded) query mode) (Icc lower 1) location-
    angularMeanFreeMultiplier mode • negativeTraceCoefficient _ 0 0
      (tupleFirstRowTrace parameters parameters.length compact lower positive state tuple r) mode=0 at zero
  rw [← coefficient] at zero
  have derivative := originalCoreCoefficient_hasDerivWithinAt parameters lower positive bounded xiCore r mode
  have slope := derivative.derivWithin ((uniqueDiffOn_Icc bounded).uniqueDiffWithinAt included)
  change derivWithin (fun query => originalPhysicalCoefficient (xi.fullField bounded) query mode) (Icc lower 1) location=_ at slope
  have sameSlope := slope.symm.trans (sub_eq_zero.mp zero)
  rw [sameSlope] at derivative
  apply derivative.congr
  · intro query member
    exact (xi.fullField_coefficient bounded query member mode).symm
  · exact (xi.fullField_coefficient bounded location included mode).symm

end Grad.OriginalKernelHomogeneousGraph
