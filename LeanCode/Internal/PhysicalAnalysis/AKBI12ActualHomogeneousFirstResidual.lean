import AKBI11SameRetainedForceRadialTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery Grad.Constraints Grad.Cor18
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.SourceCollar Grad.FinitePhysicalJetLift
open Grad.NonlinearRange

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
    (radius : Icc lower (1 : ℝ))

include nonzero sameBase sameEpsilon constrained homogeneous

/-- The first computed original AH24 residual vanishes for the SAME
original constrained smooth homogeneous field. -/
theorem originalHomogeneous_tupleF1_zero (mode : ℤ×ℤ) :
    originalTupleF1 parameters parameters.length compact lower positive state
      (originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
        lower positive bounded physicalState.2.1 vector scalar) radius mode=0 := by
  let xi := originalKernelXi physicalState.2.1 vector scalar
  let tuple := originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  have first := originalFirstTrace_scaledEuler parameters parameters.length compact nonzero state lower positive bounded vector radius
  have actual := originalHomogeneous_firstRowRecovery parameters compact nonzero state small insideSeed lower positive bounded physicalState
    sameBase sameEpsilon vector scalar constrained homogeneous radius
  change tupleFirstRowTrace parameters parameters.length compact lower positive state tuple radius=_ at actual
  dsimp only at first
  rw [← actual] at first
  have projected := congrArg (forceMeanFreeTrace (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0) first
  rw [← originalCoreNegativeTrace_meanFree] at projected
  have euler := originalKernelXi_euler parameters.length physicalState vector scalar homogeneous
  rw [sameBase] at euler
  rw [← euler,← sameBase] at projected
  have coefficients := congrArg (fun trace => negativeTraceCoefficient
    (radialKernelParameters parameters (tupleRadius lower positive radius)) 0 0 trace mode) projected
  rw [forceMeanFreeTrace,angularMeanFreeKernel,scalarModeDiagonalKernel_action_coefficient,negativeTraceCoefficient_smul,
    originalCurveNegativeTrace_coefficient _ bounded radius,
    ← originalPhysicalCoefficient_eq_double _
      (originalWeightedPhysicalSmooth_of_lowCurves (originalCoreLowCurves parameters lower positive bounded (eulerCore parameters xi)) bounded).1 radius.val radius.property mode] at coefficients
  have radial := (originalCoreCoefficient_hasDerivWithinAt parameters lower positive bounded xi radius mode).derivWithin
    ((uniqueDiffOn_Icc bounded).uniqueDiffWithinAt radius.property)
  change derivWithin (fun location => originalPhysicalCoefficient
      ((originalCoreLowCurves parameters lower positive bounded xi).fullField bounded) location mode) (Icc lower 1) radius.val-
    angularMeanFreeMultiplier mode • negativeTraceCoefficient _ 0 0
      (tupleFirstRowTrace parameters parameters.length compact lower positive state tuple radius) mode=0
  rw [radial,← coefficients]
  have nonzeroRadius : (radius.val : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (positive.trans_le radius.property.1).ne'
  rw [smul_comm (angularMeanFreeMultiplier mode) (radius.val : ℂ),inv_smul_smul₀ nonzeroRadius,sub_self]

end Grad.OriginalKernelHomogeneousGraph
