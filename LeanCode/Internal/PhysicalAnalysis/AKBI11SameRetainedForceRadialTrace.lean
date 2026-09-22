import AKBI10SameOriginalRetainedForceValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelGraphRestriction
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField Grad.SourceCollarFullSource
open Grad.BoundaryKernelAction Grad.ActualPolarEquations Grad.FinitePhysicalJetLift Grad.ActualPolarFlux
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact : ℝ) (nonzero : length≠0)
    (state : RetainedInverseState parameters length compact)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3) (radius : Icc lower (1 : ℝ))

include nonzero

theorem originalRetainedForce_scaledTrace :
    let curves := originalPolarCovariantCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
      lower positive bounded vector
    (radius.val : ℂ) • fullNegativeKernelAction _ 0 0
      (radialRetainedForceKernel parameters length compact state.val.val (tupleRadius lower positive radius))
      (originalCurveNegativeTrace curves radius)=
    (2 : ℂ) • originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded
      (dotOperation parameters (rotationCore parameters (eulerCore parameters (planarReferenceCore parameters+state.val.val.field))) vector)) radius := by
  let curves := originalPolarCovariantCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
    lower positive bounded vector
  let target := originalCoreLowCurves parameters lower positive bounded
    (dotOperation parameters (rotationCore parameters (eulerCore parameters (planarReferenceCore parameters+state.val.val.field))) vector)
  have scaled := originalScalarTrace_scale (curves.retainedForce parameters length compact lower positive bounded state) (target.smul 2)
    bounded (radius.val : ℂ) radius (by
      intro angles
      rw [samePhysical_fullField_smul target bounded 2 radius.val radius.property angles,
        originalCoreLowCurves_fullField parameters lower positive bounded _ radius.val radius.property angles]
      exact originalRetainedForce_scaledValue parameters length compact nonzero state lower positive bounded vector radius angles)
  rw [originalCurveNegativeTrace_smul] at scaled
  have action := originalCurveNegativeTrace_action parameters lower positive bounded
    (radialRetainedForceKernel parameters length compact state.val.val)
    (radialRetainedForceKernel_regular parameters length compact state.val)
    (Grad.AnnularWeightedSmoothness.actualRetainedForce_conjugated_smooth parameters length compact state lower positive bounded) curves radius
  exact (congrArg ((radius.val : ℂ) • ·) action).symm.trans scaled

/-- Exact original retained j numerator, derived from the literal F and RF
contractions and genuine angular differentiation of the same a. -/
theorem originalFirstTrace_scaledEuler :
    let curves := originalPolarCovariantCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
      lower positive bounded vector
    (radius.val : ℂ) • (forceCoordinateTrace _ 0 0 0 (originalCurveNegativeRotation curves radius)-
      fullNegativeKernelAction _ 0 0
        (radialRetainedForceKernel parameters length compact state.val.val (tupleRadius lower positive radius))
        (originalCurveNegativeTrace curves radius))=
    originalCurveNegativeTrace (originalCoreLowCurves parameters lower positive bounded
      (dotOperation parameters (eulerCore parameters (planarReferenceCore parameters+state.val.val.field)) (rotationCore parameters vector)-
        dotOperation parameters (rotationCore parameters (eulerCore parameters (planarReferenceCore parameters+state.val.val.field))) vector)) radius := by
  dsimp only
  rw [smul_sub,
    originalActualRotatedRadialTrace_euler parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
      lower positive bounded vector radius,
    originalRetainedForce_scaledTrace parameters length compact nonzero state lower positive bounded vector radius,
    originalDot_rotation,originalCoreNegativeTrace_add,originalCoreNegativeTrace_sub]
  module

end Grad.OriginalKernelHomogeneousGraph
