import AKBI9SameActualRadialCovariantTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set
open scoped BigOperators
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelGraphRestriction
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField Grad.SourceCollarFullSource
open Grad.BoundaryKernelAction Grad.ActualPolarEquations Grad.FinitePhysicalJetLift
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ActualPolarFlux Grad.ActualCartesianEquations Grad.SourceCollar Grad.ActualCurrentPrimitives

variable (parameters : PhaseParameters) (length compact : ℝ) (nonzero : length≠0)
    (state : RetainedInverseState parameters length compact)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)
    (radius : Icc lower (1 : ℝ)) (angles : ℝ×ℝ)

include nonzero

theorem originalRetainedForce_scaledValue :
    let curves := originalPolarCovariantCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
      lower positive bounded vector
    (radius.val : ℂ) • (curves.retainedForce parameters length compact lower positive bounded state).fullField bounded (radius.val,angles)=
      (2 : ℂ) • originalCoreCircle parameters
        (dotOperation parameters (rotationCore parameters (eulerCore parameters (planarReferenceCore parameters+state.val.val.field))) vector)
        (tupleRadius lower positive radius) angles := by
  let curves := originalPolarCovariantCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
    lower positive bounded vector
  let r := tupleRadius lower positive radius
  let rotated := WithLp.toLp 2 ((rotatedPhysicalFrameMatrix parameters 1 1 state.val.val.epsilon state.val.val.field angles.2
    (Grad.SourceCollarDivision.polarClosedPoint radius.val angles.1 (positive.le.trans radius.property.1) radius.property.2)*
      Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose.mulVec (originalCoreCircle parameters vector r angles))
  have force : (curves.retainedForce parameters length compact lower positive bounded state).fullField bounded (radius.val,angles)=
      (2 : ℂ) • matrixUnit (0 : Fin 1) (1 : Fin 3) (curves.fullField bounded (radius.val,angles))+
        (2 : ℂ) • originalPolarRadialValue rotated angles.1 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate
    change (curves.retainedForce parameters length compact lower positive bounded state).fullField bounded (radius.val,angles) 0 =
      ((2 : ℂ) • matrixUnit (0 : Fin 1) (1 : Fin 3) (curves.fullField bounded (radius.val,angles))+
        (2 : ℂ) • originalPolarRadialValue rotated angles.1) 0
    rw [fullField_originalRetainedForce parameters length compact lower positive bounded state curves radius.val radius.property angles,
      originalRetainedForce_sameU parameters length compact lower positive bounded state.val curves radius.val radius.property angles,
      originalPolarCovariantCurves_recovers_U parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
        lower positive bounded vector radius.val radius.property angles]
    simp [rotated,r,tupleRadius,originalPolarRadialValue,matrixUnit_apply,operatorBasis,matrixPairing,physicalRadialVector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three]
    ring
  calc
    _ = (2 : ℂ) • ((radius.val : ℂ) • matrixUnit (0 : Fin 1) (1 : Fin 3) (curves.fullField bounded (radius.val,angles))+
        (radius.val : ℂ) • originalPolarRadialValue rotated angles.1) := by rw [force]; module
    _ = (2 : ℂ) • (originalCoreCircle parameters
        (dotOperation parameters (rotationCore parameters (planarReferenceCore parameters+state.val.val.field)) vector) r angles+
      originalCoreCircle parameters (dotOperation parameters
        (rotationCore parameters (eulerCore parameters (planarReferenceCore parameters+state.val.val.field))-
          rotationCore parameters (planarReferenceCore parameters+state.val.val.field)) vector) r angles) := by
      rw [originalPolarCovariantCurves_fullField parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
        lower positive bounded vector radius.val radius.property angles,originalPolarCovariantValue_tangential]
      apply congrArg ((2 : ℂ) • ·)
      exact congrArg₂ (·+·)
        (originalTangentialFrame_dot parameters length state.val.val.epsilon state.val.val.field vector r angles)
        (originalRotatedRadialFrame_dot parameters length state.val.val.epsilon nonzero state.val.val.field vector r angles)
    _ = _ := by
      simp only [map_sub,LinearMap.sub_apply,originalCoreCircle,coreValue_subtract,r,tupleRadius]
      module

end Grad.OriginalKernelHomogeneousGraph
