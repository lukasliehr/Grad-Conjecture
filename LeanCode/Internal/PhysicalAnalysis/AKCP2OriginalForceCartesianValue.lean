import AKCP1LiteralFullFrameForceValue
import AKCJ9SameCoreCartesianFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianEquations Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalKernelHomogeneousGraph Grad.Constraints Grad.SourceCollar Grad.FinitePhysicalJetLift
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualCartesianDescent Grad.PhysicalFamily Grad.BoundaryTrace

/-- The literal original covariant force has the genuine Cartesian differential
expression at the same physical point, with the complete rotated frame value. -/
theorem originalForce_cartesianValue (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) (scalar : ACore parameters 1)
    (radius : ℝ) (positive : 0<radius) (interior : radius<1) (angles : ℝ×ℝ) :
    originalPairCircle (originalCovariantForceComponent 0 (planarReferenceCore parameters+base) vector scalar)
      (originalCovariantForceComponent 1 (planarReferenceCore parameters+base) vector scalar)
      radius positive.le interior.le angles=
    cartesianForceValue
      (planarGradientValue (fderiv ℝ (originalCoreProductLift parameters
        (originalKernelXi (planarReferenceCore parameters+base) vector scalar)) (polarPlane (radius,angles.1),angles.2)))
      (fderiv ℝ (originalCoreProductLift parameters (originalCovariantCore parameters length epsilon base vector false))
        (polarPlane (radius,angles.1),angles.2) (radius • planeQuarterTurn (radialDirection angles.1),0))
      (coreValue (originalCovariantCore parameters length epsilon base vector false)
        (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 positive.le interior.le) angles.2)
      ((2 : ℂ) • coreValue (originalCovariantCore parameters length epsilon base vector true)
        (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 positive.le interior.le) angles.2) := by
  have normInside : ‖polarPlane (radius,angles.1)‖<1 := by
    simpa only [polarPlane_norm,abs_of_pos positive] using interior
  have quarter : planeQuarterTurn (polarPlane (radius,angles.1))=radius • planeQuarterTurn (radialDirection angles.1) := by
    ext coordinate
    fin_cases coordinate <;> simp [polarPlane,collarPlane,radialDirection,planeQuarterTurn]
  have rotation := originalCoreProductLift_rotation parameters
    (originalCovariantCore parameters length epsilon base vector false) (polarPlane (radius,angles.1),angles.2) normInside
  rw [quarter] at rotation
  rw [← rotation]
  have derivativeValue (direction : Fin 2) := originalCoreProductLift_partial parameters
    (originalKernelXi (planarReferenceCore parameters+base) vector scalar) (polarPlane (radius,angles.1),angles.2) normInside direction
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change coreValue (originalCovariantForceComponent 0 (planarReferenceCore parameters+base) vector scalar) _ _ 0=_
    rw [originalCovariantForce_component_value parameters length epsilon]
    simp only [cartesianForceValue,Grad.ActualCartesianEquations.planarPart,planarGradientValue,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,
      smul_eq_mul,Matrix.cons_val_zero,derivativeValue]
    rfl
  · change coreValue (originalCovariantForceComponent 1 (planarReferenceCore parameters+base) vector scalar) _ _ 0=_
    rw [originalCovariantForce_component_value parameters length epsilon]
    simp only [cartesianForceValue,Grad.ActualCartesianEquations.planarPart,planarGradientValue,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,
      smul_eq_mul,Matrix.cons_val_one,derivativeValue]
    rfl
  · rfl

end Grad.OriginalCoreRealization
