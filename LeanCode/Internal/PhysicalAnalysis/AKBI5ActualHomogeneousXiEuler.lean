import AKBI4OriginalCartesianProductRule

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.QuotientProjection Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery

theorem originalEuler_rotation {parameters : PhaseParameters} {dimension : ℕ} (field : ACore parameters dimension) :
    eulerCore parameters (rotationCore parameters field)=rotationCore parameters (eulerCore parameters field) := by
  simp [eulerCore,rotationCore,partialCore_coordinateCore,map_add,map_sub,
    coordinateCore_commute 1 0,partialCore_commute 1 0]
  abel

theorem originalEuler_removeAngular {parameters : PhaseParameters} {dimension : ℕ} (field : ACore parameters dimension) :
    eulerCore parameters (removeAngularCore parameters field)=removeAngularCore parameters (eulerCore parameters field) := by
  change eulerCore parameters (field-angularCore parameters 0 field)=_
  rw [map_sub,← angularCore_eulerCore]
  rfl

/-- Exact retained scalar radial numerator of the SAME original homogeneous
field. It follows from the actual projected radial force, not a graph equation. -/
theorem originalKernelXi_euler {parameters : PhaseParameters} (length : ℝ)
    (state : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)]=0) :
    eulerCore parameters (originalKernelXi state.2.1 vector scalar)=
      removeAngularCore parameters
        (dotOperation parameters (eulerCore parameters state.2.1) (rotationCore parameters vector)-
          dotOperation parameters (rotationCore parameters (eulerCore parameters state.2.1)) vector) := by
  have original := originalHomogeneous_eulerForce length state vector scalar homogeneous
  rw [map_sub,map_sub] at original
  have solved := sub_eq_iff_eq_add.mp (sub_eq_zero.mp original)
  rw [originalKernelXi,originalEuler_removeAngular,map_sub,originalDot_euler,originalEuler_rotation,
    map_sub,map_add,solved,originalDot_comm (rotationCore parameters state.2.1) (eulerCore parameters vector),map_sub]
  abel

end Grad.OriginalKernelHomogeneousGraph
