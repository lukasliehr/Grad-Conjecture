import AKCH8ActualOriginalDeterminantForward
import AKBI5ActualHomogeneousXiEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.FinitePhysicalJetLift Grad.AxisSplit Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery
open Grad.OriginalKernelHomogeneousGraph

/-- Exact sourced projected radial contraction; the original correction is
cancelled using its checked radius-squared mean identity. -/
theorem originalForce_projectedEuler (parameters : PhaseParameters)
    (field vector : ACore parameters 3) (scalar : ACore parameters 1) :
    removeAngularCore parameters
      (coordinateCore parameters 0 (physicalCartesianForceComponent 0 field vector scalar)+
        coordinateCore parameters 1 (physicalCartesianForceComponent 1 field vector scalar))=
    removeAngularCore parameters (eulerCore parameters (originalKernelXi field vector scalar)-
      dotOperation parameters (eulerCore parameters field) (rotationCore parameters vector)+
      dotOperation parameters (rotationCore parameters (eulerCore parameters field)) vector) := by
  rw [physicalCartesianForce_euler,map_add,originalVariationRadialCorrection_projected,add_zero]
  rw [originalKernelXi,originalEuler_removeAngular]
  simp only [map_sub,originalDot_euler,originalEuler_rotation,map_add]
  have idempotent (core : ACore parameters 1) : removeAngularCore parameters (removeAngularCore parameters core)=removeAngularCore parameters core := by
    simp [removeAngularCore,angularCore_projection]
  simp only [idempotent]
  rw [originalDot_comm (eulerCore parameters vector) (rotationCore parameters field)]
  abel

/-- The angular force is the exact retained Xi angular contraction for any
source, without imposing the homogeneous kernel equation. -/
theorem originalForce_angularXi (parameters : PhaseParameters)
    (field vector : ACore parameters 3) (scalar : ACore parameters 1) :
    coordinateCore parameters 0 (physicalCartesianForceComponent 1 field vector scalar)-
      coordinateCore parameters 1 (physicalCartesianForceComponent 0 field vector scalar)=
    rotationCore parameters (originalKernelXi field vector scalar)+
      dotOperation parameters (rotationCore parameters (rotationCore parameters field)) vector-
      dotOperation parameters (rotationCore parameters field) (rotationCore parameters vector) := by
  rw [physicalCartesianForce_angular,originalKernelXi,rotationCore_removeAngular,map_sub,originalDot_rotation]
  module

/-- The actual original force has zero radial mean whenever the actual
original scalar does. The radial correction is retained in this identity. -/
theorem originalForce_radialMeanZero (parameters : PhaseParameters)
    (field vector : ACore parameters 3) (scalar : ACore parameters 1)
    (mean : angularCore parameters 0 scalar=0) :
    angularCore parameters 0
      (coordinateCore parameters 0 (physicalCartesianForceComponent 0 field vector scalar)+
        coordinateCore parameters 1 (physicalCartesianForceComponent 1 field vector scalar))=0 := by
  rw [physicalCartesianForce_euler,originalVariationRadialCorrection_mean]
  simp only [map_add,map_sub,angularCore_projection,ite_true]
  rw [angularCore_eulerCore,mean,map_zero]
  abel

end Grad.OriginalCoreRealization
