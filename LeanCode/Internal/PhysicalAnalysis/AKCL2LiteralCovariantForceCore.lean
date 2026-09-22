import AKCL1SourcedOriginalForceContractions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.FinitePhysicalJetLift Grad.AxisSplit Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery
open Grad.OriginalKernelHomogeneousGraph

 def originalPlanarCovariantComponent {parameters : PhaseParameters} (direction : Fin 2)
    (field vector : ACore parameters 3) : ACore parameters 1 :=
  dotOperation parameters (partialCore parameters direction field) vector

 def originalQuarterCovariantComponent {parameters : PhaseParameters} (direction : Fin 2)
    (field vector : ACore parameters 3) : ACore parameters 1 :=
  if direction=0 then -originalPlanarCovariantComponent 1 field vector else originalPlanarCovariantComponent 0 field vector

/-- Literal grad Xi - R a - J a + 2(R F)^T U in the original core. -/
def originalCovariantForceComponent {parameters : PhaseParameters} (direction : Fin 2)
    (field vector : ACore parameters 3) (scalar : ACore parameters 1) : ACore parameters 1 :=
  partialCore parameters direction (originalKernelXi field vector scalar)-
    rotationCore parameters (originalPlanarCovariantComponent direction field vector)-
    originalQuarterCovariantComponent direction field vector+
    (2 : ℂ) • dotOperation parameters (rotationCore parameters (partialCore parameters direction field)) vector

 theorem originalPartial_rotation_zero {parameters : PhaseParameters} {dimension : ℕ} (field : ACore parameters dimension) :
    partialCore parameters 0 (rotationCore parameters field)=
      rotationCore parameters (partialCore parameters 0 field)+partialCore parameters 1 field := by
  simp [rotationCore,partialCore_coordinateCore,map_sub,partialCore_commute 0 1]
  abel

 theorem originalPartial_rotation_one {parameters : PhaseParameters} {dimension : ℕ} (field : ACore parameters dimension) :
    partialCore parameters 1 (rotationCore parameters field)=
      rotationCore parameters (partialCore parameters 1 field)-partialCore parameters 0 field := by
  simp [rotationCore,partialCore_coordinateCore,map_sub,partialCore_commute 0 1]
  abel

 theorem originalCovariantForceComponent_expand {parameters : PhaseParameters} (direction : Fin 2)
    (field vector : ACore parameters 3) (scalar : ACore parameters 1) :
    originalCovariantForceComponent direction field vector scalar=
      partialCore parameters direction (originalKernelXi field vector scalar)+
        dotOperation parameters (partialCore parameters direction (rotationCore parameters field)) vector-
        dotOperation parameters (partialCore parameters direction field) (rotationCore parameters vector) := by
  fin_cases direction
  · change originalCovariantForceComponent 0 field vector scalar=
      partialCore parameters 0 (originalKernelXi field vector scalar)+
        dotOperation parameters (partialCore parameters 0 (rotationCore parameters field)) vector-
        dotOperation parameters (partialCore parameters 0 field) (rotationCore parameters vector)
    simp only [originalCovariantForceComponent,originalQuarterCovariantComponent,
      originalPartial_rotation_zero,map_add,originalPlanarCovariantComponent,originalDot_rotation]
    simp only [if_true,LinearMap.add_apply]
    module
  · change originalCovariantForceComponent 1 field vector scalar=
      partialCore parameters 1 (originalKernelXi field vector scalar)+
        dotOperation parameters (partialCore parameters 1 (rotationCore parameters field)) vector-
        dotOperation parameters (partialCore parameters 1 field) (rotationCore parameters vector)
    simp only [originalCovariantForceComponent,originalQuarterCovariantComponent,if_neg (by decide : (1 : Fin 2)≠0),
      originalPartial_rotation_one,map_sub,originalPlanarCovariantComponent,originalDot_rotation]
    simp only [LinearMap.sub_apply]
    module

/-- All original correction terms are explicit before Qrad is applied. -/
theorem physicalForce_covariant_exact {parameters : PhaseParameters} (direction : Fin 2)
    (field vector : ACore parameters 3) (scalar : ACore parameters 1) :
    physicalCartesianForceComponent direction field vector scalar=
      originalCovariantForceComponent direction field vector scalar+
        partialCore parameters direction (angularCore parameters 0
          (scalar-dotOperation parameters (rotationCore parameters field) vector))+
        coordinateCore parameters direction (physicalVariationRadialCorrection field vector) := by
  rw [originalCovariantForceComponent_expand,originalKernelXi]
  change physicalCartesianForceComponent direction field vector scalar=
    partialCore parameters direction ((scalar-dotOperation parameters (rotationCore parameters field) vector)-
      angularCore parameters 0 (scalar-dotOperation parameters (rotationCore parameters field) vector))+
      dotOperation parameters (partialCore parameters direction (rotationCore parameters field)) vector-
      dotOperation parameters (partialCore parameters direction field) (rotationCore parameters vector)+
      partialCore parameters direction (angularCore parameters 0 (scalar-dotOperation parameters (rotationCore parameters field) vector))+
      coordinateCore parameters direction (physicalVariationRadialCorrection field vector)
  rw [physicalCartesianForceComponent,map_sub,map_sub,originalDot_partial,
    originalDot_comm (partialCore parameters direction vector) (rotationCore parameters field)]
  abel

 theorem originalCovariantForce_euler {parameters : PhaseParameters}
    (field vector : ACore parameters 3) (scalar : ACore parameters 1) :
    coordinateCore parameters 0 (originalCovariantForceComponent 0 field vector scalar)+
      coordinateCore parameters 1 (originalCovariantForceComponent 1 field vector scalar)=
    eulerCore parameters (originalKernelXi field vector scalar)+
      dotOperation parameters (rotationCore parameters (eulerCore parameters field)) vector-
      dotOperation parameters (eulerCore parameters field) (rotationCore parameters vector) := by
  rw [← originalEuler_rotation]
  simp only [originalCovariantForceComponent_expand,eulerCore,LinearMap.add_apply,LinearMap.comp_apply,
    map_add,map_sub,dot_coordinate_first]
  abel

 theorem originalCovariantForce_angular {parameters : PhaseParameters}
    (field vector : ACore parameters 3) (scalar : ACore parameters 1) :
    coordinateCore parameters 0 (originalCovariantForceComponent 1 field vector scalar)-
      coordinateCore parameters 1 (originalCovariantForceComponent 0 field vector scalar)=
    rotationCore parameters (originalKernelXi field vector scalar)+
      dotOperation parameters (rotationCore parameters (rotationCore parameters field)) vector-
      dotOperation parameters (rotationCore parameters field) (rotationCore parameters vector) := by
  simp only [originalCovariantForceComponent_expand,rotationCore,LinearMap.sub_apply,LinearMap.comp_apply,
    map_add,map_sub,dot_coordinate_first]
  abel

end Grad.OriginalCoreRealization
