import AKBI1OriginalRadialCorrectionMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.FlatSourceProjection Grad.AxisSplit
open Grad.NonlinearRange Grad.QuotientProjection Grad.FinitePhysicalJetLift
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery

theorem originalRadiusSquared_coordinates {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) :
    radiusSquaredCore parameters field=coordinateCore parameters 0 (coordinateCore parameters 0 field)+
      coordinateCore parameters 1 (coordinateCore parameters 1 field) := by
  apply acore_ext
  intro cell point
  rw [radiusSquaredCore_value]
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  simp [acore_val_add,coordinateCore_val,coordinateJet_value,pow_two,add_smul,smul_smul]

theorem physicalCartesianForce_euler {parameters : PhaseParameters}
    (field vector : ACore parameters 3) (scalar : ACore parameters 1) :
    coordinateCore parameters 0 (physicalCartesianForceComponent 0 field vector scalar)+
      coordinateCore parameters 1 (physicalCartesianForceComponent 1 field vector scalar)=
    eulerCore parameters scalar-dotOperation parameters (eulerCore parameters vector) (rotationCore parameters field)-
      dotOperation parameters (eulerCore parameters field) (rotationCore parameters vector)+
      radiusSquaredCore parameters (physicalVariationRadialCorrection field vector) := by
  rw [originalRadiusSquared_coordinates]
  simp only [physicalCartesianForceComponent,eulerCore,LinearMap.comp_apply,LinearMap.add_apply,
    map_add,map_sub,dot_coordinate_first]
  abel

theorem originalHomogeneous_forceComponents {parameters : PhaseParameters} (length : ℝ)
    (state : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)]=0) (direction : Fin 2) :
    physicalCartesianForceComponent direction state.2.1 vector scalar=0 := by
  fin_cases direction
  · change physicalCartesianForceComponent 0 state.2.1 vector scalar=0
    rw [← physicalEtaZeroRows_cartesian_first parameters length state vector scalar,
      ← quotientRowsDerivative_etaZero parameters length state vector scalar,homogeneous]
    simp [cartesianSpinFirst]
  · change physicalCartesianForceComponent 1 state.2.1 vector scalar=0
    rw [← physicalEtaZeroRows_cartesian_second parameters length state vector scalar,
      ← quotientRowsDerivative_etaZero parameters length state vector scalar,homogeneous]
    simp [cartesianSpinSecond]

/-- The true projected Euler force follows from the original homogeneous
rows and their actual radial correction, with no annular PDE premise. -/
theorem originalHomogeneous_eulerForce {parameters : PhaseParameters} (length : ℝ)
    (state : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)]=0) :
    removeAngularCore parameters
      (eulerCore parameters scalar-dotOperation parameters (eulerCore parameters vector) (rotationCore parameters state.2.1)-
        dotOperation parameters (eulerCore parameters state.2.1) (rotationCore parameters vector))=0 := by
  have radial := physicalCartesianForce_euler state.2.1 vector scalar
  rw [originalHomogeneous_forceComponents length state vector scalar homogeneous 0,
    originalHomogeneous_forceComponents length state vector scalar homogeneous 1,map_zero,map_zero,add_zero] at radial
  have projected := congrArg (removeAngularCore parameters) radial
  rw [map_zero,map_add,originalVariationRadialCorrection_projected,add_zero] at projected
  exact projected.symm

end Grad.OriginalKernelHomogeneousGraph
