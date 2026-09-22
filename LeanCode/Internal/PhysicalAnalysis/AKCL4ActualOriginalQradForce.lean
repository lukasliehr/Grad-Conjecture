import AKCL3OriginalForcePolarAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianEquations Grad.ActualDeterminantEquations Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.OriginalKernelHomogeneousGraph Grad.Constraints Grad.SourceCollar Grad.FinitePhysicalJetLift

 theorem originalPairCircle_Qrad (parameters : PhaseParameters)
    (first second rawFirst rawSecond : ACore parameters 1)
    (radial : removeAngularCore parameters (coordinateCore parameters 0 rawFirst+coordinateCore parameters 1 rawSecond)=
      coordinateCore parameters 0 first+coordinateCore parameters 1 second)
    (angular : coordinateCore parameters 0 rawSecond-coordinateCore parameters 1 rawFirst=
      coordinateCore parameters 0 second-coordinateCore parameters 1 first)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (radius : ℝ)
    (inside : radius∈Icc lower 1) (angles : ℝ×ℝ) :
    cartesianRadialMeanFree (originalPairCircle rawFirst rawSecond radius (positive.le.trans inside.1) inside.2) angles=
      originalPairCircle first second radius (positive.le.trans inside.1) inside.2 angles := by
  have radiusPositive := positive.trans_le inside.1
  have representation : originalPairCircle rawFirst rawSecond radius (positive.le.trans inside.1) inside.2=
      fun query => cartesianCovariantValue query.1 (WithLp.toLp 2 ![
        (radius : ℂ)⁻¹ * coreValue (coordinateCore parameters 0 rawFirst+coordinateCore parameters 1 rawSecond)
          (Grad.SourceCollarDivision.polarClosedPoint radius query.1 radiusPositive.le inside.2) query.2 0,
        (radius : ℂ)⁻¹ * coreValue (coordinateCore parameters 0 rawSecond-coordinateCore parameters 1 rawFirst)
          (Grad.SourceCollarDivision.polarClosedPoint radius query.1 radiusPositive.le inside.2) query.2 0,0]) :=
    funext (originalPairCircle_polar rawFirst rawSecond radius radiusPositive inside.2)
  rw [representation,cartesianRadialMeanFree_polar,originalPairCircle_polar first second radius radiusPositive inside.2 angles]
  apply congrArg (cartesianCovariantValue angles.1)
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change removePolarMean (fun query => (radius : ℂ)⁻¹ • coreValue
        (coordinateCore parameters 0 rawFirst+coordinateCore parameters 1 rawSecond)
        (Grad.SourceCollarDivision.polarClosedPoint radius query.1 radiusPositive.le inside.2) query.2 0) angles=_
    rw [congrFun (removePolarMean_smul (radius : ℂ)⁻¹ _) angles,
      ← originalCore_removeAngular_polar parameters lower positive bounded _ radius inside angles,radial]
    rfl
  · change (radius : ℂ)⁻¹ * coreValue (coordinateCore parameters 0 rawSecond-coordinateCore parameters 1 rawFirst) _ _ 0=_
    rw [angular]
    rfl
  · rfl

/-- Exact true Qrad (radial mean removal, equivalently id+JTJ) of the literal
covariant force is the full original Cartesian force with its radial correction.
Only the original scalar angular constraint is needed; no source equation or
homogeneous-kernel premise occurs. -/
theorem originalForce_Qrad_covariant (parameters : PhaseParameters)
    (field vector : ACore parameters 3) (scalar : ACore parameters 1)
    (mean : angularCore parameters 0 scalar=0)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (radius : ℝ)
    (inside : radius∈Icc lower 1) (angles : ℝ×ℝ) :
    cartesianRadialMeanFree
      (originalPairCircle (originalCovariantForceComponent 0 field vector scalar)
        (originalCovariantForceComponent 1 field vector scalar) radius (positive.le.trans inside.1) inside.2) angles=
    originalPairCircle (physicalCartesianForceComponent 0 field vector scalar)
      (physicalCartesianForceComponent 1 field vector scalar) radius (positive.le.trans inside.1) inside.2 angles := by
  apply originalPairCircle_Qrad parameters
    (physicalCartesianForceComponent 0 field vector scalar) (physicalCartesianForceComponent 1 field vector scalar)
    (originalCovariantForceComponent 0 field vector scalar) (originalCovariantForceComponent 1 field vector scalar)
    ?_ ?_ lower positive bounded radius inside angles
  · rw [originalCovariantForce_euler]
    have reorder : eulerCore parameters (Grad.OriginalKernelRetainedDecay.originalKernelXi field vector scalar)+
        dotOperation parameters (rotationCore parameters (eulerCore parameters field)) vector-
        dotOperation parameters (eulerCore parameters field) (rotationCore parameters vector)=
      eulerCore parameters (Grad.OriginalKernelRetainedDecay.originalKernelXi field vector scalar)-
        dotOperation parameters (eulerCore parameters field) (rotationCore parameters vector)+
        dotOperation parameters (rotationCore parameters (eulerCore parameters field)) vector := by abel
    rw [reorder,← originalForce_projectedEuler parameters field vector scalar]
    change _-angularCore parameters 0 _=_
    rw [originalForce_radialMeanZero parameters field vector scalar mean,sub_zero]
    rfl
  · rw [originalCovariantForce_angular,originalForce_angularXi]

/-- The actual quotient derivative's two Cartesian source components are
exactly the same projected covariant force. -/
theorem originalQuotientForce_Qrad_covariant (parameters : PhaseParameters) (length : ℝ)
    (state : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (mean : angularCore parameters 0 scalar=0)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (radius : ℝ)
    (inside : radius∈Icc lower 1) (angles : ℝ×ℝ) :
    cartesianRadialMeanFree
      (originalPairCircle (originalCovariantForceComponent 0 state.2.1 vector scalar)
        (originalCovariantForceComponent 1 state.2.1 vector scalar) radius (positive.le.trans inside.1) inside.2) angles=
    originalPairCircle (cartesianSpinFirst (quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)]))
      (cartesianSpinSecond (quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)]))
      radius (positive.le.trans inside.1) inside.2 angles := by
  rw [quotientRowsDerivative_etaZero,physicalEtaZeroRows_cartesian_first,physicalEtaZeroRows_cartesian_second]
  exact originalForce_Qrad_covariant parameters state.2.1 vector scalar mean lower positive bounded radius inside angles

end Grad.OriginalCoreRealization
