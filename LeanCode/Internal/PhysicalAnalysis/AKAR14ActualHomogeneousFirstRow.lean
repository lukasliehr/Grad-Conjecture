import AKAR10SixCoefficientNorms
import AKU31LiteralCartesianForwardForce
import AKU37QuadraticLiftRadialCorrection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.FinitePhysicalJetLift

theorem coordinateCore_commute {parameters : PhaseParameters} {dimension : ℕ}
    (first second : Fin 2) (field : ACore parameters dimension) :
    coordinateCore parameters first (coordinateCore parameters second field) =
      coordinateCore parameters second (coordinateCore parameters first field) := by
  apply coreValue_ext
  intro point angle
  rw [coreValue_coordinate,coreValue_coordinate,coreValue_coordinate,coreValue_coordinate]
  exact smul_comm _ _ _

theorem originalDot_comm {parameters : PhaseParameters} (first second : ACore parameters 3) :
    dotOperation parameters first second = dotOperation parameters second first := by
  apply coreValue_ext
  intro point angle
  apply PiLp.ext
  intro index
  have only : index=0 := Subsingleton.elim _ _
  subst index
  rw [coreValue_dotOperation,coreValue_dotOperation]
  simp only [Grad.NonlinearQuotient.complexDot,mul_comm]

/-- The original radial correction cancels under contraction with Jy. -/
theorem physicalCartesianForce_angular {parameters : PhaseParameters}
    (base vector : ACore parameters 3) (scalar : ACore parameters 1) :
    coordinateCore parameters 0 (physicalCartesianForceComponent 1 base vector scalar) -
      coordinateCore parameters 1 (physicalCartesianForceComponent 0 base vector scalar) =
      rotationCore parameters scalar - (2 : ℂ) •
        dotOperation parameters (rotationCore parameters base) (rotationCore parameters vector) := by
  have raw : coordinateCore parameters 0 (physicalCartesianForceComponent 1 base vector scalar) -
      coordinateCore parameters 1 (physicalCartesianForceComponent 0 base vector scalar) =
      rotationCore parameters scalar -
        dotOperation parameters (rotationCore parameters vector) (rotationCore parameters base) -
        dotOperation parameters (rotationCore parameters base) (rotationCore parameters vector) := by
    simp only [physicalCartesianForceComponent,rotationCore,LinearMap.comp_apply,LinearMap.sub_apply,
      map_add,map_sub,dot_coordinate_first,dot_coordinate_second]
    simp only [coordinateCore_commute 1 0]
    abel
  rw [raw,originalDot_comm (rotationCore parameters vector) (rotationCore parameters base)]
  module

/-- The actual original quotient derivative vanishes, hence its true angular
first row is RS=2 Rv·RU. No retained equation is an input. -/
theorem originalHomogeneous_first_row (parameters : PhaseParameters) (length : ℝ)
    (base : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 base ![(0,vector,scalar)] = 0) :
    rotationCore parameters scalar = (2 : ℂ) •
      dotOperation parameters (rotationCore parameters base.2.1) (rotationCore parameters vector) := by
  have first : physicalCartesianForceComponent 0 base.2.1 vector scalar = 0 := by
    rw [← physicalEtaZeroRows_cartesian_first parameters length base vector scalar,
      ← quotientRowsDerivative_etaZero parameters length base vector scalar,homogeneous]
    simp [cartesianSpinFirst]
  have second : physicalCartesianForceComponent 1 base.2.1 vector scalar = 0 := by
    rw [← physicalEtaZeroRows_cartesian_second parameters length base vector scalar,
      ← quotientRowsDerivative_etaZero parameters length base vector scalar,homogeneous]
    simp [cartesianSpinSecond]
  have actual := physicalCartesianForce_angular base.2.1 vector scalar
  rw [first,second,map_zero,map_zero,sub_self] at actual
  exact sub_eq_zero.mp actual.symm

end Grad.OriginalKernelRetainedDecay
