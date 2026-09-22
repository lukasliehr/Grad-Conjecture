import AKCL4ActualOriginalQradForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianEquations Grad.ActualDeterminantEquations Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalKernelHomogeneousGraph Grad.Constraints Grad.SourceCollar Grad.FinitePhysicalJetLift
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

 theorem originalCovariantCore_planarComponent (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) (rotated : Bool) (direction : Fin 2) :
    valueMapCore parameters (matrixUnit (0 : Fin 1) (⟨direction.val,by omega⟩ : Fin 3))
      (originalCovariantCore parameters length epsilon base vector rotated)=
    dotOperation parameters (if rotated then rotationCore parameters (partialCore parameters direction (planarReferenceCore parameters+base))
      else partialCore parameters direction (planarReferenceCore parameters+base)) vector := by
  fin_cases direction
  all_goals rw [originalCovariantCore,originalScalarTripletCore_coordinate]
  all_goals simp only [originalFrameColumnCore]
  all_goals rfl

 theorem originalCovariantForce_component_value (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) (scalar : ACore parameters 1) (direction : Fin 2)
    (point : ClosedDisk) (axial : ℝ) :
    coreValue (originalCovariantForceComponent direction (planarReferenceCore parameters+base) vector scalar) point axial 0=
      coreValue (partialCore parameters direction (originalKernelXi (planarReferenceCore parameters+base) vector scalar)) point axial 0-
      coreValue (rotationCore parameters (originalCovariantCore parameters length epsilon base vector false)) point axial ⟨direction.val,by omega⟩-
      polarQuarter (coreValue (originalCovariantCore parameters length epsilon base vector false) point axial) ⟨direction.val,by omega⟩+
      2 * coreValue (originalCovariantCore parameters length epsilon base vector true) point axial ⟨direction.val,by omega⟩ := by
  have component (rotated : Bool) (direction : Fin 2) := originalCovariantCore_planarComponent parameters length epsilon base vector rotated direction
  have rotated (direction : Fin 2) := congrArg (rotationCore parameters) (component false direction)
  simp_rw [originalRotation_valueMap] at rotated
  simp only [Bool.false_eq_true,if_false] at rotated
  have rotationValue (direction : Fin 2) := congrArg (fun core : ACore parameters 1 => coreValue core point axial 0) (rotated direction)
  simp only [coreValue_valueMap,matrixUnit_apply,operatorBasis,PiLp.smul_apply,smul_eq_mul,ite_true,mul_one] at rotationValue
  have values (rotated : Bool) (direction : Fin 2) := congrArg (fun core : ACore parameters 1 => coreValue core point axial 0) (component rotated direction)
  simp only [coreValue_valueMap,matrixUnit_apply,operatorBasis,PiLp.smul_apply,smul_eq_mul,ite_true,mul_one] at values
  rw [originalCovariantForceComponent,coreValue_add,coreValue_subtract,coreValue_subtract,coreValue_smul]
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  rw [originalPlanarCovariantComponent,← rotationValue direction]
  have trueValue := values true direction
  simp only [if_true] at trueValue
  rw [← trueValue]
  congr 2
  fin_cases direction
  · change coreValue (originalQuarterCovariantComponent 0 (planarReferenceCore parameters+base) vector) point axial 0=_
    simp only [originalQuarterCovariantComponent,Fin.zero_eta,Fin.isValue,ite_true,originalPlanarCovariantComponent]
    rw [show -dotOperation parameters (partialCore parameters 1 (planarReferenceCore parameters+base)) vector=
      (-1 : ℂ) • dotOperation parameters (partialCore parameters 1 (planarReferenceCore parameters+base)) vector by module,coreValue_smul]
    have value := values false 1
    simp only [Bool.false_eq_true,if_false] at value
    simp only [PiLp.smul_apply,smul_eq_mul]
    rw [← value]
    simp [polarQuarter]
  · change coreValue (originalQuarterCovariantComponent 1 (planarReferenceCore parameters+base) vector) point axial 0=_
    simp only [originalQuarterCovariantComponent,show (1 : Fin 2)≠0 by decide,if_false,originalPlanarCovariantComponent]
    have value := values false 0
    simp only [Bool.false_eq_true,if_false] at value
    rw [← value]
    simp [polarQuarter]

end Grad.OriginalCoreRealization
