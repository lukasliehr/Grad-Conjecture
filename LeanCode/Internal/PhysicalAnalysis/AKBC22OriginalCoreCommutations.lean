import AKBC21OriginalAxialProductRule
import AKU49ActualAxialCorrectionOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.FinitePhysicalJetLift Grad.AxisSplit Grad.OriginalKernelRetainedDecay
open Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem originalTime_partial {parameters : PhaseParameters} {dimension : ℕ}
    (direction : Fin 2) (field : ACore parameters dimension) :
    timeDerivativeCore parameters (partialCore parameters direction field)=
      partialCore parameters direction (timeDerivativeCore parameters field) := by
  apply acore_ext
  intro cell point
  rw [timeDerivativeCore_val,partialCore_val,partialCore_val,timeDerivativeCore_val]
  change ((cell : ℂ)*Complex.I) • closedDerivative (field.val cell) 1 (fun _ => direction) point =
    closedDerivative (((cell : ℂ)*Complex.I) • field.val cell) 1 (fun _ => direction) point
  exact (congrArg (fun value : C(ClosedDisk,ComplexEuclidean dimension) => value point)
    ((closedDerivativeLinear 1 (fun _ => direction)).map_smul ((cell : ℂ)*Complex.I) (field.val cell))).symm

theorem originalTime_rotation {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) :
    timeDerivativeCore parameters (rotationCore parameters field)=
      rotationCore parameters (timeDerivativeCore parameters field) := by
  simp only [rotationCore,LinearMap.sub_apply,LinearMap.comp_apply,map_sub,
    timeDerivativeCore_coordinate,originalTime_partial]

theorem originalRotation_valueMap {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : ACore parameters input) :
    rotationCore parameters (valueMapCore parameters mapping field)=
      valueMapCore parameters mapping (rotationCore parameters field) := by
  apply Subtype.ext
  funext cell
  exact rotationJet_valueMap mapping (field.val cell)

theorem originalTime_angular {parameters : PhaseParameters} {dimension : ℕ}
    (mode : ℤ) (field : ACore parameters dimension) :
    timeDerivativeCore parameters (angularCore parameters mode field)=
      angularCore parameters mode (timeDerivativeCore parameters field) := by
  apply Subtype.ext
  funext cell
  exact (angularClosedJet_smul mode ((cell : ℂ)*Complex.I) (field.val cell)).symm

theorem originalTime_removeAngular {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) :
    timeDerivativeCore parameters (removeAngularCore parameters field)=
      removeAngularCore parameters (timeDerivativeCore parameters field) := by
  change timeDerivativeCore parameters (field-angularCore parameters 0 field)=_
  rw [map_sub,originalTime_angular]
  rfl

theorem originalDot_tangentSkew {parameters : PhaseParameters} (first second : ACore parameters 3) :
    dotOperation parameters (valueMapCore parameters tangentGeneratorMap first) second =
      -dotOperation parameters first (valueMapCore parameters tangentGeneratorMap second) := by
  apply coreValue_ext
  intro point axial
  apply PiLp.ext
  intro coordinate
  have only : coordinate=0 := Subsingleton.elim _ _
  subst coordinate
  rw [show -dotOperation parameters first (valueMapCore parameters tangentGeneratorMap second)=
    (-1 : ℂ) • dotOperation parameters first (valueMapCore parameters tangentGeneratorMap second) by module]
  rw [coreValue_smul]
  change coreValue (dotOperation parameters (valueMapCore parameters tangentGeneratorMap first) second) point axial 0 =
    (-1 : ℂ)*coreValue (dotOperation parameters first (valueMapCore parameters tangentGeneratorMap second)) point axial 0
  rw [coreValue_dotOperation,coreValue_dotOperation,coreValue_valueMap,coreValue_valueMap]
  simp [tangentGeneratorMap_value,Grad.NonlinearQuotient.complexTangentGenerator,
    Grad.NonlinearQuotient.complexDot,Fin.sum_univ_three]

end Grad.OriginalKernelCovariantRecovery
