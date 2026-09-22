import AKAY33RoughAngularMapAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Compensated

theorem startupPointKernel_neg {input output : ℕ} (mapping : OperatorValue input output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    startupPointKernel (-mapping) orthogonal = -startupPointKernel mapping orthogonal := by
  apply ContinuousLinearMap.ext
  intro field
  apply startupField_ae_ext
  filter_upwards [startupPointKernel_field_ae (-mapping) orthogonal field,
    startupPointKernel_field_ae mapping orthogonal field,
    Lp.coeFn_neg (startupPointKernel mapping orthogonal field)] with point first second negative
  intro cell
  change (startupPointKernel (-mapping) orthogonal field) point cell = (-startupPointKernel mapping orthogonal field) point cell
  rw [first cell, negative]
  simp only [neg_apply, lp.coeFn_neg, Pi.neg_apply, second cell]

theorem startupAverage_quarter (field : StartupL2 2) :
    originalAverageKernel (originalValueKernel quarterValueMap field) =
      originalValueKernel quarterValueMap (originalAverageKernel field) := by
  have positive := startupAngularKernel_value_commute quarterValueMap (angularCharacter 1) (angularCharacter_smooth 1)
  have negative := startupAngularKernel_value_commute quarterValueMap (angularCharacter (-1)) (angularCharacter_smooth (-1))
  have positiveMaps : (originalValueKernel positiveHelicity).comp (originalValueKernel quarterValueMap) =
      (originalValueKernel quarterValueMap).comp (originalValueKernel positiveHelicity) := by
    rw [originalValueKernel_comp, originalValueKernel_comp, quarter_positive_commute]
  have negativeMaps : (originalValueKernel negativeHelicity).comp (originalValueKernel quarterValueMap) =
      (originalValueKernel quarterValueMap).comp (originalValueKernel negativeHelicity) := by
    rw [originalValueKernel_comp, originalValueKernel_comp, quarter_negative_commute]
  have positiveField := congrArg (fun operator : StartupL2 2 →L[ℂ] StartupL2 2 => operator field) positive
  have negativeField := congrArg (fun operator : StartupL2 2 →L[ℂ] StartupL2 2 => operator field) negative
  change startupCharacterKernel 2 1 (originalValueKernel quarterValueMap field) = _ at positiveField
  change startupCharacterKernel 2 (-1) (originalValueKernel quarterValueMap field) = _ at negativeField
  change originalValueKernel positiveHelicity (startupCharacterKernel 2 1 (originalValueKernel quarterValueMap field)) +
    originalValueKernel negativeHelicity (startupCharacterKernel 2 (-1) (originalValueKernel quarterValueMap field)) = _
  rw [positiveField, negativeField]
  have first := congrArg (fun operator : StartupL2 2 →L[ℂ] StartupL2 2 => operator (startupCharacterKernel 2 1 field)) positiveMaps
  have second := congrArg (fun operator : StartupL2 2 →L[ℂ] StartupL2 2 => operator (startupCharacterKernel 2 (-1) field)) negativeMaps
  exact (congrArg₂ (fun x y : StartupL2 2 => x + y) first second).trans ((originalValueKernel quarterValueMap).map_add
    (originalValueKernel positiveHelicity (startupCharacterKernel 2 1 field))
    (originalValueKernel negativeHelicity (startupCharacterKernel 2 (-1) field))).symm

theorem startupReflection_quarter (field : StartupL2 2) :
    startupPointKernel reflectionValueMap cartesianReflectionEquiv (originalValueKernel quarterValueMap field) =
      -originalValueKernel quarterValueMap (startupPointKernel reflectionValueMap cartesianReflectionEquiv field) := by
  have anti : reflectionValueMap.comp quarterValueMap = -(quarterValueMap.comp reflectionValueMap) := by
    apply ContinuousLinearMap.ext
    intro value
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [reflectionValueMap, reflectionValueLinear, quarterValueMap, quarterValueLinear]
  have left := startupPointKernel_comp reflectionValueMap quarterValueMap cartesianReflectionEquiv (LinearIsometryEquiv.refl ℝ _)
  have right := startupPointKernel_comp quarterValueMap reflectionValueMap (LinearIsometryEquiv.refl ℝ _) cartesianReflectionEquiv
  have actual : (startupPointKernel reflectionValueMap cartesianReflectionEquiv).comp (originalValueKernel quarterValueMap) =
      -(originalValueKernel quarterValueMap).comp (startupPointKernel reflectionValueMap cartesianReflectionEquiv) := by
    change (startupPointKernel reflectionValueMap cartesianReflectionEquiv).comp
      (startupPointKernel quarterValueMap (LinearIsometryEquiv.refl ℝ _)) = _
    rw [left]
    change startupPointKernel (reflectionValueMap.comp quarterValueMap) cartesianReflectionEquiv = _
    rw [anti, startupPointKernel_neg]
    exact congrArg Neg.neg right.symm
  exact congrArg (fun operator : StartupL2 2 →L[ℂ] StartupL2 2 => operator field) actual

/-- The actual all-cell Qrad agrees with I-(I+S)A/2 on arbitrary L2 fields.
No smooth compensation data or extra angular gauge is assumed. -/
theorem startupGenuineQrad_reflection (field : StartupL2 2) :
    startupGenuineQradKernel field = field - (1 / 2 : ℂ) •
      (originalAverageKernel field + startupPointKernel reflectionValueMap cartesianReflectionEquiv (originalAverageKernel field)) := by
  have square (value : StartupL2 2) := congrArg (fun operator : StartupL2 2 →L[ℂ] StartupL2 2 => operator value) startupQuarter_square
  change field + originalValueKernel quarterValueMap ((1 / 2 : ℂ) •
    (originalAverageKernel (originalValueKernel quarterValueMap field) -
      startupPointKernel reflectionValueMap cartesianReflectionEquiv (originalAverageKernel (originalValueKernel quarterValueMap field)))) = _
  rw [startupAverage_quarter, startupReflection_quarter, map_smul, map_sub, map_neg]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply] at square
  rw [square, square]
  module

end Grad.CartesianStartup
