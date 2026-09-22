import AXF23CartesianRadial

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.QuotientProjection
open Grad.AxisSplit Grad.AxisJet Grad.AxisCore

variable {parameters : PhaseParameters}

def cartesianSourceLinear : SmoothQuotient parameters →ₗ[ℂ] ACore parameters 2 :=
  (Grad.Constraints.valueMapCore (componentInsertion 0) parameters).comp cartesianSpinFirst +
    (Grad.Constraints.valueMapCore (componentInsertion 1) parameters).comp cartesianSpinSecond

@[simp] theorem cartesianSourceLinear_apply (source : SmoothQuotient parameters) :
    cartesianSourceLinear source = cartesianSourceVector source := rfl

def fixedValueCorrection {dimension : ℕ} :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  radialValueInsertion.comp traceZero

theorem profileJetZero_valueMap {first second : ℕ}
    (mapping : ComplexEuclidean first →L[ℂ] ComplexEuclidean second)
    (cell : ℤ) (value : ComplexEuclidean first) :
    profileJetZero cell (mapping value) = valueMapJet mapping (profileJetZero cell value) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet_value]
  change profileScalarZero cell point.val • mapping value =
    mapping (profileScalarZero cell point.val • value)
  exact ((mapping.restrictScalars ℝ).map_smul _ _).symm

theorem fixedValueCorrection_valueMap {first second : ℕ}
    (mapping : ComplexEuclidean first →L[ℂ] ComplexEuclidean second)
    (field : ACore parameters first) :
    fixedValueCorrection (Grad.Constraints.valueMapCore mapping parameters field) =
      Grad.Constraints.valueMapCore mapping parameters (fixedValueCorrection field) := by
  apply Subtype.ext
  funext cell
  change angularClosedJet 0 (profileJetZero cell
    (originValue (valueMapJet mapping (field.val cell)))) =
      valueMapJet mapping (angularClosedJet 0 (profileJetZero cell (originValue (field.val cell))))
  have origin : originValue (valueMapJet mapping (field.val cell)) =
      mapping (originValue (field.val cell)) := valueMapJet_value mapping (field.val cell) originPoint
  rw [origin, profileJetZero_valueMap, angularClosedJet_valueMap]

theorem cartesianSourceVector_valueCorrection (source : SmoothQuotient parameters) :
    cartesianSourceVector (valueCorrection source) =
      fixedValueCorrection (cartesianSourceVector source) := by
  apply spinCore_joint_injective
  · rw [spinCore_cartesianSource_plus]
    change radialValueInsertion (traceZero (source 0)) =
      Grad.Constraints.valueMapCore (spinValue 1) parameters
        (fixedValueCorrection (cartesianSourceVector source))
    rw [← fixedValueCorrection_valueMap]
    change fixedValueCorrection (source 0) =
      fixedValueCorrection (spinCore 1 (cartesianSourceVector source))
    rw [spinCore_cartesianSource_plus]
  · rw [spinCore_cartesianSource_minus]
    change radialValueInsertion (traceZero (source 1)) =
      Grad.Constraints.valueMapCore (spinValue (-1)) parameters
        (fixedValueCorrection (cartesianSourceVector source))
    rw [← fixedValueCorrection_valueMap]
    change fixedValueCorrection (source 1) =
      fixedValueCorrection (spinCore (-1) (cartesianSourceVector source))
    rw [spinCore_cartesianSource_minus]

def cartesianCurlTrace : ACore parameters 2 →ₗ[ℂ] AxisSmoothCore parameters 1 :=
  (traceFirst 0).comp (componentCore 2 1) - (traceFirst 1).comp (componentCore 2 0)

theorem affineTrace_cartesian_curl (source : SmoothQuotient parameters) :
    affineTrace parameters source = (1 / 2 : ℂ) •
      cartesianCurlTrace (cartesianSourceVector source) := by
  change affineTrace parameters source = (1 / 2 : ℂ) •
    (traceFirst 0 (componentCore 2 1 (vectorTuple (cartesianSpinFirst source) (cartesianSpinSecond source))) -
      traceFirst 1 (componentCore 2 0 (vectorTuple (cartesianSpinFirst source) (cartesianSpinSecond source))))
  rw [componentCore_vectorTuple, componentCore_vectorTuple]
  change (4 * Complex.I)⁻¹ •
    ((traceFirst 0 (source 0) - Complex.I • traceFirst 1 (source 0)) -
      (traceFirst 0 (source 1) + Complex.I • traceFirst 1 (source 1))) =
    (1 / 2 : ℂ) • (traceFirst 0 ((-Complex.I / 2) • (source 0 - source 1)) -
      traceFirst 1 ((1 / 2 : ℂ) • (source 0 + source 1)))
  have inverse : (4 * Complex.I)⁻¹ = -Complex.I / 4 := by
    apply inv_eq_of_mul_eq_one_right
    calc _ = -(Complex.I * Complex.I) := by ring
         _ = 1 := by rw [Complex.I_mul_I]; norm_num
  rw [inverse]
  simp only [map_smul, map_sub, map_add]
  calc _ = (-Complex.I / 4) • traceFirst 0 (source 0) +
      (Complex.I ^ 2 / 4) • traceFirst 1 (source 0) +
      (Complex.I / 4) • traceFirst 0 (source 1) +
      (Complex.I ^ 2 / 4) • traceFirst 1 (source 1) := by module
       _ = _ := by rw [Complex.I_sq]; module

end Grad.FlatSourceProjection
