import AXF22SpinMaps

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.QuotientProjection

variable {parameters : PhaseParameters}

theorem spinValue_reflection (sign : ℂ) :
    (spinValue sign).comp reflectionValueMap = spinValue (-sign) := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro component
  fin_cases component
  simp [ContinuousLinearMap.comp_apply, spinValue_apply, reflectionValueMap,
    reflectionValueLinear]

theorem spinCore_reflected (sign : ℂ) (field : ACore parameters 2) :
    spinCore sign (reflectedVectorCore parameters field) =
      reflection parameters (spinCore (-sign) field) := by
  change Grad.Constraints.valueMapCore (spinValue sign) parameters
    (Grad.Constraints.valueMapCore reflectionValueMap parameters
      (orthogonalCore parameters cartesianReflectionEquiv field)) = _
  rw [coreValueMap_comp, spinValue_reflection]
  apply Subtype.ext
  funext cell
  exact valueMapJet_orthogonal (spinValue (-sign)) cartesianReflectionEquiv (field.val cell)

/-- AM1's Cartesian rotation/reflection radial projection, with no division
by the radius. The minus-reflection part is the accepted tangential map. -/
def radialSourceCore (parameters : PhaseParameters) :
    ACore parameters 2 →ₗ[ℂ] ACore parameters 2 :=
  (1 / 2 : ℂ) • ((LinearMap.id + reflectedVectorCore parameters).comp
    (equivariantAverageCore parameters))

theorem radialSourceCore_eq_average_sub_tangential (field : ACore parameters 2) :
    radialSourceCore parameters field =
      equivariantAverageCore parameters field - tangentialCore parameters field := by
  change (1 / 2 : ℂ) • (equivariantAverageCore parameters field +
    reflectedVectorCore parameters (equivariantAverageCore parameters field)) =
      equivariantAverageCore parameters field - (1 / 2 : ℂ) •
        (equivariantAverageCore parameters field -
          reflectedVectorCore parameters (equivariantAverageCore parameters field))
  module

theorem spinCore_radial_plus (field : ACore parameters 2) :
    spinCore 1 (radialSourceCore parameters field) = (1 / 2 : ℂ) •
      (angularCore parameters 1 (spinCore 1 field) +
        reflection parameters (angularCore parameters (-1) (spinCore (-1) field))) := by
  change spinCore 1 ((1 / 2 : ℂ) • (equivariantAverageCore parameters field +
    reflectedVectorCore parameters (equivariantAverageCore parameters field))) = _
  rw [map_smul, map_add, spinCore_equivariant_plus, spinCore_reflected,
    spinCore_equivariant_minus]

theorem spinCore_radial_minus (field : ACore parameters 2) :
    spinCore (-1) (radialSourceCore parameters field) = (1 / 2 : ℂ) •
      (angularCore parameters (-1) (spinCore (-1) field) +
        reflection parameters (angularCore parameters 1 (spinCore 1 field))) := by
  change spinCore (-1) ((1 / 2 : ℂ) • (equivariantAverageCore parameters field +
    reflectedVectorCore parameters (equivariantAverageCore parameters field))) = _
  rw [map_smul, map_add, spinCore_equivariant_minus, spinCore_reflected]
  norm_num only [neg_neg]
  rw [spinCore_equivariant_plus]

theorem radialSource_cartesian_plus (source : SmoothQuotient parameters) :
    spinCore 1 (radialSourceCore parameters (cartesianSourceVector source)) =
      firstMode parameters source := by
  rw [spinCore_radial_plus, spinCore_cartesianSource_plus, spinCore_cartesianSource_minus]
  rfl

theorem radialSource_cartesian_minus (source : SmoothQuotient parameters) :
    spinCore (-1) (radialSourceCore parameters (cartesianSourceVector source)) =
      reflection parameters (firstMode parameters source) := by
  rw [spinCore_radial_minus, spinCore_cartesianSource_plus, spinCore_cartesianSource_minus]
  change (1 / 2 : ℂ) • (angularCore parameters (-1) (source 1) +
    reflection parameters (angularCore parameters 1 (source 0))) =
      reflection parameters ((1 / 2 : ℂ) • (angularCore parameters 1 (source 0) +
        reflection parameters (angularCore parameters (-1) (source 1))))
  rw [map_smul, map_add, reflection_involutive, add_comm]

theorem spinCore_components_first (field : ACore parameters 2) :
    (1 / 2 : ℂ) • (spinCore 1 field + spinCore (-1) field) = componentCore 2 0 field := by
  rw [spinCore_components, spinCore_components]
  module

theorem spinCore_components_second (field : ACore parameters 2) :
    (-Complex.I / 2) • (spinCore 1 field - spinCore (-1) field) = componentCore 2 1 field := by
  rw [spinCore_components, spinCore_components]
  calc _ = -(Complex.I ^ 2) • componentCore 2 1 field := by module
       _ = componentCore 2 1 field := by simp

theorem spinCore_joint_injective {first second : ACore parameters 2}
    (plus : spinCore 1 first = spinCore 1 second)
    (minus : spinCore (-1) first = spinCore (-1) second) : first = second := by
  have zero : componentCore 2 0 first = componentCore 2 0 second := by
    rw [← spinCore_components_first, ← spinCore_components_first, plus, minus]
  have one : componentCore 2 1 first = componentCore 2 1 second := by
    rw [← spinCore_components_second, ← spinCore_components_second, plus, minus]
  rw [← vectorTuple_components first, zero, one, vectorTuple_components]

/-- The literal spin projection and AM1's actual Cartesian radial map agree. -/
theorem cartesianSourceVector_modeProjection (source : SmoothQuotient parameters) :
    cartesianSourceVector (modeProjection parameters source) =
      radialSourceCore parameters (cartesianSourceVector source) := by
  apply spinCore_joint_injective
  · rw [spinCore_cartesianSource_plus, radialSource_cartesian_plus]
    rfl
  · rw [spinCore_cartesianSource_minus, radialSource_cartesian_minus]
    rfl

end Grad.FlatSourceProjection
