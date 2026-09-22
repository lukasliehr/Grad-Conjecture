import PolarVectorAlgebra

noncomputable section

open Set MeasureTheory
open scoped Interval Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.GaugeCoefficients.Radial Grad.PhysicalFamily

theorem angularClosedJet_rotation_value {dimension : ℕ} (mode : ℤ)
    (field : ClosedJet dimension) (angle : ℝ) (point : ClosedDisk) :
    (angularClosedJet mode field).value (rotatedPoint angle point) =
      angularCharacter mode (-angle) • (angularClosedJet mode field).value point := by
  change angularProjectionValue mode (smoothClosedExtension field) (planeRotationEquiv angle point.val) = _
  rw [← physicalRotation_eq_orthogonal]
  exact angularProjectionValue_rotation mode _ angle point.val

theorem equivariantAverageJet_value_helicity (field : ClosedJet 2) (point : ClosedDisk) :
    (equivariantAverageJet field).value point =
      positiveHelicity ((angularClosedJet 1 field).value point) +
        negativeHelicity ((angularClosedJet (-1) field).value point) := by
  rw [equivariantAverageJet_eq]
  change (valueMapJet positiveHelicity (angularClosedJet 1 field)).value point +
    (valueMapJet negativeHelicity (angularClosedJet (-1) field)).value point = _
  rw [valueMapJet_value, valueMapJet_value]

theorem equivariantAverageJet_rotation_value (field : ClosedJet 2) (angle : ℝ) (point : ClosedDisk) :
    (equivariantAverageJet field).value (rotatedPoint angle point) =
      rotationValueMap angle ((equivariantAverageJet field).value point) := by
  rw [equivariantAverageJet_value_helicity, equivariantAverageJet_value_helicity,
    angularClosedJet_rotation_value, angularClosedJet_rotation_value,
    map_smul, map_smul, map_add, rotationValueMap_positiveHelicity, rotationValueMap_negativeHelicity]

theorem equivariantAverageJet_polar_value (field : ClosedJet 2) (radius : ℝ)
    (bounded : |radius| ≤ 1) (angle : ℝ) :
    (equivariantAverageJet field).value (polarClosedPoint radius bounded angle) =
      rotationValueMap angle ((equivariantAverageJet field).value (axisClosedPoint radius bounded)) :=
  equivariantAverageJet_rotation_value field angle (axisClosedPoint radius bounded)

theorem reflectedVectorJet_value (field : ClosedJet 2) (point : ClosedDisk) :
    (reflectedVectorJet field).value point =
      reflectionValueMap (field.value (orthogonalClosedPoint cartesianReflectionEquiv point)) := by
  rw [reflectedVectorJet_eq, valueMapJet_value]
  rfl

theorem tangentialJet_value (field : ClosedJet 2) (point : ClosedDisk) :
    (tangentialJet field).value point = (1 / 2 : ℂ) •
      ((equivariantAverageJet field).value point -
        reflectionValueMap ((equivariantAverageJet field).value
          (orthogonalClosedPoint cartesianReflectionEquiv point))) := by
  rw [tangentialJet_eq]
  simp only [sub_eq_add_neg, Grad.CartesianState.closedJet_value_smul,
    Grad.CartesianState.closedJet_value_add, Grad.CartesianState.closedJet_value_neg,
    ContinuousMap.smul_apply, ContinuousMap.add_apply, ContinuousMap.neg_apply,
    reflectedVectorJet_value]

theorem tangentialJet_polar_axis_value (field : ClosedJet 2) (radius : ℝ)
    (bounded : |radius| ≤ 1) (angle : ℝ) :
    (tangentialJet field).value (polarClosedPoint radius bounded angle) =
      ((equivariantAverageJet field).value (axisClosedPoint radius bounded) 1) •
        polarTangentialVector angle := by
  rw [tangentialJet_value, reflectedPoint_polar,
    equivariantAverageJet_polar_value, equivariantAverageJet_polar_value]
  exact rotated_antisymmetric_value angle _

end Grad.Constraints
