import GC18PointwiseComplement

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial Grad.PhysicalFamily

/-- Literal Cartesian character projection on physical closed-disk values. -/
def closedCharacterProjection {dimension : ℕ} (mode : ℤ)
    (field : ClosedDisk → ComplexEuclidean dimension) (point : ClosedDisk) : ComplexEuclidean dimension :=
  angularProjectionValue mode (closedFieldExtension field) point.val

theorem closedCharacterProjection_rotation {dimension : ℕ} (mode : ℤ)
    (field : ClosedDisk → ComplexEuclidean dimension) (angle : ℝ) (point : ClosedDisk) :
    closedCharacterProjection mode field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point) =
      angularCharacter mode (-angle) • closedCharacterProjection mode field point := by
  unfold closedCharacterProjection
  have identity := angularProjectionValue_rotation mode (closedFieldExtension field) angle point.val
  simpa only [Grad.GaugeCoefficients.Radial.rotatedPoint, physicalRotation_eq_orthogonal,
    planeRotationEquiv_apply] using identity

theorem closedCharacterProjection_jet {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) (point : ClosedDisk) :
    closedCharacterProjection mode field.value point = (angularClosedJet mode field).value point := by
  change angularProjectionValue mode (closedFieldExtension field.value) point.val =
    angularProjectionValue mode (smoothClosedExtension field) point.val
  apply angularProjectionValue_congr_closed
  intro other
  rw [closedFieldExtension_value, smoothClosedExtension_value]

theorem closedCharacterProjection_zero {dimension : ℕ}
    (field : ClosedDisk → ComplexEuclidean dimension) (point : ClosedDisk) :
    closedCharacterProjection 0 field point = closedAngularMean field point := by
  rw [closedAngularMean_eq_rotationAverage]
  unfold closedCharacterProjection angularProjectionValue rotationAverage
  simp only [angularCharacter_zero_mode, one_smul]

def closedEquivariantValue (field : ClosedDisk → ComplexEuclidean 2) (point : ClosedDisk) : ComplexEuclidean 2 :=
  positiveHelicity (closedCharacterProjection 1 field point) +
    negativeHelicity (closedCharacterProjection (-1) field point)

theorem closedEquivariantValue_rotation (field : ClosedDisk → ComplexEuclidean 2)
    (angle : ℝ) (point : ClosedDisk) :
    closedEquivariantValue field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point) =
      rotationValueMap angle (closedEquivariantValue field point) := by
  rw [closedEquivariantValue, closedEquivariantValue,
    closedCharacterProjection_rotation, closedCharacterProjection_rotation,
    map_smul, map_smul, map_add, rotationValueMap_positiveHelicity, rotationValueMap_negativeHelicity]

theorem closedEquivariantValue_jet (field : ClosedJet 2) (point : ClosedDisk) :
    closedEquivariantValue field.value point = (equivariantAverageJet field).value point := by
  rw [closedEquivariantValue, closedCharacterProjection_jet, closedCharacterProjection_jet,
    equivariantAverageJet_value_helicity]

/-- The nonsingular Cartesian reflection/rotation formula, with no division
of an unknown field by radius. This is the actual T realization. -/
def closedTangentialValue (field : ClosedDisk → ComplexEuclidean 2) (point : ClosedDisk) : ComplexEuclidean 2 :=
  (1 / 2 : ℂ) • (closedEquivariantValue field point -
    reflectionValueMap (closedEquivariantValue field (orthogonalClosedPoint cartesianReflectionEquiv point)))

theorem closedTangentialValue_jet (field : ClosedJet 2) (point : ClosedDisk) :
    closedTangentialValue field.value point = (tangentialJet field).value point := by
  rw [closedTangentialValue, closedEquivariantValue_jet, closedEquivariantValue_jet, tangentialJet_value]

theorem closedTangentialValue_polar (field : ClosedDisk → ComplexEuclidean 2)
    (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedTangentialValue field (polarClosedPoint radius bounded angle) =
      (closedEquivariantValue field (axisClosedPoint radius bounded) 1) • polarTangentialVector angle := by
  rw [closedTangentialValue, reflectedPoint_polar]
  change (1 / 2 : ℂ) •
    (closedEquivariantValue field (Grad.GaugeCoefficients.Radial.rotatedPoint angle (axisClosedPoint radius bounded)) -
      reflectionValueMap (closedEquivariantValue field (Grad.GaugeCoefficients.Radial.rotatedPoint (-angle) (axisClosedPoint radius bounded)))) = _
  rw [closedEquivariantValue_rotation, closedEquivariantValue_rotation]
  exact rotated_antisymmetric_value angle _

/-- Actual nonsingular Cartesian C0=diag(T,Π), on physical values. -/
def cartesianComplementValue (field : ClosedDisk → ComplexEuclidean 3) (point : ClosedDisk) : ComplexEuclidean 3 :=
  planarInclusionMap (closedTangentialValue (fun other => planarPartMap (field other)) point) +
    toroidalInclusionMap (closedCharacterProjection 0 (fun other => toroidalPartMap (field other)) point)

theorem cartesianComplementValue_core (parameters : PhaseParameters) (field : ACore parameters 3)
    (cell : ℤ) (point : ClosedDisk) :
    cartesianComplementValue (field.val cell).value point =
      ((fixedComplementCore parameters field).val cell).value point := by
  have planar : (fun other => planarPartMap ((field.val cell).value other)) =
      (valueMapJet planarPartMap (field.val cell)).value :=
    funext (fun other => (valueMapJet_value planarPartMap (field.val cell) other).symm)
  have toroidal : (fun other => toroidalPartMap ((field.val cell).value other)) =
      (valueMapJet toroidalPartMap (field.val cell)).value :=
    funext (fun other => (valueMapJet_value toroidalPartMap (field.val cell) other).symm)
  rw [cartesianComplementValue, planar, toroidal]
  rw [closedTangentialValue_jet, closedCharacterProjection_jet]
  change _ = (valueMapJet planarInclusionMap (tangentialJet (valueMapJet planarPartMap (field.val cell)))).value point +
    (valueMapJet toroidalInclusionMap (angularClosedJet 0 (valueMapJet toroidalPartMap (field.val cell)))).value point
  rw [valueMapJet_value, valueMapJet_value]

end Grad.GaugeCoefficients.Physical.RadialLedger
