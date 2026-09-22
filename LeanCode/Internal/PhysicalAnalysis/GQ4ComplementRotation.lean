import GQ3RotationCore
import GaugeProjectionBounds

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearRange Grad.GaugeCoefficients.Physical.RadialLedger

theorem rotationJet_valueMap {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) (field : ClosedJet input) :
    rotationJet (valueMapJet mapping field) = valueMapJet mapping (rotationJet field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have original := closedOrbit_hasDerivAt field point 0
  have composed := (mapping.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 original
  have mapped := closedOrbit_hasDerivAt (valueMapJet mapping field) point 0
  have equality : (fun angle => (valueMapJet mapping field).value (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)) =
      (fun angle => mapping (field.value (Grad.GaugeCoefficients.Radial.rotatedPoint angle point))) :=
    funext (fun _ => valueMapJet_value _ _ _)
  rw [equality, rotatedPoint_zero] at mapped
  rw [rotatedPoint_zero] at composed
  rw [valueMapJet_value]
  exact mapped.unique composed

theorem rotationJet_add {dimension : ℕ} (first second : ClosedJet dimension) :
    rotationJet (first + second) = rotationJet first + rotationJet second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have derivative := (closedOrbit_hasDerivAt first point 0).add (closedOrbit_hasDerivAt second point 0)
  have total := closedOrbit_hasDerivAt (first + second) point 0
  simp only [closedJet_value_add, ContinuousMap.add_apply, rotatedPoint_zero] at total derivative ⊢
  exact total.unique derivative

/-- J on the planar stored coordinates, zero on the toroidal coordinate.
Its target and norm are the original Euclidean three-component ones. -/
def storedQuarterMap : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 :=
  planarInclusionMap.comp (quarterValueMap.comp planarPartMap)

theorem storedQuarterMap_norm_le : ‖storedQuarterMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound storedQuarterMap zero_le_one
  intro value
  have first := planarInclusionMap.le_opNorm (quarterValueMap (planarPartMap value))
  have second := planarPartMap.le_opNorm value
  have firstBound := first.trans (mul_le_mul_of_nonneg_right planarInclusionMap_norm_le (norm_nonneg _))
  have secondBound := second.trans (mul_le_mul_of_nonneg_right planarPartMap_norm_le (norm_nonneg _))
  have turned : ‖quarterValueMap (planarPartMap value)‖ = ‖planarPartMap value‖ := quarterValue_norm _
  rw [one_mul, turned] at firstBound
  rw [one_mul] at secondBound
  simpa only [storedQuarterMap, ContinuousLinearMap.comp_apply, one_mul] using firstBound.trans secondBound

theorem storedQuarterMap_planar (value : ComplexEuclidean 2) :
    storedQuarterMap (planarInclusionMap value) = planarInclusionMap (quarterValueMap value) := by
  change planarInclusionMap (quarterValueMap ((planarPartMap.comp planarInclusionMap) value)) = _
  rw [planarPart_planarInclusion, ContinuousLinearMap.id_apply]

theorem storedQuarterMap_toroidal (value : ComplexEuclidean 1) :
    storedQuarterMap (toroidalInclusionMap value) = 0 := by
  change planarInclusionMap (quarterValueMap ((planarPartMap.comp toroidalInclusionMap) value)) = _
  rw [planarPart_toroidalInclusion, zero_apply, map_zero, map_zero]

/-- The actual differential identity on the fixed complement; neither
radiality nor an angular derivative is assumed as part of its range. -/
theorem rotationJet_fixedComplement (field : ClosedJet 3) :
    rotationJet (fixedComplementJet field) = valueMapJet storedQuarterMap (fixedComplementJet field) := by
  change rotationJet (valueMapJet planarInclusionMap (tangentialJet (valueMapJet planarPartMap field)) +
      valueMapJet toroidalInclusionMap (angularClosedJet 0 (valueMapJet toroidalPartMap field))) = _
  rw [rotationJet_add, rotationJet_valueMap, rotationJet_valueMap,
    rotationJet_tangential, rotationJet_angular_zero, valueMapJet_map_zero, add_zero]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [valueMapJet_value]
  change planarInclusionMap (quarterValueMap ((tangentialJet (valueMapJet planarPartMap field)).value point)) =
    storedQuarterMap ((valueMapJet planarInclusionMap (tangentialJet (valueMapJet planarPartMap field)) +
      valueMapJet toroidalInclusionMap (angularClosedJet 0 (valueMapJet toroidalPartMap field))).value point)
  rw [closedJet_value_add, ContinuousMap.add_apply, valueMapJet_value, valueMapJet_value,
    map_add, storedQuarterMap_planar, storedQuarterMap_toroidal, add_zero]

theorem rotationJet_of_complement_fixed (field : ClosedJet 3) (fixed : fixedComplementJet field = field) :
    rotationJet field = valueMapJet storedQuarterMap field := by
  have identity := rotationJet_fixedComplement field
  rwa [fixed] at identity

end Grad.GaugeCoefficients.Physical.GaugeTransfer
