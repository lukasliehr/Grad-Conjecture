import GQ14AxisFlatness

noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory
open scoped Interval

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Radial

theorem ClosedAxisFlat.valueMap {input output : ℕ} {field : ClosedDisk → ComplexEuclidean input}
    (flat : ClosedAxisFlat field) (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    ClosedAxisFlat (fun point => mapping (field point)) :=
  flat.of_bound _ ‖mapping‖ (norm_nonneg _) (fun point => mapping.le_opNorm (field point))

theorem ClosedAxisFlat.smul {dimension : ℕ} {field : ClosedDisk → ComplexEuclidean dimension}
    (flat : ClosedAxisFlat field) (scalar : ℂ) : ClosedAxisFlat (fun point => scalar • field point) :=
  flat.of_bound _ ‖scalar‖ (norm_nonneg _) (fun point => (norm_smul scalar (field point)).le)

theorem ClosedAxisFlat.operator {input output : ℕ} {field : ClosedDisk → ComplexEuclidean input}
    (flat : ClosedAxisFlat field)
    (coefficient : C(ClosedDisk, ComplexEuclidean input →L[ℂ] ComplexEuclidean output)) :
    ClosedAxisFlat (fun point => coefficient point (field point)) := by
  apply flat.of_bound _ ‖coefficient‖ (norm_nonneg coefficient)
  intro point
  exact ((coefficient point).le_opNorm (field point)).trans
    (mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm coefficient point) (norm_nonneg _))

theorem closedCharacterProjection_local_bound {dimension : ℕ} (mode : ℤ)
    (field : ClosedDisk → ComplexEuclidean dimension) (point : ClosedDisk) (constant : ℝ)
    (bound : ∀ angle : ℝ, ‖field (rotatedPoint angle point)‖ ≤ constant) :
    ‖closedCharacterProjection mode field point‖ ≤ constant := by
  rw [closedCharacterProjection_integral, norm_smul, Real.norm_of_nonneg (by positivity)]
  have integralBound : ‖∫ angle in (0 : ℝ)..2 * Real.pi,
      angularCharacter mode angle • field (rotatedPoint angle point)‖ ≤ constant * (2 * Real.pi) := by
    have estimate := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2 * Real.pi)
      (f := fun angle => angularCharacter mode angle • field (rotatedPoint angle point))
      (fun angle _ => by rw [norm_smul, angularCharacter_norm, one_mul]; exact bound angle)
    simpa only [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using estimate
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (constant * (2 * Real.pi)) := mul_le_mul_of_nonneg_left integralBound (by positivity)
    _ = constant := by field_simp

theorem ClosedAxisFlat.character {dimension : ℕ} {field : ClosedDisk → ComplexEuclidean dimension}
    (flat : ClosedAxisFlat field) (mode : ℤ) : ClosedAxisFlat (closedCharacterProjection mode field) := by
  intro tolerance positive
  obtain ⟨radius, radiusPositive, bound⟩ := flat tolerance positive
  refine ⟨radius, radiusPositive, fun point inside => ?_⟩
  apply closedCharacterProjection_local_bound mode field point (tolerance * ‖point.val‖)
  intro angle
  simpa only [radialRotatedPoint_norm] using bound (rotatedPoint angle point)
    (by simpa only [radialRotatedPoint_norm] using inside)

theorem ClosedAxisFlat.orthogonal {dimension : ℕ} {field : ClosedDisk → ComplexEuclidean dimension}
    (flat : ClosedAxisFlat field) (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    ClosedAxisFlat (fun point => field (orthogonalClosedPoint orthogonal point)) :=
  flat.pullback (orthogonalClosedPoint orthogonal) (fun point => orthogonal.norm_map point.val)

theorem ClosedAxisFlat.equivariant {field : ClosedDisk → ComplexEuclidean 2}
    (flat : ClosedAxisFlat field) : ClosedAxisFlat (closedEquivariantValue field) :=
  ((flat.character 1).valueMap positiveHelicity).add ((flat.character (-1)).valueMap negativeHelicity)

theorem ClosedAxisFlat.tangential {field : ClosedDisk → ComplexEuclidean 2}
    (flat : ClosedAxisFlat field) : ClosedAxisFlat (closedTangentialValue field) :=
  (flat.equivariant.sub ((flat.equivariant.orthogonal cartesianReflectionEquiv).valueMap reflectionValueMap)).smul (1 / 2)

theorem ClosedAxisFlat.complement {field : ClosedDisk → ComplexEuclidean 3}
    (flat : ClosedAxisFlat field) : ClosedAxisFlat (cartesianComplementValue field) :=
  (((flat.valueMap planarPartMap).tangential).valueMap planarInclusionMap).add
    (((flat.valueMap toroidalPartMap).character 0).valueMap toroidalInclusionMap)

end Grad.GaugeCoefficients.Physical.GaugeTransfer
