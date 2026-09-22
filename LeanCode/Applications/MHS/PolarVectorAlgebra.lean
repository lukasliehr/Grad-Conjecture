import EquivariantAverageProjection

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Grad.Constraints

open Grad.ClosedJets Grad.GaugeCoefficients.Radial Grad.PhysicalFamily

def polarRadialVector (angle : ℝ) : ComplexEuclidean 2 :=
  WithLp.toLp 2 ![(Real.cos angle : ℂ), (Real.sin angle : ℂ)]

def polarTangentialVector (angle : ℝ) : ComplexEuclidean 2 :=
  WithLp.toLp 2 ![-(Real.sin angle : ℂ), (Real.cos angle : ℂ)]

def polarTangentialComponent (angle : ℝ) (value : ComplexEuclidean 2) : ℂ :=
  -(Real.sin angle : ℂ) * value 0 + (Real.cos angle : ℂ) * value 1

def axisClosedPoint (radius : ℝ) (bounded : |radius| ≤ 1) : ClosedDisk :=
  ⟨WithLp.toLp 2 ![radius, 0], by
    change ‖WithLp.toLp 2 ![radius, (0 : ℝ)]‖ ≤ 1
    rw [PiLp.norm_eq_of_L2]
    simpa [Fin.sum_univ_two] using bounded⟩

def polarClosedPoint (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) : ClosedDisk :=
  rotatedPoint angle (axisClosedPoint radius bounded)

theorem polarClosedPoint_coordinates (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    (polarClosedPoint radius bounded angle).val =
      WithLp.toLp 2 ![radius * Real.cos angle, radius * Real.sin angle] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [polarClosedPoint, rotatedPoint, planeRotation, axisClosedPoint]
  all_goals ring

theorem rotatedPoint_polar (radius : ℝ) (bounded : |radius| ≤ 1) (angle shift : ℝ) :
    rotatedPoint shift (polarClosedPoint radius bounded angle) =
      polarClosedPoint radius bounded (shift + angle) := by
  apply Subtype.ext
  simpa only [polarClosedPoint, rotatedPoint, physicalRotation_eq_orthogonal,
    planeRotationEquiv_apply] using physicalRotation_add shift angle (axisClosedPoint radius bounded).val

theorem reflectedPoint_polar (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    orthogonalClosedPoint cartesianReflectionEquiv (polarClosedPoint radius bounded angle) =
      polarClosedPoint radius bounded (-angle) := by
  apply Subtype.ext
  change cartesianReflection (polarClosedPoint radius bounded angle).val = _
  rw [polarClosedPoint_coordinates, polarClosedPoint_coordinates]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [cartesianReflection]

theorem polarClosedPoint_periodic (radius : ℝ) (bounded : |radius| ≤ 1) :
    Function.Periodic (polarClosedPoint radius bounded) (2 * Real.pi) := by
  intro angle
  apply Subtype.ext
  rw [polarClosedPoint_coordinates, polarClosedPoint_coordinates]
  simp

theorem rotationValueMap_positiveHelicity (angle : ℝ) (value : ComplexEuclidean 2) :
    rotationValueMap angle (positiveHelicity value) =
      angularCharacter 1 (-angle) • positiveHelicity value := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [rotationValueMap_apply, positiveHelicity_apply, angularCharacter_trig] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem rotationValueMap_negativeHelicity (angle : ℝ) (value : ComplexEuclidean 2) :
    rotationValueMap angle (negativeHelicity value) =
      angularCharacter (-1) (-angle) • negativeHelicity value := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [rotationValueMap_apply, negativeHelicity_apply, angularCharacter_trig] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem reflection_rotationValueMap (angle : ℝ) (value : ComplexEuclidean 2) :
    reflectionValueMap (rotationValueMap (-angle) value) =
      rotationValueMap angle (reflectionValueMap value) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [rotationValueMap_apply, reflectionValueMap, reflectionValueLinear]
  ring

theorem rotated_antisymmetric_value (angle : ℝ) (value : ComplexEuclidean 2) :
    (1 / 2 : ℂ) • (rotationValueMap angle value -
      reflectionValueMap (rotationValueMap (-angle) value)) =
        (value 1) • polarTangentialVector angle := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [rotationValueMap_apply, reflectionValueMap, reflectionValueLinear,
      polarTangentialVector] <;> ring

end Grad.Constraints
