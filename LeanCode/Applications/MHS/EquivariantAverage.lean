import ValueMapAngular
import HelicityAlgebra
import CartesianReflection

noncomputable section

open Set MeasureTheory
open scoped Interval Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Radial

/-- A finite character realization of N3's Cartesian equivariant average.
The literal integral identity below fixes its normalization and orientation. -/
def equivariantAverageLinear : ClosedJet 2 →ₗ[ℂ] ClosedJet 2 :=
  (valueMapJetLinear 2 2 positiveHelicity).comp (angularClosedJetLinear 2 1) +
    (valueMapJetLinear 2 2 negativeHelicity).comp (angularClosedJetLinear 2 (-1))

def equivariantAverageJet (field : ClosedJet 2) : ClosedJet 2 := equivariantAverageLinear field

theorem valueMapJet_angular_value {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (mode : ℤ) (field : ClosedJet sourceDimension) (point : ClosedDisk) :
    (valueMapJet mapping (angularClosedJet mode field)).value point =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in (0 : ℝ)..2 * Real.pi,
        mapping (angularCharacter mode angle • field.value (rotatedPoint angle point)) := by
  rw [valueMapJet_value, angularClosedJet_value,
    mapping.intervalIntegral_comp_comm ((angularValueIntegrand_continuous mode field point).intervalIntegrable _ _)]
  exact (mapping.restrictScalars ℝ).map_smul _ _

theorem equivariantAverageJet_value_negative (field : ClosedJet 2) (point : ClosedDisk) :
    (equivariantAverageJet field).value point =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in (0 : ℝ)..2 * Real.pi,
        rotationValueMap (-angle) (field.value (rotatedPoint angle point)) := by
  change (valueMapJet positiveHelicity (angularClosedJet 1 field)).value point +
    (valueMapJet negativeHelicity (angularClosedJet (-1) field)).value point = _
  rw [valueMapJet_angular_value, valueMapJet_angular_value, ← smul_add]
  have firstIntegrable : IntervalIntegrable
      (fun angle => positiveHelicity (angularCharacter 1 angle • field.value (rotatedPoint angle point)))
      volume 0 (2 * Real.pi) :=
    (positiveHelicity.continuous.comp (angularValueIntegrand_continuous 1 field point)).intervalIntegrable _ _
  have secondIntegrable : IntervalIntegrable
      (fun angle => negativeHelicity (angularCharacter (-1) angle • field.value (rotatedPoint angle point)))
      volume 0 (2 * Real.pi) :=
    (negativeHelicity.continuous.comp (angularValueIntegrand_continuous (-1) field point)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add firstIntegrable secondIntegrable]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  simpa only [map_smul] using
    (rotationValueMap_character angle (field.value (rotatedPoint angle point))).symm

theorem rotationValueMap_periodic (value : ComplexEuclidean 2) :
    Function.Periodic (fun angle => rotationValueMap angle value) (2 * Real.pi) := by
  intro angle
  simp [rotationValueMap, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Literal N3: value rotation by theta and argument rotation by -theta. -/
theorem equivariantAverageJet_value (field : ClosedJet 2) (point : ClosedDisk) :
    (equivariantAverageJet field).value point =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in (0 : ℝ)..2 * Real.pi,
        rotationValueMap angle (field.value (rotatedPoint (-angle) point)) := by
  let integrand : ℝ → ComplexEuclidean 2 := fun angle =>
    rotationValueMap (-angle) (field.value (rotatedPoint angle point))
  have periodic : Function.Periodic integrand (2 * Real.pi) := by
    intro angle
    have rotatedPeriodic : rotatedPoint (angle + 2 * Real.pi) point = rotatedPoint angle point := by
      apply Subtype.ext
      simpa only [rotatedPoint, physicalRotation_eq_orthogonal, planeRotationEquiv_apply] using
        Grad.Constraints.physicalRotation_periodic point.val angle
    simp only [integrand, rotatedPeriodic, rotationValueMap, Real.cos_neg, Real.sin_neg]
    simp [Real.cos_add, Real.sin_add]
  rw [equivariantAverageJet_value_negative]
  have equality := periodic_intervalIntegral_neg integrand (2 * Real.pi) periodic
  simpa only [integrand, neg_neg] using congrArg (fun value => ((2 * Real.pi)⁻¹ : ℝ) • value) equality.symm

end Grad.Constraints
