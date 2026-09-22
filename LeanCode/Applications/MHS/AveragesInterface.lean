import FiniteAngularProjection
import PolarCoverage
import RadialAngularMean
import AngularLaplacian

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Radial

/-- Exact N1-N5 public contract. All maps, weights, norms and values below
are the actual constructed Cartesian/original-core objects; no analytic
input or assumed projection is part of the contract. -/
structure AveragesGoal : Prop where
  angular_formula : ∀ {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) (point : ClosedDisk),
    (angularClosedJet mode field).value point =
      (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
        angularCharacter mode angle • field.value (rotatedPoint angle point)
  angular_projection : ∀ {dimension : ℕ} (first second : ℤ) (field : ClosedJet dimension),
    angularClosedJet first (angularClosedJet second field) =
      if first = second then angularClosedJet first field else 0
  angular_reflection : ∀ {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension),
    orthogonalJet cartesianReflectionEquiv (angularClosedJet mode field) =
      angularClosedJet (-mode) (orthogonalJet cartesianReflectionEquiv field)
  original_angular_bound : ∀ {dimension grade : ℕ} (parameters : PhaseParameters) (mode : ℤ)
    (field : GradeCore parameters dimension grade),
    ‖angularGradeCore parameters mode field‖ ≤ orthogonalGradeConstant grade * ‖field‖
  average_formula : ∀ (field : ClosedJet 2) (point : ClosedDisk),
    (equivariantAverageJet field).value point =
      (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
        rotationValueMap angle (field.value (rotatedPoint (-angle) point))
  tangential_cartesian : ∀ field : ClosedJet 2,
    tangentialJet field = (1 / 2 : ℂ) •
      (equivariantAverageJet field - reflectedVectorJet (equivariantAverageJet field))
  tangential_projection : ∀ field : ClosedJet 2, tangentialJet (tangentialJet field) = tangentialJet field
  original_tangential_bound : ∀ {grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters 2 grade),
    ‖tangentialGradeCore parameters field‖ ≤ tangentialGradeConstant grade * ‖field‖
  average_polar : ∀ (field : ClosedJet 2) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ),
    (equivariantAverageJet field).value (polarClosedPoint radius bounded angle) =
      polarRadialMean field radius bounded angle • polarRadialVector angle +
        polarTangentialMean field radius bounded angle • polarTangentialVector angle
  tangential_polar : ∀ (field : ClosedJet 2) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ),
    (tangentialJet field).value (polarClosedPoint radius bounded angle) =
      polarTangentialMean field radius bounded angle • polarTangentialVector angle
  entire_disk_polar : ∀ point : ClosedDisk, ∃ angle : ℝ,
    polarClosedPoint ‖point.val‖ (by rw [abs_norm]; exact point.property) angle = point
  angular_zero_jets : ∀ {dimension order : ℕ} (mode : ℤ) (field : ClosedJet dimension),
    (∀ word : CartesianWord order, closedDerivative field order word ⟨0, by simp [closedUnitDisk]⟩ = 0) →
    ∀ word : CartesianWord order, closedDerivative (angularClosedJet mode field) order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0
  tangential_zero_jets : ∀ {order : ℕ} (field : ClosedJet 2),
    (∀ word : CartesianWord order, closedDerivative field order word ⟨0, by simp [closedUnitDisk]⟩ = 0) →
    ∀ word : CartesianWord order, closedDerivative (tangentialJet field) order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0
  coordinate_shift : ∀ {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension),
    angularClosedJet mode (coordinateMultiplyJet 1 field) =
      coordinateMultiplyJet 1 (angularClosedJet (mode - 1) field)
  conjugate_coordinate_shift : ∀ {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension),
    angularClosedJet mode (coordinateMultiplyJet (-1) field) =
      coordinateMultiplyJet (-1) (angularClosedJet (mode + 1) field)
  laplacian_origin : ∀ {dimension : ℕ} (field : ClosedJet dimension),
    closedLaplacianValue (angularClosedJet 0 field) ⟨0, by simp [closedUnitDisk]⟩ =
      closedLaplacianValue field ⟨0, by simp [closedUnitDisk]⟩
  high_modes_projection : ∀ {dimension : ℕ} (field : ClosedJet dimension),
    excludedAngularJet lowAngularModes (excludedAngularJet lowAngularModes field) =
      excludedAngularJet lowAngularModes field
  high_modes_bound : ∀ {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade),
    ‖excludedAngularGradeCore parameters lowAngularModes field‖ ≤
      (1 + 5 * orthogonalGradeConstant grade) * ‖field‖

end Grad.Constraints
