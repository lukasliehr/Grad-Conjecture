import QR3CoreCompatibility
import CP14Consumer

noncomputable section

open scoped ComplexConjugate

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.Constraints
open Grad.GaugeCoefficients.Radial

theorem closedJetConjugate_complex_smul {dimension : ℕ} (scalar : ℂ)
    (field : ClosedJet dimension) :
    closedJetConjugate (scalar • field) = conj scalar • closedJetConjugate field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  simp only [closedJetConjugate_value_apply, closedJet_value_smul,
    ContinuousMap.smul_apply, PiLp.smul_apply, smul_eq_mul, map_mul]

theorem coreConjugation_complex_smul {dimension : ℕ} (parameters : PhaseParameters)
    (scalar : ℂ) (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (scalar • field) =
      conj scalar • cartesianCoreConjugation parameters field := by
  apply Subtype.ext
  funext cell
  exact closedJetConjugate_complex_smul scalar (field.1 (-cell))

theorem angularCharacter_conjugate (mode : ℤ) (angle : ℝ) :
    conj (angularCharacter mode angle) = angularCharacter (-mode) angle := by
  unfold angularCharacter cellExponential
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul]

/-- Literal conjugation reverses the angular mode in N1. -/
theorem angularClosedJet_conjugate {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) :
    closedJetConjugate (angularClosedJet mode field) =
      angularClosedJet (-mode) (closedJetConjugate field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianPhysicalConjugation dimension ((angularClosedJet mode field).value point) = _
  rw [angularClosedJet_value, angularClosedJet_value,
    (cartesianPhysicalConjugation dimension).map_smul]
  have commutation : cartesianPhysicalConjugation dimension
      (∫ angle in (0 : ℝ)..2 * Real.pi,
        angularCharacter mode angle • field.value (rotatedPoint angle point)) =
      ∫ angle in (0 : ℝ)..2 * Real.pi, cartesianPhysicalConjugation dimension
        (angularCharacter mode angle • field.value (rotatedPoint angle point)) := by
    exact ((cartesianPhysicalConjugation dimension).toContinuousLinearEquiv.toContinuousLinearMap.intervalIntegral_comp_comm
      ((angularValueIntegrand_continuous mode field point).intervalIntegrable 0 (2 * Real.pi))).symm
  rw [commutation]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  change cartesianPhysicalConjugation dimension
    (angularCharacter mode angle • field.value (rotatedPoint angle point)) =
    angularCharacter (-mode) angle •
      cartesianPhysicalConjugation dimension (field.value (rotatedPoint angle point))
  rw [axisConjugation_smul, angularCharacter_conjugate]

theorem angularCore_conjugate {dimension : ℕ} (parameters : PhaseParameters)
    (mode : ℤ) (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (angularCore parameters mode field) =
      angularCore parameters (-mode) (cartesianCoreConjugation parameters field) := by
  apply Subtype.ext
  funext cell
  exact angularClosedJet_conjugate mode (field.1 (-cell))

theorem orthogonalCore_conjugate {dimension : ℕ} (parameters : PhaseParameters)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (orthogonalCore parameters orthogonal field) =
      orthogonalCore parameters orthogonal (cartesianCoreConjugation parameters field) := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rfl

end Grad.CompletedReality
