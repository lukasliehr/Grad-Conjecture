import QR4LiteralReality

noncomputable section

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.Constraints Grad.AxisJet Grad.AxisSplit

theorem axisCoreInvolution_add (parameters : PhaseParameters) (dimension : ℕ)
    (first second : AxisSmoothCore parameters dimension) :
    axisCoreInvolution parameters dimension (first + second) =
      axisCoreInvolution parameters dimension first + axisCoreInvolution parameters dimension second := by
  apply Subtype.ext
  funext cell
  exact (cartesianPhysicalConjugation dimension).map_add _ _

theorem axisCoreInvolution_sub (parameters : PhaseParameters) (dimension : ℕ)
    (first second : AxisSmoothCore parameters dimension) :
    axisCoreInvolution parameters dimension (first - second) =
      axisCoreInvolution parameters dimension first - axisCoreInvolution parameters dimension second := by
  apply Subtype.ext
  funext cell
  exact (cartesianPhysicalConjugation dimension).map_sub _ _

theorem axisCoreInvolution_smul (parameters : PhaseParameters) (dimension : ℕ)
    (scalar : ℂ) (field : AxisSmoothCore parameters dimension) :
    axisCoreInvolution parameters dimension (scalar • field) =
      starRingEnd ℂ scalar • axisCoreInvolution parameters dimension field := by
  apply Subtype.ext
  funext cell
  exact axisConjugation_smul dimension scalar _

theorem traceZero_conjugate {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) :
    traceZero (cartesianCoreConjugation parameters field) =
      axisCoreInvolution parameters dimension (traceZero field) := by
  apply Subtype.ext
  funext cell
  rfl

theorem traceFirst_conjugate {dimension : ℕ} (parameters : PhaseParameters)
    (direction : Fin 2) (field : ACore parameters dimension) :
    traceFirst direction (cartesianCoreConjugation parameters field) =
      axisCoreInvolution parameters dimension (traceFirst direction field) := by
  apply Subtype.ext
  funext cell
  change originPartial direction (closedJetConjugate (field.1 (-cell))) =
    cartesianPhysicalConjugation dimension (originPartial direction (field.1 (-cell)))
  rw [originPartial_eq_closedDerivative, closedJetConjugate_derivative]
  rfl

theorem insertZero_conjugate {dimension : ℕ} (parameters : PhaseParameters)
    (family : AxisSmoothCore parameters dimension) :
    cartesianCoreConjugation parameters (insertZero family) =
      insertZero (axisCoreInvolution parameters dimension family) := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianPhysicalConjugation dimension
    (profileScalarZero (-cell) point.1 • family.1 (-cell)) =
    profileScalarZero cell point.1 • cartesianPhysicalConjugation dimension (family.1 (-cell))
  rw [(cartesianPhysicalConjugation dimension).map_smul]
  simp only [profileScalarZero, cellFrequency_neg]

theorem insertOne_conjugate {dimension : ℕ} (parameters : PhaseParameters)
    (direction : Fin 2) (family : AxisSmoothCore parameters dimension) :
    cartesianCoreConjugation parameters (insertOne direction family) =
      insertOne direction (axisCoreInvolution parameters dimension family) := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianPhysicalConjugation dimension
    (profileScalarOne direction (-cell) point.1 • family.1 (-cell)) =
    profileScalarOne direction cell point.1 • cartesianPhysicalConjugation dimension (family.1 (-cell))
  rw [(cartesianPhysicalConjugation dimension).map_smul]
  simp only [profileScalarOne, cellFrequency_neg]

/-- The actual axis first-jet projection commutes with cell-reversing conjugation. -/
theorem axisJetProjection_conjugate {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (axisJetProjection field) =
      axisJetProjection (cartesianCoreConjugation parameters field) := by
  simp only [axisJetProjection_apply, map_sub, map_add, insertZero_conjugate,
    insertOne_conjugate, traceZero_conjugate, traceFirst_conjugate]

end Grad.CompletedReality
