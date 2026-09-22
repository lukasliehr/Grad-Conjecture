import ANL13LiteralNormalSeries

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.Constraints
open Grad.CircularHighWeak Grad.OrdinaryDiskCalculus Grad.NonlinearRange
local instance (priority := 2000) consumerUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) consumerBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

/-- The actual reference Robin operator has coefficient 2 on the value trace. -/
theorem normalSmoothLift_robin_coefficient (parameters : PhaseParameters) (data : NormalSmoothBoundary)
    (order : ℕ) (mode : ℤ) :
    fourierCoeff (fun angle : CellCircle =>
      (eulerJet (normalSmoothLift parameters data)).value (boundaryDiskPoint angle) +
        (2 : ℝ) • (normalSmoothLift parameters data).value (boundaryDiskPoint angle)) mode =
          normalBoundaryCoefficient (order + 2) (data.grade order) mode := by
  simp only [normalSmoothLift_boundary, smul_zero, add_zero]
  exact normalSmoothLift_normal_coefficient parameters data order mode

/-- Completed AN22: the constant is chosen before arbitrary boundary data.
The source is the existing circle H^(q-3/2) grade, and the target is ordinary H^q. -/
theorem actualCompletedNormalCoretraction (order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ field : normalBoundaryGrade (order + 2),
      ‖completedNormalLift (order + 2) field‖ ≤ constant * ‖field‖ ∧
      ordinaryBoundaryTrace (order + 2) (by omega) (completedNormalLift (order + 2) field) = 0 ∧
      ordinaryNormalTrace order (completedNormalLift (order + 2) field) = field.val ∧
      ((∀ mode ∈ lowAngularModes, normalBoundaryCoefficient (order + 2) field mode = 0) →
        unitDiskBulk (order + 2) (completedNormalLift (order + 2) field) ∈ highDiskL2) := by
  refine ⟨Real.sqrt (normalSobolevConstant (order + 2)), Real.sqrt_nonneg _, ?_⟩
  intro field
  exact ⟨completedNormalLift_bound (order + 2) (by omega) field,
    completedNormalLift_zero_trace (order + 2) (by omega) field,
    completedNormalLift_normal_trace order field,
    completedNormalLift_high (order + 2) (by omega) field⟩

/-- One smooth actual normal lift, exact at every ordinary grade and with the
literal Robin coefficient and original circle norm; no proposed-lift hypotheses. -/
theorem actualSmoothNormalCoretraction (order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (parameters : PhaseParameters) (data : NormalSmoothBoundary),
      unitDiskCoreInto (order + 2) (normalSmoothLift parameters data) =
        completedNormalLift (order + 2) (data.grade order) ∧
      ‖unitDiskCoreInto (order + 2) (normalSmoothLift parameters data)‖ ≤ constant * ‖data.grade order‖ ∧
      (∀ angle, (normalSmoothLift parameters data).value (boundaryDiskPoint angle) = 0) ∧
      (∀ mode, fourierCoeff (fun angle : CellCircle =>
        (eulerJet (normalSmoothLift parameters data)).value (boundaryDiskPoint angle) +
          (2 : ℝ) • (normalSmoothLift parameters data).value (boundaryDiskPoint angle)) mode =
            normalBoundaryCoefficient (order + 2) (data.grade order) mode) ∧
      ((∀ mode ∈ lowAngularModes, normalBoundaryCoefficient 2 (data.grade 0) mode = 0) →
        closedL2Core (normalSmoothLift parameters data) ∈ highDiskL2) := by
  refine ⟨Real.sqrt (normalSobolevConstant (order + 2)), Real.sqrt_nonneg _, ?_⟩
  intro parameters data
  exact ⟨normalSmoothLift_core parameters data order, normalSmoothLift_bound parameters data order,
    normalSmoothLift_boundary parameters data, normalSmoothLift_robin_coefficient parameters data order,
    normalSmoothLift_high parameters data⟩

end Grad.CircularNormalLift
