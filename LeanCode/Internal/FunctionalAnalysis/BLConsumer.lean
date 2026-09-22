import BLProof

noncomputable section

namespace Grad.BoundaryLift.Consumer

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

/-- Immediate exact consumer: on every positive half-order boundary grade
the accepted completed trace has an explicit bounded right inverse. -/
theorem completed_section_consumer {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    ∃ completed : BoundaryGrade parameters (ComplexEuclidean dimension) grade →L[ℂ]
        AGrade parameters dimension grade,
      (completedTrace parameters grade gradePositive).comp completed =
          ContinuousLinearMap.id ℂ (BoundaryGrade parameters (ComplexEuclidean dimension) grade) ∧
        ‖completed‖ ≤ Real.sqrt (originalLiftCellConstant parameters grade) :=
  ⟨completedBoundaryLift parameters grade gradePositive,
    completedBoundaryLift_trace parameters grade gradePositive,
    completedBoundaryLift_norm_le parameters grade gradePositive⟩

/-- Immediate exact consumer: at the physical boundary circle the lifted
field reproduces the literal double-Fourier series at collar time zero. -/
theorem boundary_circle_physical_consumer {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (angle cellPoint : CellCircle) :
    (originalPhysicalClosedJet parameters (boundaryLift parameters values)).value
        (boundaryDiskPoint angle, cellPoint) =
      literalBoundaryLift values.1 0 angle cellPoint :=
  boundaryLift_physical_value parameters values (boundaryDiskPoint angle) 0 le_rfl
    (by norm_num) angle cellPoint (by rw [sub_zero, one_smul]; rfl)

/-- Immediate exact consumer: high-angular boundary data are fixed by the
five-mode complement projection after the same-grade embedding. -/
theorem highComplementProjection_fixes_high_support {dimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ) (gradePositive : 1 ≤ grade)
    (values : BoundaryCore parameters dimension)
    (highSupport : HighBoundarySupport parameters values) :
    highComplementProjection parameters grade dimension
        (boundaryToGrade parameters grade gradePositive values) =
      boundaryToGrade parameters grade gradePositive values := by
  apply Subtype.ext
  funext mode
  rw [← boundary_weighted_coefficient parameters grade
      (highComplementProjection parameters grade dimension
        (boundaryToGrade parameters grade gradePositive values)) mode,
    ← boundary_weighted_coefficient parameters grade
      (boundaryToGrade parameters grade gradePositive values) mode,
    highComplementProjection_coefficient]
  by_cases small : |mode.1| ≤ 2
  · rw [if_pos small, boundaryToGrade_coefficient, highSupport mode small]
  · rw [if_neg small]

theorem lowAngularModes_abs_le (mode : ℤ) (membership : mode ∈ Grad.Constraints.lowAngularModes) :
    |mode| ≤ 2 := by
  have enumeration : mode = -2 ∨ mode = -1 ∨ mode = 0 ∨ mode = 1 ∨ mode = 2 := by
    simpa [Grad.Constraints.lowAngularModes] using membership
  rcases enumeration with h | h | h | h | h <;> subst h <;> decide

/-- Immediate exact gauge-support consumer: for high-angular boundary data
every lifted cell is fixed by the actual five-mode complement, so both
quadratic gauge integrands of the correction see no low angular mode. -/
theorem boundaryLift_excludedAngular_fixed {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension)
    (highSupport : HighBoundarySupport parameters values) (cell : ℤ) :
    Grad.Constraints.excludedAngularJet Grad.Constraints.lowAngularModes
        ((boundaryLift parameters values).1 cell) =
      (boundaryLift parameters values).1 cell := by
  have selectedZero : Grad.Constraints.selectedAngularJet Grad.Constraints.lowAngularModes
      ((boundaryLift parameters values).1 cell) = 0 := by
    rw [Grad.Constraints.selectedAngularJet_eq]
    apply Finset.sum_eq_zero
    intro mode membership
    exact boundaryLift_high_support parameters values highSupport mode
      (lowAngularModes_abs_le mode membership) cell
  have complementLaw : Grad.Constraints.excludedAngularJet Grad.Constraints.lowAngularModes
      ((boundaryLift parameters values).1 cell) =
      (boundaryLift parameters values).1 cell -
        Grad.Constraints.selectedAngularJet Grad.Constraints.lowAngularModes
          ((boundaryLift parameters values).1 cell) := rfl
  rw [complementLaw, selectedZero, sub_zero]

end Grad.BoundaryLift.Consumer
