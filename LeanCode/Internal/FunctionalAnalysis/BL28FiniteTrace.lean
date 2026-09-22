import BL27BoundaryDensity

noncomputable section

open Set
open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem finiteBoundaryJet_coefficient {dimension : ℕ} (cell : ℤ)
    (values : ℤ →₀ ComplexEuclidean dimension) (frequency : ℤ) :
    fourierCoeff (fun angle : CellCircle =>
      (finiteBoundaryJet cell values.support values).value (boundaryDiskPoint angle)) frequency = values frequency := by
  have boundaryLaw (angle : CellCircle) :
      (finiteBoundaryJet cell values.support values).value (boundaryDiskPoint angle) =
        ∑ mode ∈ values.support, fourier mode angle • values mode := by
    change (∑ mode ∈ values.support, boundaryKernel (mode, cell) (boundaryCirclePoint angle) • values mode) = _
    simp_rw [boundaryKernel_boundary]
  simp_rw [boundaryLaw]
  rw [finiteFourier_coefficient]
  by_cases member : frequency ∈ values.support
  · rw [if_pos member]
  · have zeroValue : values frequency = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using member
    rw [if_neg member, zeroValue]

theorem finiteLiftLinear_boundary_coefficient {dimension : ℕ} (parameters : PhaseParameters)
    (values : FiniteBoundaryData dimension) (mode : ℤ × ℤ) :
    originalBoundaryCoefficient parameters (finiteLiftLinear parameters dimension values) mode = values mode.2 mode.1 := by
  unfold originalBoundaryCoefficient
  rw [finiteLiftLinear_cell, angularFiniteJetLinear_eq]
  exact finiteBoundaryJet_coefficient mode.2 (values mode.2) mode.1

theorem finiteLiftLinear_completed_trace {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (values : FiniteBoundaryData dimension) :
    completedTrace parameters grade gradePositive
      (aGradeEta parameters (GradeCore.ofCoreLinear (finiteLiftLinear parameters dimension values))) =
        finiteBoundaryToGrade parameters grade gradePositive values := by
  apply Subtype.ext
  funext mode
  rw [← boundary_weighted_coefficient parameters grade
    (completedTrace parameters grade gradePositive
      (aGradeEta parameters (GradeCore.ofCoreLinear (finiteLiftLinear parameters dimension values)))) mode,
    ← boundary_weighted_coefficient parameters grade (finiteBoundaryToGrade parameters grade gradePositive values) mode,
    completedTrace_coefficient, finiteBoundaryToGrade_coefficient]
  change (boundaryWeight parameters grade mode : ℂ) •
    originalBoundaryCoefficient parameters (finiteLiftLinear parameters dimension values) mode = _
  rw [finiteLiftLinear_boundary_coefficient]

end Grad.BoundaryLift
