import AFZ4DefectBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

/-- The existing exact R isometry, preceded by the original high projection. -/
def strongAngularLift (L sigma gamma ell : ℝ) (grade : ℕ) :
    APBoundaryGrade L sigma gamma ell 1 (grade + 1) →L[ℂ] StrongMatchingGrade L sigma gamma ell grade :=
  (highAngularIsometry L sigma gamma ell grade).toLinearIsometry.toContinuousLinearMap.comp
    (highBoundaryProjection L sigma gamma ell (grade + 1))

theorem strongAngularLift_norm (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) :
    ‖strongAngularLift L sigma gamma ell grade field‖ =
      ‖apHighProjection L sigma gamma ell (grade + 1) field‖ :=
  (highAngularIsometry L sigma gamma ell grade).norm_map _

theorem strongAngularLift_high (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) :
    strongAngularLift L sigma gamma ell grade (apHighProjection L sigma gamma ell (grade + 1) field) =
      strongAngularLift L sigma gamma ell grade field :=
  congrArg (highAngularIsometry L sigma gamma ell grade)
    (Subtype.ext (apHighProjection_idempotent L sigma gamma ell (grade + 1) field))

theorem strongAngularLift_coefficient (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) (mode : ℤ × ℤ) :
    strongMatchingCoefficient L sigma gamma ell grade (strongAngularLift L sigma gamma ell grade field) mode =
      (Complex.I * (mode.1 : ℂ)) • apBoundaryCoefficient L sigma gamma ell (grade + 1)
        (apHighProjection L sigma gamma ell (grade + 1) field) mode :=
  highAngularIsometry_coefficient L sigma gamma ell grade (highBoundaryProjection L sigma gamma ell (grade + 1) field) mode

theorem strongAngularLift_weak (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) :
    strongMatchingWeak L sigma gamma ell grade (strongAngularLift L sigma gamma ell grade field) =
      apHighProjection L sigma gamma ell grade (matchingAngular L sigma gamma ell grade field) :=
  strongMatchingWeak_angular L sigma gamma ell grade field

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

/-- The genuine angular image of the actual physical normal row. -/
def completedStrongNormal (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] StrongMatchingGrade L sigma gamma ell grade :=
  (strongAngularLift L sigma gamma ell grade).comp (completedNormalTrace admissible data grade core)

/-- The actual AR16 defect in the exact AY1 stronger trace target. -/
def completedStrongDefect (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] StrongMatchingGrade L sigma gamma ell grade :=
  (strongAngularLift L sigma gamma ell grade).comp (completedMatchingDefect admissible data grade core)

theorem completedStrongNormal_norm (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedStrongNormal admissible data grade core field‖ =
      ‖completedNormalTrace admissible data grade core field‖ :=
  (strongAngularLift_norm L sigma gamma ell grade (completedNormalTrace admissible data grade core field)).trans
    (congrArg (fun value : APBoundaryGrade L sigma gamma ell 1 (grade + 1) => ‖value‖)
      (completedNormalTrace_high admissible data grade core field))

/-- Exact AY11 signed physical-row law. Both normal and defect are actual
completed traces of the original graph, not new boundary assumptions. -/
theorem completedStrongFlux_physicalRow (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    completedStrongFlux admissible data grade core field =
      -completedStrongNormal admissible data grade core field +
        completedStrongDefect admissible data grade core field := by
  have addition := (strongAngularLift L sigma gamma ell grade).map_add
    (apHighProjection L sigma gamma ell (grade + 1) (completedMatchingP admissible data grade core field))
    (completedNormalTrace admissible data grade core field)
  have first := strongAngularLift_high L sigma gamma ell grade (completedMatchingP admissible data grade core field)
  change completedStrongDefect admissible data grade core field =
    strongAngularLift L sigma gamma ell grade
      (apHighProjection L sigma gamma ell (grade + 1) (completedMatchingP admissible data grade core field)) +
    completedStrongNormal admissible data grade core field at addition
  have total := addition.trans (congrArg (fun value : StrongMatchingGrade L sigma gamma ell grade =>
    value + completedStrongNormal admissible data grade core field) first)
  change completedStrongDefect admissible data grade core field =
    completedStrongFlux admissible data grade core field + completedStrongNormal admissible data grade core field at total
  have transformed := congrArg (fun value : StrongMatchingGrade L sigma gamma ell grade =>
    -completedStrongNormal admissible data grade core field + value) total
  exact (transformed.trans (by abel)).symm

/-- The stronger defect norm is exactly its primitive high boundary norm. -/
theorem completedStrongDefect_norm (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedStrongDefect admissible data grade core field‖ =
      ‖completedMatchingDefect admissible data grade core field‖ :=
  (strongAngularLift_norm L sigma gamma ell grade (completedMatchingDefect admissible data grade core field)).trans
    (congrArg (fun value : APBoundaryGrade L sigma gamma ell 1 (grade + 1) => ‖value‖)
      (completedMatchingDefect_high admissible data grade core field))

theorem completedStrongDefect_bound (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedStrongDefect admissible data grade core field‖ ≤ matchingDefectConstant data grade * ‖field‖ :=
  (completedStrongDefect_norm admissible data grade core field).trans_le
    (completedMatchingDefect_bound admissible data grade core field)

theorem completedStrongDefect_coefficient (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) (mode : ℤ × ℤ) :
    strongMatchingCoefficient L sigma gamma ell grade (completedStrongDefect admissible data grade core field) mode =
      (Complex.I * (mode.1 : ℂ)) • apBoundaryCoefficient L sigma gamma ell (grade + 1)
        (completedMatchingDefect admissible data grade core field) mode :=
  (strongAngularLift_coefficient L sigma gamma ell grade (completedMatchingDefect admissible data grade core field) mode).trans
    (congrArg (fun value : APBoundaryGrade L sigma gamma ell 1 (grade + 1) =>
      (Complex.I * (mode.1 : ℂ)) • apBoundaryCoefficient L sigma gamma ell (grade + 1) value mode)
      (completedMatchingDefect_high admissible data grade core field))

end Grad.GaugeCoefficients.Physical.Compensated
