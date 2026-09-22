import AFZ3PhysicalDefectCoefficients
import AFZ5StrongPhysicalRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

/-- Exact physical-row defect laws, on the original native graph at every
grade and before specializing its closed core to an actual current gauge. -/
def PhysicalDefectLaws {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell) : Prop :=
  ∀ (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core),
    completedMatchingDefect admissible data grade core field =
      apHighTrace L sigma gamma ell (grade + 1) (by omega)
        (completedMatchingDefectBulk admissible data grade core field) ∧
    completedStrongFlux admissible data grade core field =
      -completedStrongNormal admissible data grade core field + completedStrongDefect admissible data grade core field ∧
    ‖completedStrongDefect admissible data grade core field‖ =
      ‖completedMatchingDefect admissible data grade core field‖ ∧
    ‖completedStrongDefect admissible data grade core field‖ ≤ matchingDefectConstant data grade * ‖field‖ ∧
    ∀ mode : ℤ × ℤ,
      strongMatchingCoefficient L sigma gamma ell grade (completedStrongDefect admissible data grade core field) mode =
        (Complex.I * (mode.1 : ℂ)) • apBoundaryCoefficient L sigma gamma ell (grade + 1)
          (completedMatchingDefect admissible data grade core field) mode

theorem physicalDefectCompletedLaws {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell) :
    PhysicalDefectLaws admissible data := by
  intro grade core field
  exact ⟨completedMatchingDefect_formula admissible data grade core field,
    completedStrongFlux_physicalRow admissible data grade core field,
    completedStrongDefect_norm admissible data grade core field,
    completedStrongDefect_bound admissible data grade core field,
    completedStrongDefect_coefficient admissible data grade core field⟩

/-- The SAME physical low-ball witness and completed stronger matching map
now carry the actual signed AR16/AY11 defect, without any assumed boundary
row, inverse, discarded cross term, or cap-cell support restriction. -/
theorem actualPhysicalDefectConsumer (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3,
          physicalBudget parameters base rho epsilon 10 < lowRadius →
          physicalBudget parameters base rho epsilon 12 ≤ 1 →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
            ∃ smooth : SmoothCompensatedCoreIsomorphism admissible ledger.val.gaugeDeviation,
              ScalarTracePreservation admissible ledger.val smooth ∧
              StrongMatchingLaws admissible ledger.val ledger.property.1 smooth ∧
              PhysicalDefectLaws admissible ledger.val := by
  have result := actualStrongMatchingConsumer parameters L radius threshold positive radiusNonnegative thresholdPositive
  let lowRadius := result.choose
  have neighborhood := result.choose_spec
  refine ⟨lowRadius, neighborhood.1, neighborhood.2.1, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaBound deltaBound parameterBound base small bounded
  obtain ⟨ledger, primitive, smooth, preservation, strong⟩ :=
    neighborhood.2.2 ell rho alpha delta parameter epsilon admissible alphaBound deltaBound parameterBound base small bounded
  exact ⟨ledger, primitive, smooth, preservation, strong,
    physicalDefectCompletedLaws (L := L) (sigma := parameters.sigma0)
      (gamma := parameters.gamma) (ell := ell) admissible ledger.val⟩

end Grad.GaugeCoefficients.Physical.Compensated
