import AHC8DistributedMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

def DistributedFamilyLaw {L sigma gamma ell : ℝ} {input output : ℕ}
    (admissible : Admissible L sigma gamma ell) (family : CoefficientFamily L sigma gamma ell input output) : Prop :=
  ∀ (grade : ℕ) (field : apGrade L sigma gamma ell input grade),
    ‖apMultiplier admissible (family grade) field‖ ≤
      apDistributedMultiplierConstant L sigma gamma grade *
        ∑ order : Fin (grade + 1), ‖family order.val‖ *
          ‖apLowering L sigma gamma ell (Nat.sub_le grade order.val) field‖

/-- The exact three coefficient families used by cap matching and its
physical-row defect have the distributed original-width multiplier bound. -/
def DistributedLedgerLaws {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell) : Prop :=
  DistributedFamilyLaw admissible data.gaugeDeviation ∧
  DistributedFamilyLaw admissible data.fluxDeviation ∧
  DistributedFamilyLaw admissible data.traceDeviation

theorem distributedLedgerLaws {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data) : DistributedLedgerLaws admissible data :=
  ⟨fun _ field => apMultiplier_distributed_bound admissible data.gaugeDeviation coherent.2.2.2.1 field,
    fun _ field => apMultiplier_distributed_bound admissible data.fluxDeviation coherent.2.2.2.2.1 field,
    fun _ field => apMultiplier_distributed_bound admissible data.traceDeviation coherent.2.2.2.2.2.1 field⟩

/-- The SAME actual low-ball coefficient witness, stronger matching pair,
and signed physical defect now have distributed multiplier estimates. No
cap interpolation or one-high coefficient bound is assumed in this result. -/
theorem actualDistributedMultiplierConsumer (parameters : PhaseParameters) (L radius threshold : ℝ)
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
              PhysicalDefectLaws admissible ledger.val ∧
              DistributedLedgerLaws admissible ledger.val := by
  have result := actualPhysicalDefectConsumer parameters L radius threshold positive radiusNonnegative thresholdPositive
  let lowRadius := result.choose
  have neighborhood := result.choose_spec
  refine ⟨lowRadius, neighborhood.1, neighborhood.2.1, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaBound deltaBound parameterBound base small bounded
  obtain ⟨ledger, primitive, smooth, preservation, strong, defect⟩ :=
    neighborhood.2.2 ell rho alpha delta parameter epsilon admissible alphaBound deltaBound parameterBound base small bounded
  exact ⟨ledger, primitive, smooth, preservation, strong, defect,
    distributedLedgerLaws admissible ledger.val ledger.property.1⟩

end Grad.GaugeCoefficients.Physical.Compensated
