import GQ9PhysicalGaugeConsumer
import GQ12CompletedAngularAction

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

theorem storedQuarterMap_coordinates (value : ComplexEuclidean 3) :
    storedQuarterMap value = WithLp.toLp 2 ![-value 1, value 0, 0] := rfl

theorem ActualProjectionLaws.removed_mem {L sigma gamma ell : ℝ}
    {admissible : Admissible L sigma gamma ell} {gauge : CoefficientFamily L sigma gamma ell 3 3} {grade : ℕ}
    (laws : ActualProjectionLaws admissible gauge grade) (field : apGrade L sigma gamma ell 3 grade) :
    field - apCurrentProjection admissible gauge grade field ∈ apComplementRange L sigma gamma ell grade := by
  rw [← laws.kernel]
  change apCurrentProjection admissible gauge grade (field - apCurrentProjection admissible gauge grade field) = 0
  rw [map_sub, laws.idempotent, sub_self]

theorem ActualProjectionLaws.gauge_zero {L sigma gamma ell : ℝ}
    {admissible : Admissible L sigma gamma ell} {gauge : CoefficientFamily L sigma gamma ell 3 3} {grade : ℕ}
    (laws : ActualProjectionLaws admissible gauge grade) (field : apGrade L sigma gamma ell 3 grade) :
    apGaugeMap admissible gauge grade (apCurrentProjection admissible gauge grade field) = 0 := by
  have member : apCurrentProjection admissible gauge grade field ∈
      LinearMap.range (apCurrentProjection admissible gauge grade).toLinearMap := ⟨field, rfl⟩
  rw [laws.range] at member
  exact member

/-- The extra rotation-graph coordinate of the actual removed field is
controlled without any extra derivative of the input. This is the precise
angular-action consumer needed by the compensated transfer, not that
transfer's still-unconstructed core/closure isomorphism. -/
theorem ActualProjectionLaws.removed_angular {L sigma gamma ell : ℝ}
    {admissible : Admissible L sigma gamma ell} {gauge : CoefficientFamily L sigma gamma ell 3 3} {grade : ℕ}
    (laws : ActualProjectionLaws admissible gauge grade) (field : apGrade L sigma gamma ell 3 grade) :
    let removed := field - apCurrentProjection admissible gauge grade field
    APHasAngularDerivative L sigma gamma ell removed (apStoredQuarter L sigma gamma ell grade removed) ∧
      ‖apStoredQuarter L sigma gamma ell grade removed‖ ≤ ‖removed‖ :=
  ⟨apComplementRange_angular_weak L sigma gamma ell grade _ (laws.removed_mem field),
    apStoredQuarter_bound L sigma gamma ell grade _⟩

def ActualGaugeTransferPrerequisiteGoal (parameters : PhaseParameters) (L radius threshold : ℝ) : Prop :=
  ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
    ∀ (ell rho alpha delta parameter epsilon : ℝ)
      (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
      |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
      ∀ base : ACore parameters 3,
        physicalBudget parameters base rho epsilon 10 < lowRadius →
        physicalBudget parameters base rho epsilon 12 ≤ 1 →
        ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
          primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
          ∀ grade, ActualProjectionLaws admissible ledger.val.gaugeDeviation grade ∧
            ∀ field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade,
              apGaugeMap admissible ledger.val.gaugeDeviation grade
                (apCurrentProjection admissible ledger.val.gaugeDeviation grade field) = 0 ∧
              let removed := field - apCurrentProjection admissible ledger.val.gaugeDeviation grade field
              APHasAngularDerivative L parameters.sigma0 parameters.gamma ell removed
                  (apStoredQuarter L parameters.sigma0 parameters.gamma ell grade removed) ∧
                ‖apStoredQuarter L parameters.sigma0 parameters.gamma ell grade removed‖ ≤ ‖removed‖

theorem actualGaugeTransferPrerequisites (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualGaugeTransferPrerequisiteGoal parameters L radius threshold := by
  obtain ⟨lowRadius, positiveRadius, boundedRadius, supplied⟩ :=
    actualGaugeProjection parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨lowRadius, positiveRadius, boundedRadius, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low bounded
  obtain ⟨ledger, margin, laws⟩ := supplied ell rho alpha delta parameter epsilon admissible
    alphaSmall deltaSmall parameterSmall base low bounded
  exact ⟨ledger, margin, fun grade => ⟨laws grade, fun field =>
    ⟨(laws grade).gauge_zero field, (laws grade).removed_angular field⟩⟩⟩

end Grad.GaugeCoefficients.Physical.GaugeTransfer
