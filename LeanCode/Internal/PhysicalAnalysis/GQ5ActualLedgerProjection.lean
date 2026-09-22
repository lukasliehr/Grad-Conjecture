import GQ2ActualRanges

noncomputable section

set_option maxHeartbeats 1800000

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

/-- AO17–19 on the actual original AP2 completion, not a compensated
graph and not a replacement for its missing differential constraints. -/
structure ActualProjectionLaws {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) : Prop where
  idempotent : ∀ field, apCurrentProjection admissible gauge grade
    (apCurrentProjection admissible gauge grade field) = apCurrentProjection admissible gauge grade field
  range : LinearMap.range (apCurrentProjection admissible gauge grade).toLinearMap =
    LinearMap.ker (apGaugeMap admissible gauge grade).toLinearMap
  kernel : LinearMap.ker (apCurrentProjection admissible gauge grade).toLinearMap =
    apComplementRange L sigma gamma ell grade
  circleRight : ∀ field, apCurrentProjection admissible gauge grade
    (apCircleProjection L sigma gamma ell grade field) = apCurrentProjection admissible gauge grade field
  circleLeft : ∀ field, apCircleProjection L sigma gamma ell grade
    (apCurrentProjection admissible gauge grade field) = apCircleProjection L sigma gamma ell grade field
  rangeInverse : ∃ equivalence :
      LinearMap.range (apCircleProjection L sigma gamma ell grade).toLinearMap ≃L[ℂ]
        LinearMap.range (apCurrentProjection admissible gauge grade).toLinearMap,
    (∀ field, (equivalence field).val = apCurrentProjection admissible gauge grade field.val) ∧
    (∀ field, (equivalence.symm field).val = apCircleProjection L sigma gamma ell grade field.val)

theorem actualProjectionLaws_of_ledger_bounds {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (base : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters base rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters base rho epsilon (grade + 4))
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants) (grade : ℕ) :
    ActualProjectionLaws admissible gauge grade where
  idempotent := apCurrentProjection_idempotent parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade
  range := apCurrentProjection_range parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade
  kernel := apCurrentProjection_kernel parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade
  circleRight := apCurrentProjection_circle_right parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade
  circleLeft := apCurrentProjection_circle_left parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade
  rangeInverse := ⟨apRangeEquivalence parameters admissible base rho epsilon gauge coherent constants nonnegative low bound small grade,
    fun _ => rfl, fun _ => rfl⟩

/-- Exact current physical GC17 ledger, one low neighborhood, all original
cells, widths, seed parameters and grades. No complement inverse is a premise. -/
def ActualGaugeProjectionGoal (parameters : PhaseParameters) (L radius threshold : ℝ) : Prop :=
  ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
    ∀ (ell rho alpha delta parameter epsilon : ℝ)
      (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
      |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
      ∀ base : ACore parameters 3,
        physicalBudget parameters base rho epsilon 10 < lowRadius →
        physicalBudget parameters base rho epsilon 12 ≤ 1 →
        ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
          primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
          ∀ grade, ActualProjectionLaws admissible ledger.val.gaugeDeviation grade

theorem actualGaugeProjection (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualGaugeProjectionGoal parameters L radius threshold := by
  obtain ⟨ledgerRadius, ledgerRadiusPositive, ledgerRadiusOne, gaugeConstants, higherConstants,
    gaugeConstantsNonnegative, _, supplied⟩ := actualLedger parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨min ledgerRadius (determinantLowRadius gaugeConstants),
    lt_min ledgerRadiusPositive (determinantLowRadius_positive gaugeConstants),
    (min_le_left _ _).trans ledgerRadiusOne, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low _bounded
  have lowSix := (physicalBudget_monotone parameters base rho epsilon (by norm_num : 6 ≤ 10)).trans low.le
  have ledgerSmall := lowSix.trans (min_le_left _ _)
  have determinantSmall := lowSix.trans (min_le_right _ _)
  have unitSmall := ledgerSmall.trans ledgerRadiusOne
  have rhoSmall : |rho| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg epsilon]
  have epsilonSmall : |epsilon| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg rho]
  obtain ⟨ledger, primitiveMargin, ledgerBounds⟩ := supplied ell rho alpha delta parameter epsilon admissible
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall base ledgerSmall
  have gaugeBound (grade : ℕ) : ‖ledger.val.gaugeDeviation grade‖ ≤
      gaugeConstants grade * physicalBudget parameters base rho epsilon (grade + 4) :=
    (actualGaugeDeviation_bound ledger grade).trans (ledgerBounds grade).1
  have gaugeCoherent : FamilyCoherent ledger.val.gaugeDeviation := ledger.property.1.2.2.2.1
  exact ⟨ledger, primitiveMargin, fun grade => actualProjectionLaws_of_ledger_bounds parameters admissible base rho epsilon _
    gaugeCoherent gaugeConstants gaugeConstantsNonnegative unitSmall gaugeBound determinantSmall grade⟩

end Grad.GaugeCoefficients.Physical.GaugeTransfer
