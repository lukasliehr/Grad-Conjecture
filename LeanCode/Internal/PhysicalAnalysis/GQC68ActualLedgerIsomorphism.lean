import GQC67CoreIsomorphism

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.GaugeTransfer

/-- CT_GC22 on one B10-small/B12-bounded physical neighborhood, all
original cells, grades, widths, ell, and admitted finite seed parameters. -/
def ActualCompensatedCoreGoal (parameters : PhaseParameters) (L radius threshold : ℝ) : Prop :=
  ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
    ∀ (ell rho alpha delta parameter epsilon : ℝ)
      (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
      |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
      ∀ base : ACore parameters 3,
        physicalBudget parameters base rho epsilon 10 < lowRadius →
        physicalBudget parameters base rho epsilon 12 ≤ 1 →
        ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
          primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
          Nonempty (SmoothCompensatedCoreIsomorphism admissible ledger.val.gaugeDeviation)

theorem actualCompensatedCore (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualCompensatedCoreGoal parameters L radius threshold := by
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
  have coherent : FamilyCoherent ledger.val.gaugeDeviation := ledger.property.1.2.2.2.1
  have inverseCoherent := (determinantInverse_estimate parameters admissible base rho epsilon ledger.val.gaugeDeviation coherent
    gaugeConstants gaugeConstantsNonnegative unitSmall gaugeBound determinantSmall).actualCoherent
  have laws := fun grade => actualProjectionLaws_of_ledger_bounds parameters admissible base rho epsilon ledger.val.gaugeDeviation
    coherent gaugeConstants gaugeConstantsNonnegative unitSmall gaugeBound determinantSmall grade
  have margin := determinant_base_margin parameters admissible base rho epsilon ledger.val.gaugeDeviation coherent
    gaugeConstants gaugeConstantsNonnegative unitSmall gaugeBound determinantSmall
  exact ⟨ledger, primitiveMargin, ⟨smoothCompensatedCoreIsomorphism admissible ledger.val.gaugeDeviation coherent inverseCoherent laws margin⟩⟩

end Grad.GaugeCoefficients.Physical.Compensated
