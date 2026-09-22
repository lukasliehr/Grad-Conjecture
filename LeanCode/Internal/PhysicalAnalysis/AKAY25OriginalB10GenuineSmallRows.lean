import AKAY24GenuineSmallRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 3000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.CartesianUncompressed
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.Compensated

/-- One B10 neighborhood before ell, fields and cell grades makes ALL the
 literal ER11 a,c,h,s kernels small simultaneously on L2 and the inherited
 first weak graph. The SAME ledger supplies the full original two-gauge
 Cartesian reduction and corrected full-cell row bounds. This is the actual
 coefficient-smallness part of RB startup, not an assumed tensor equation. -/
theorem actualOriginalB10GenuineSmallRows (parameters : PhaseParameters)
    (L radius primitiveThreshold operatorThreshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius)
    (primitivePositive : 0 < primitiveThreshold) (operatorPositive : 0 < operatorThreshold) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3,
          physicalBudget parameters base rho epsilon 10 < lowRadius →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ primitiveThreshold ∧
            ∃ inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation),
              ActualLedgerReduction ledger inverseCoherent ∧
              ActualGenuineStartupRowsSmall ledger inverseCoherent operatorThreshold := by
  obtain ⟨ledgerRadius, ledgerRadiusPositive, ledgerRadiusOne, four, five,
    fourNonnegative, fiveNonnegative, supplied⟩ :=
    actualLedger parameters L radius primitiveThreshold positive radiusNonnegative primitivePositive
  let rowConstant := startupGenuineRowsConstant L parameters.sigma0 parameters.gamma four five
  have rowNonnegative : 0 ≤ rowConstant := startupGenuineRowsConstant_nonnegative _ _ _ _ _
  have denominatorPositive : 0 < rowConstant + 1 := by positivity
  refine ⟨min ledgerRadius (min (determinantLowRadius four) (operatorThreshold / (rowConstant + 1))),
    lt_min ledgerRadiusPositive (lt_min (determinantLowRadius_positive four)
      (div_pos operatorPositive denominatorPositive)), (min_le_left _ _).trans ledgerRadiusOne, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  have lowSix := (physicalBudget_monotone parameters base rho epsilon (by norm_num : 6 ≤ 10)).trans low.le
  have ledgerSmall := lowSix.trans (min_le_left _ _)
  have determinantSmall := lowSix.trans ((min_le_right _ _).trans (min_le_left _ _))
  have unitSmall := ledgerSmall.trans ledgerRadiusOne
  have unitTen := low.le.trans ((min_le_left _ _).trans ledgerRadiusOne)
  have rhoSmall : |rho| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have nonnegative := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg epsilon]
  have epsilonSmall : |epsilon| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have nonnegative := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg rho]
  obtain ⟨ledger, primitiveMargin, ledgerBounds⟩ := supplied ell rho alpha delta parameter epsilon admissible
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall base ledgerSmall
  have gaugeBound (grade : ℕ) : ‖ledger.val.gaugeDeviation grade‖ ≤
      four grade * physicalBudget parameters base rho epsilon (grade + 4) :=
    (actualGaugeDeviation_bound ledger grade).trans (ledgerBounds grade).1
  have coherent : FamilyCoherent ledger.val.gaugeDeviation := ledger.property.1.2.2.2.1
  have inverseCoherent := (determinantInverse_estimate parameters admissible base rho epsilon ledger.val.gaugeDeviation coherent
    four fourNonnegative unitSmall gaugeBound determinantSmall).actualCoherent
  have laws := fun grade => actualProjectionLaws_of_ledger_bounds parameters admissible base rho epsilon ledger.val.gaugeDeviation
    coherent four fourNonnegative unitSmall gaugeBound determinantSmall grade
  have rowsSmall := actualGenuineStartupRowsSmall_of_budget ledger four five fourNonnegative fiveNonnegative ledgerBounds
    unitTen determinantSmall inverseCoherent operatorThreshold (low.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  exact ⟨ledger, primitiveMargin, inverseCoherent, actualLedgerReduction_of_projection ledger inverseCoherent laws,
    rowsSmall⟩

end Grad.CartesianStartup
