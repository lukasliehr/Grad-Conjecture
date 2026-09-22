import AKCX54ActualOriginalNativeAllSpatialGrades

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.CartesianUncompressed Grad.GenericCarriers
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.Compensated

/-- A single original B10 ball gives both the accepted startup rows and the
true covector principal tensor bounds at EVERY rank, retaining the SAME gauge bound needed by native recovery.
The ball is fixed before the scale, state, source, cell power and rank. -/
theorem actualOriginalB10AllRankPrincipalGauge (parameters : PhaseParameters)
    (L radius primitiveThreshold rowThreshold tensorThreshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius)
    (primitivePositive : 0 < primitiveThreshold) (rowPositive : 0 < rowThreshold) (tensorPositive : 0 < tensorThreshold) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3, physicalBudget parameters base rho epsilon 10 < lowRadius →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ primitiveThreshold ∧
            ∃ inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation),
              ActualLedgerReduction ledger inverseCoherent ∧ ActualGenuineStartupRowsSmall ledger inverseCoherent rowThreshold ∧
              (∀ (rank : ℕ) (outer inner : Fin 2),
                ‖(StartupRankOperator.principalTensor admissible rank ledger.val ledger.property.1 inverseCoherent outer inner).coarse‖ < tensorThreshold ∧
                ‖(StartupRankOperator.principalTensor admissible rank ledger.val ledger.property.1 inverseCoherent outer inner).fine‖ < tensorThreshold) ∧
              ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
                physicalBudget parameters base rho epsilon 6 ≤ 1 ∧
                (∀ grade, ‖ledger.val.gaugeDeviation grade‖ ≤ constants grade * physicalBudget parameters base rho epsilon (grade+4)) ∧
                physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants := by
  obtain ⟨ledgerRadius, ledgerPositive, ledgerOne, four, five, fourNonnegative, fiveNonnegative, supplied⟩ :=
    actualLedger parameters L radius primitiveThreshold positive radiusNonnegative primitivePositive
  let rowConstant := startupGenuineRowsConstant L parameters.sigma0 parameters.gamma four five
  let tensorConstant := StartupRankOperator.principalBudget L parameters.sigma0 parameters.gamma four five
  have rowNonnegative : 0 ≤ rowConstant := startupGenuineRowsConstant_nonnegative _ _ _ _ _
  have tensorNonnegative : 0 ≤ tensorConstant := StartupRankOperator.principalBudget_nonnegative _ _ _ _ _
  have rowDenominator : 0 < rowConstant + 1 := by positivity
  have tensorDenominator : 0 < tensorConstant + 1 := by positivity
  let lowRadius := min ledgerRadius (min (determinantLowRadius four)
    (min (rowThreshold / (rowConstant + 1)) (tensorThreshold / (tensorConstant + 1))))
  have lowPositive : 0 < lowRadius := lt_min ledgerPositive
    (lt_min (determinantLowRadius_positive four)
      (lt_min (div_pos rowPositive rowDenominator) (div_pos tensorPositive tensorDenominator)))
  refine ⟨lowRadius, lowPositive, (min_le_left _ _).trans ledgerOne, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  have lowLedger : physicalBudget parameters base rho epsilon 10 < ledgerRadius := low.trans_le (min_le_left _ _)
  have lowDeterminant : physicalBudget parameters base rho epsilon 10 < determinantLowRadius four :=
    low.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have lowRows : physicalBudget parameters base rho epsilon 10 < rowThreshold / (rowConstant + 1) :=
    low.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have lowTensor : physicalBudget parameters base rho epsilon 10 < tensorThreshold / (tensorConstant + 1) :=
    low.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have unitTen := lowLedger.le.trans ledgerOne
  have lowSix := physicalBudget_monotone parameters base rho epsilon (by norm_num : 6 ≤ 10)
  have unitSix := lowSix.trans unitTen
  have rhoSmall : |rho| ≤ 1 := by
    unfold physicalBudget at unitSix
    have nonnegative := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg epsilon]
  have epsilonSmall : |epsilon| ≤ 1 := by
    unfold physicalBudget at unitSix
    have nonnegative := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 base
    linarith [abs_nonneg rho]
  obtain ⟨ledger, primitive, ledgerBounds⟩ := supplied ell rho alpha delta parameter epsilon admissible
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall base (lowSix.trans lowLedger.le)
  have gaugeBound (grade : ℕ) : ‖ledger.val.gaugeDeviation grade‖ ≤
      four grade * physicalBudget parameters base rho epsilon (grade + 4) :=
    (actualGaugeDeviation_bound ledger grade).trans (ledgerBounds grade).1
  have coherent : FamilyCoherent ledger.val.gaugeDeviation := ledger.property.1.2.2.2.1
  have inverseCoherent := (determinantInverse_estimate parameters admissible base rho epsilon ledger.val.gaugeDeviation coherent
    four fourNonnegative unitSix gaugeBound (lowSix.trans lowDeterminant.le)).actualCoherent
  have laws := fun grade => actualProjectionLaws_of_ledger_bounds parameters admissible base rho epsilon ledger.val.gaugeDeviation
    coherent four fourNonnegative unitSix gaugeBound (lowSix.trans lowDeterminant.le) grade
  have rowsSmall := actualGenuineStartupRowsSmall_of_budget ledger four five fourNonnegative fiveNonnegative ledgerBounds
    unitTen (lowSix.trans lowDeterminant.le) inverseCoherent rowThreshold lowRows
  refine ⟨ledger, primitive, inverseCoherent, actualLedgerReduction_of_projection ledger inverseCoherent laws, rowsSmall, ?_, four, fourNonnegative, unitSix, gaugeBound, lowSix.trans lowDeterminant.le⟩
  intro rank outer inner
  have bound := StartupRankOperator.actual_principalTensor_bound ledger four five fourNonnegative fiveNonnegative ledgerBounds
    unitTen (lowSix.trans lowDeterminant.le) inverseCoherent rank outer inner
  have payment : tensorConstant * physicalBudget parameters base rho epsilon 10 < tensorThreshold := by
    have budgetPositive := physicalBudget_nonnegative parameters base rho epsilon 10
    have paid := (lt_div_iff₀ tensorDenominator).mp lowTensor
    nlinarith
  exact ⟨(StartupRankOperator.principalTensor admissible rank ledger.val ledger.property.1 inverseCoherent outer inner).coarse_bound.trans_lt
      (bound.trans_lt payment),
    (StartupRankOperator.principalTensor admissible rank ledger.val ledger.property.1 inverseCoherent outer inner).fine_bound.trans_lt
      (bound.trans_lt payment)⟩

end Grad.CartesianStartup
