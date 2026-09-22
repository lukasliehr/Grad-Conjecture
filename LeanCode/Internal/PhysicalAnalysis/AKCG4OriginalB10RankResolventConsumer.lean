import AKCG3CoupledRankSecondResolvent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.TensorBootstrap Grad.SobolevBridge Grad.GenericCarriers
open Grad.CartesianState Grad.CartesianUncompressed
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

/-- Rank-uniform SAME-field resolvent prerequisite for the actual differentiated
ER equation. Only its genuine remaining weak identity is an input; no H1
membership or rank-dependent smallness is required. -/
theorem actualOriginalB10RankResolvent (parameters : PhaseParameters)
    (L radius primitiveThreshold rowThreshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius)
    (primitivePositive : 0 < primitiveThreshold) (rowPositive : 0 < rowThreshold)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (included : tsupport scalar ⊆ openUnitDisk) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3, physicalBudget parameters base rho epsilon 10 < lowRadius →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ primitiveThreshold ∧
            ∃ inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation),
              ActualLedgerReduction ledger inverseCoherent ∧ ActualGenuineStartupRowsSmall ledger inverseCoherent rowThreshold ∧
              ∀ (rank : ℕ) (original zeroth : StartupOrderedL2 rank) (flux : Fin 2 → StartupOrderedL2 rank),
                (∀ word : DerivativeIndex rank,
                  Laplacian.laplacian (distributionEmbedding (original word)) =
                    (∑ index : TensorIndex, distributionDerivative index.1
                      (distributionDerivative index.2 (distributionEmbedding
                        ((StartupRankOperator.principalTensor admissible rank ledger.val ledger.property.1 inverseCoherent index.1 index.2).localizedCoarse
                          scalar smooth compact original word)))) +
                      distributionEmbedding (zeroth word) +
                      ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word))) →
                ∃ improved : StartupOrderedH1 rank, startupOrderedValue rank improved = original := by
  let restriction := restrictionMinimalProbe.choose
  have restrictionBase := restrictionMinimalProbe.choose_spec.1
  have restrictionNorm := restrictionMinimalProbe.choose_spec.2
  let extension := (extensionMinimalExistence scalar smooth compact included).choose
  have extensionBase := (extensionMinimalExistence scalar smooth compact included).choose_spec.1
  have extensionNorm := (extensionMinimalExistence scalar smooth compact included).choose_spec.2
  let payment := startupCutoffConstant scalar smooth compact
  have paymentPositive : 0 < payment := startupCutoffConstant_positive scalar smooth compact
  have denominator : 0 < 4 * payment + 1 := by positivity
  have tensorPositive : 0 < 1 / (4 * payment + 1) := div_pos zero_lt_one denominator
  obtain ⟨lowRadius, lowPositive, lowOne, supplied⟩ := actualOriginalB10AllRankPrincipal parameters L radius
    primitiveThreshold rowThreshold (1 / (4 * payment + 1)) positive radiusNonnegative primitivePositive rowPositive tensorPositive
  refine ⟨lowRadius, lowPositive, lowOne, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  obtain ⟨ledger, primitive, inverseCoherent, reduction, rows, bounded⟩ :=
    supplied ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  refine ⟨ledger, primitive, inverseCoherent, reduction, rows, ?_⟩
  intro rank original zeroth flux equation
  let operators := fun index : TensorIndex =>
    StartupRankOperator.principalTensor admissible rank ledger.val ledger.property.1 inverseCoherent index.1 index.2
  have bounds := startupRankPrincipal_bounds operators scalar smooth compact restriction extension restrictionNorm extensionNorm (1 / (4 * payment + 1))
    (fun index => (bounded rank index.1 index.2).1.le) (fun index => (bounded rank index.1 index.2).2.le)
  have coarseCut : ‖startupCutoffL2 scalar smooth compact‖ ≤ payment := by
    unfold payment startupCutoffConstant
    linarith [norm_nonneg (startupCutoffFirst scalar smooth compact)]
  have fineCut : ‖startupCutoffFirst scalar smooth compact‖ ≤ payment := by
    unfold payment startupCutoffConstant
    linarith [norm_nonneg (startupCutoffL2 scalar smooth compact)]
  have paid : 4 * (payment * (1 / (4 * payment + 1))) < 1 := by
    have same : 4 * (payment * (1 / (4 * payment + 1))) = (4 * payment) / (4 * payment + 1) := by ring
    rw [same]
    exact (div_lt_iff₀ denominator).mpr (by linarith)
  have coarseSmall : ‖startupRankPrincipalCoarse operators scalar smooth compact‖ < 1 :=
    bounds.1.trans_lt ((mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right coarseCut tensorPositive.le) (by norm_num : (0 : ℝ) ≤ 4)).trans_lt paid)
  have fineSmall : ‖startupRankPrincipalFine operators restriction extension‖ < 1 :=
    bounds.2.trans_lt ((mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right fineCut tensorPositive.le) (by norm_num : (0 : ℝ) ≤ 4)).trans_lt paid)
  exact startupOrdered_sameField_h1 rank
    (fun index => (operators index).localizedCoarse scalar smooth compact)
    (startupRankPrincipalFine operators restriction extension)
    (startupRankPrincipal_compatible operators scalar smooth compact restriction extension restrictionBase extensionBase) coarseSmall fineSmall original zeroth flux equation

end Grad.CartesianStartup
