import AKCG3CoupledRankSecondResolvent
import AKCX55ActualAllRankGaugeBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.TensorBootstrap Grad.GenericCarriers
open Grad.CartesianState Grad.CartesianUncompressed
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

/-- The genuine localized full-cell principal resolvent has a rank-independent
bound. No fine graph or unknown regularity is an input to this estimate. -/
theorem startupRankPrincipalCoarse_norm {rank : ℕ}
    (operators : TensorIndex → StartupRankOperator rank 3 3)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (compact : HasCompactSupport scalar) (bound : ℝ)
    (bounded : ∀ index, ‖(operators index).coarse‖ ≤ bound) :
    ‖startupRankPrincipalCoarse operators scalar smooth compact‖ ≤
      4 * (‖startupCutoffL2 scalar smooth compact‖ * bound) := by
  apply startupFourComposedBound
    (fun index => hilbertLift (Index := DerivativeIndex rank) (startupSecondL2 index))
    (fun index => (operators index).localizedCoarse scalar smooth compact)
    (‖startupCutoffL2 scalar smooth compact‖ * bound)
  · intro index
    exact (hilbertLift_opNorm_le (Index := DerivativeIndex rank) (startupSecondL2 index)).trans
      (startupSecondL2_opNorm index)
  · intro index
    exact ((operators index).localizedCoarse_norm scalar smooth compact).trans
      (mul_le_mul_of_nonneg_left (bounded index) (norm_nonneg _))

/-- One original physical B10 ball makes the actual localized principal
resolvent smaller than one eighth at every rank. The cutoff and the ball are
chosen before the state, source, cell weight and running derivative rank. -/
theorem actualOriginalB10Principal_oneEighth (parameters : PhaseParameters)
    (L radius primitiveThreshold rowThreshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius)
    (primitivePositive : 0 < primitiveThreshold) (rowPositive : 0 < rowThreshold)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (compact : HasCompactSupport scalar) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3, physicalBudget parameters base rho epsilon 10 < lowRadius →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ primitiveThreshold ∧
            ∃ inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation),
              ActualLedgerReduction ledger inverseCoherent ∧
              ActualGenuineStartupRowsSmall ledger inverseCoherent rowThreshold ∧
              (∀ rank : ℕ,
                ‖startupRankPrincipalCoarse
                  (fun index : TensorIndex => StartupRankOperator.principalTensor admissible rank
                    ledger.val ledger.property.1 inverseCoherent index.1 index.2)
                  scalar smooth compact‖ < (1 / 8 : ℝ)) ∧
              ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
                physicalBudget parameters base rho epsilon 6 ≤ 1 ∧
                (∀ grade, ‖ledger.val.gaugeDeviation grade‖ ≤ constants grade *
                  physicalBudget parameters base rho epsilon (grade + 4)) ∧
                physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants := by
  let cutoff := ‖startupCutoffL2 scalar smooth compact‖
  have cutoffNonnegative : 0 ≤ cutoff := norm_nonneg _
  let threshold := 1 / (32 * cutoff + 8)
  have denominator : 0 < 32 * cutoff + 8 := by positivity
  have thresholdPositive : 0 < threshold := one_div_pos.mpr denominator
  obtain ⟨lowRadius, lowPositive, lowOne, supplied⟩ :=
    actualOriginalB10AllRankPrincipalGauge parameters L radius primitiveThreshold rowThreshold
      threshold positive radiusNonnegative primitivePositive rowPositive thresholdPositive
  refine ⟨lowRadius, lowPositive, lowOne, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  obtain ⟨ledger, primitive, inverseCoherent, reduction, rows, bounded, gauge⟩ :=
    supplied ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low
  refine ⟨ledger, primitive, inverseCoherent, reduction, rows, ?_, gauge⟩
  intro rank
  have bound := startupRankPrincipalCoarse_norm
    (fun index : TensorIndex => StartupRankOperator.principalTensor admissible rank
      ledger.val ledger.property.1 inverseCoherent index.1 index.2)
    scalar smooth compact threshold (fun index => (bounded rank index.1 index.2).1.le)
  have paid : 4 * (cutoff * threshold) < (1 / 8 : ℝ) := by
    dsimp only [threshold]
    rw [show 4 * (cutoff * (1 / (32 * cutoff + 8))) =
      (4 * cutoff) / (32 * cutoff + 8) by ring]
    apply (div_lt_iff₀ denominator).mpr
    linarith
  exact bound.trans_lt paid

end Grad.CartesianStartup
