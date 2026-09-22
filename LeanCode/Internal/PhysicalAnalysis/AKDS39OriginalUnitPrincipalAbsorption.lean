import AKDS38OriginalUnitPrincipalBudget
import AKDM1ActualPrincipalAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 4000
open scoped ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.SourceCollarCoefficients Grad.CartesianStartup
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.PDEBootstrap

def originalUnitLocalizedConstant (parameters : PhaseParameters) (length radius : ℝ)
    (scalar : Spatial→ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar) : ℝ :=
  4*‖startupCutoffL2 scalar smooth compact‖*
    StartupRankOperator.principalBudget 1 parameters.sigma0 parameters.gamma
      (originalUnitFour parameters length radius) (originalUnitFive parameters length)

theorem originalUnitLocalizedConstant_nonnegative (parameters : PhaseParameters) (length radius : ℝ)
    (scalar : Spatial→ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar) :
    0≤originalUnitLocalizedConstant parameters length radius scalar smooth compact :=
  mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (StartupRankOperator.principalBudget_nonnegative _ _ _ _ _)

/-- One positive, rank-independent radius for the literal original-L
localized principal, selected before the physical state and source. -/
def originalUnitPrincipalRadius (parameters : PhaseParameters) (length radius : ℝ)
    (scalar : Spatial→ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar) : ℝ :=
  min (originalUnitRankRadius parameters length radius)
    (1/(8*(originalUnitLocalizedConstant parameters length radius scalar smooth compact+1)))

theorem originalUnitPrincipalRadius_positive (parameters : PhaseParameters) (length radius : ℝ)
    (scalar : Spatial→ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar) :
    0<originalUnitPrincipalRadius parameters length radius scalar smooth compact :=
  lt_min (originalUnitRankRadius_positive parameters length radius)
    (one_div_pos.mpr (mul_pos (by norm_num) (by linarith [originalUnitLocalizedConstant_nonnegative parameters length radius scalar smooth compact])))

theorem originalUnitPrincipalRadius_le (parameters : PhaseParameters) (length radius : ℝ)
    (scalar : Spatial→ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar) :
    originalUnitPrincipalRadius parameters length radius scalar smooth compact≤originalUnitRankRadius parameters length radius := min_le_left _ _

namespace OriginalUnitRankState
variable {parameters : PhaseParameters} {length radius : ℝ}

theorem localized_principal_oneEighth (radiusNonnegative : 0≤radius)
    (state : OriginalUnitRankState parameters length radius)
    (scalar : Spatial→ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (small : physicalBudget parameters state.field state.rho state.epsilon 10<
      originalUnitPrincipalRadius parameters length radius scalar smooth compact) (rank : ℕ) :
    ‖startupRankPrincipalCoarse
      (fun index => StartupRankOperator.principalTensor (unitDiskAdmissible parameters) rank state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) index.1 index.2)
      scalar smooth compact‖ < (1/8:ℝ) := by
  let coefficient := StartupRankOperator.principalBudget 1 parameters.sigma0 parameters.gamma
    (originalUnitFour parameters length radius) (originalUnitFive parameters length)
  let budget := physicalBudget parameters state.field state.rho state.epsilon 10
  let constant := originalUnitLocalizedConstant parameters length radius scalar smooth compact
  have bounded := startupRankPrincipalCoarse_norm
    (fun index => StartupRankOperator.principalTensor (unitDiskAdmissible parameters) rank state.data
      (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) index.1 index.2)
    scalar smooth compact (coefficient*budget)
    (fun index => (StartupRankOperator.principalTensor (unitDiskAdmissible parameters) rank state.data
      (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) index.1 index.2).coarse_bound.trans
        (state.principal_bound radiusNonnegative rank index.1 index.2))
  have paid : ‖startupRankPrincipalCoarse
      (fun index => StartupRankOperator.principalTensor (unitDiskAdmissible parameters) rank state.data
        (state.coherent radiusNonnegative) (state.inverseCoherent radiusNonnegative) index.1 index.2)
      scalar smooth compact‖≤constant*budget := bounded.trans_eq (by dsimp only [constant,originalUnitLocalizedConstant,coefficient]; ring)
  have constant0 : 0≤constant := originalUnitLocalizedConstant_nonnegative parameters length radius scalar smooth compact
  have budget0 : 0≤budget := physicalBudget_nonnegative _ _ _ _ _
  have low : budget<1/(8*(constant+1)) := small.trans_le (min_le_right _ _)
  have denominator : 0<8*(constant+1) := by positivity
  have allocated := (lt_div_iff₀ denominator).mp low
  have strict : constant*budget<(1/8:ℝ) := by nlinarith only [allocated,budget0]
  exact paid.trans_lt strict

end OriginalUnitRankState
end Grad.OriginalCoreRealization
