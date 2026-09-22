import AKDP28UniformActualMatrixRank

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupUniformOriginalRank

/-- The literal current formula uses the same original full-gauge,
complement and extension factors. Its quantitative profile is uniform in
the entire coefficient state. -/
theorem current {State : Type*} (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0) (offset rank : ℕ)
    (gaugeProfile extensionProfile : EstimateProfile)
    (gaugeFixed : ∀ grade,0≤gaugeProfile.fixed grade) (gaugeDeviation : ∀ grade,0≤gaugeProfile.deviation grade)
    (extensionFixed : ∀ grade,0≤extensionProfile.fixed grade) (extensionDeviation : ∀ grade,0≤extensionProfile.deviation grade)
    (baseField : State → ACore parameters 3) (rho curvature : State → ℝ)
    (gauge : State → CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : ∀ state,FamilyCoherent (gauge state))
    (inverseCoherent : ∀ state,FamilyCoherent (determinantInverseFamily admissible (gauge state)))
    (gaugeEstimate : ∀ state,FamilyEstimate parameters (baseField state) (rho state) (curvature state) offset gaugeProfile
      (fullGaugeFamily (gauge state)) (identityFamily L parameters.sigma0 parameters.gamma ell 3))
    (extensionEstimate : ∀ state,FamilyEstimate parameters (baseField state) (rho state) (curvature state) offset extensionProfile
      (complementExtensionFamily admissible (gauge state)) (identityFamily L parameters.sigma0 parameters.gamma ell 3))
    (low : ∀ state,physicalBudget parameters (baseField state) (rho state) (curvature state) offset≤1) :
    StartupUniformOriginalRank parameters
      (fun state => 1+physicalBudget parameters (baseField state) (rho state) (curvature state) (offset+rank))
      (fun state => originalCurrentKernel admissible (gauge state) (coherent state) (inverseCoherent state))
      (fun state => (StartupRankOperator.current admissible rank (gauge state) (coherent state) (inverseCoherent state)).coarse) := by
  let budget := fun state => 1+physicalBudget parameters (baseField state) (rho state) (curvature state) (offset+rank)
  have budgetNonnegative (state : State) : 0≤budget state :=
    add_nonneg zero_le_one (physicalBudget_nonnegative parameters (baseField state) (rho state) (curvature state) _)
  have fullGauge := matrix (rank := rank) admissible lengthNonzero scaleNonzero offset gaugeProfile gaugeFixed gaugeDeviation
    baseField rho curvature (fun state => fullGaugeFamily (gauge state)) (fun _ => identityFamily _ _ _ _ 3) gaugeEstimate low
  have extension := matrix (rank := rank) admissible lengthNonzero scaleNonzero offset extensionProfile extensionFixed extensionDeviation
    baseField rho curvature (fun state => complementExtensionFamily admissible (gauge state)) (fun _ => identityFamily _ _ _ _ 3) extensionEstimate low
  have fixed := (StartupSpatialAction.complement_originalRankControlled (L := L) (ell := ell) parameters rank).onBudget budget budgetNonnegative
  have complement := fixed.comp fullGauge (StartupRankOperator.complement rank).bound
    (StartupRankOperator.complement rank).nonnegative (fun _ => (StartupRankOperator.complement rank).coarse_bound) budgetNonnegative
  have extended := extension.comp complement (startupMatrixProfileBaseBound L parameters.sigma0 parameters.gamma extensionProfile)
    (startupMatrixProfileBaseBound_nonnegative admissible extensionProfile extensionFixed extensionDeviation)
    (matrix_rankBound admissible extensionEstimate low) budgetNonnegative
  exact (identity 3 rank budgetNonnegative).sub extended

end StartupUniformOriginalRank
end Grad.CartesianStartup
