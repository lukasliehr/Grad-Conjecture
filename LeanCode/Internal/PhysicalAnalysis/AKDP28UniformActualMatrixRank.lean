import AKDP27ActualFixedFormulaRankControl

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- The coarse matrix rank norm is bounded by the original matrix norm,
without the unnecessary first-graph norm in the bundled bound. -/
theorem startupMatrix_rankCoarse_norm {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ} (rank : ℕ)
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family) :
    ‖(StartupRankOperator.matrix admissible rank family coherent).coarse‖≤‖originalMatrixKernel admissible family coherent‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro field
  have represented := (startupTensorFieldEquiv input rank).apply_symm_apply field
  conv_lhs => rw [← represented]
  rw [StartupRankOperator.matrix,StartupRankOperator.entrywise_coarse,LinearIsometryEquiv.norm_map]
  exact (hilbertLiftLinear_norm_le _ _).trans_eq (by rw [LinearIsometryEquiv.norm_map])

namespace StartupUniformOriginalRank
variable {State : Type*} {input output rank : ℕ} {parameters : PhaseParameters} {L ell : ℝ}

theorem matrix (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0) (offset : ℕ) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade) (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (baseField : State → ACore parameters 3) (rho curvature : State → ℝ)
    (family reference : State → CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
    (estimate : ∀ state,FamilyEstimate parameters (baseField state) (rho state) (curvature state) offset profile (family state) (reference state))
    (low : ∀ state,physicalBudget parameters (baseField state) (rho state) (curvature state) offset≤1) :
    StartupUniformOriginalRank parameters
      (fun state => 1+physicalBudget parameters (baseField state) (rho state) (curvature state) (offset+rank))
      (fun state => originalMatrixKernel admissible (family state) (estimate state).actualCoherent)
      (fun state => (StartupRankOperator.matrix admissible rank (family state) (estimate state).actualCoherent).coarse) := by
  obtain ⟨controlled,bound⟩ := startupOriginalMatrix_rankControl parameters admissible lengthNonzero scaleNonzero
    offset rank profile fixedNonnegative deviationNonnegative
  exact ⟨controlled,fun state => bound input output (baseField state) (rho state) (curvature state)
    (family state) (reference state) (estimate state) (low state)⟩

theorem matrix_rankBound (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    {offset : ℕ} {profile : EstimateProfile} {baseField : State → ACore parameters 3} {rho curvature : State → ℝ}
    {family reference : State → CoefficientFamily L parameters.sigma0 parameters.gamma ell input output}
    (estimate : ∀ state,FamilyEstimate parameters (baseField state) (rho state) (curvature state) offset profile (family state) (reference state))
    (low : ∀ state,physicalBudget parameters (baseField state) (rho state) (curvature state) offset≤1) :
    ∀ state,‖(StartupRankOperator.matrix admissible rank (family state) (estimate state).actualCoherent).coarse‖ ≤
      startupMatrixProfileBaseBound L parameters.sigma0 parameters.gamma profile := fun state =>
  (startupMatrix_rankCoarse_norm admissible rank (family state) (estimate state).actualCoherent).trans
    (startupEstimatedMatrix_lowNorm parameters admissible (estimate state) (low state))

end StartupUniformOriginalRank
end Grad.CartesianStartup
