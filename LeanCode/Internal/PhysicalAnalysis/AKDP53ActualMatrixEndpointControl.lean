import AKDP52ActualFixedEndpointFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupUniformOriginalEndpoint
variable {State : Type*} {input output rank : ℕ} {parameters : PhaseParameters} {L ell : ℝ}

theorem identity (dimension rank : ℕ) {budget : State → ℝ} (nonnegative : ∀ state,0≤budget state) :
    StartupUniformOriginalEndpoint parameters budget
      (fun _ => ContinuousLinearMap.id ℂ (StartupL2 dimension))
      (fun _ => ContinuousLinearMap.id ℂ (StartupL2 (startupTensorDimension dimension rank))) :=
  (StartupSpatialAction.identity_originalEndpointControlled (L := 1) (ell := 1) parameters rank dimension).onBudget budget nonnegative

theorem matrix (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0) (offset : ℕ) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade) (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (baseField : State → ACore parameters 3) (rho curvature : State → ℝ)
    (family reference : State → CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
    (estimate : ∀ state,FamilyEstimate parameters (baseField state) (rho state) (curvature state) offset profile (family state) (reference state))
    (low : ∀ state,physicalBudget parameters (baseField state) (rho state) (curvature state) offset≤1) :
    StartupUniformOriginalEndpoint parameters
      (fun state => 1+physicalBudget parameters (baseField state) (rho state) (curvature state) (offset+rank))
      (fun state => originalMatrixKernel admissible (family state) (estimate state).actualCoherent)
      (fun state => (StartupRankOperator.matrix admissible rank (family state) (estimate state).actualCoherent).coarse) := by
  refine ⟨StartupUniformOriginalRank.matrix admissible lengthNonzero scaleNonzero offset profile fixedNonnegative deviationNonnegative
    baseField rho curvature family reference estimate low,?_⟩
  obtain ⟨leading,nonnegative,bound⟩ := startupEstimatedMatrix_cellAdjustable parameters admissible lengthNonzero scaleNonzero
    offset rank profile fixedNonnegative deviationNonnegative
  refine ⟨leading,nonnegative,?_⟩
  intro epsilon positive
  obtain ⟨tail,tailNonnegative,actual⟩ := bound epsilon positive
  refine ⟨tail,tailNonnegative,?_⟩
  intro state core image same
  exact actual input output (baseField state) (rho state) (curvature state) (family state) (reference state) (estimate state)
    core (startupOriginalSignedFamily parameters core L ell) image rfl same (low state)

end StartupUniformOriginalEndpoint
end Grad.CartesianStartup
