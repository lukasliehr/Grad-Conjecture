import AKDP67FiniteAdjustableGraphFormula
import AKDP68LowerGraphsAgainstFullNorm
import AKDP64ActualLowerEndpointTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.NonlinearProduct
open Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate Grad.OriginalCoreRealization
open Grad.SpatialDilation Grad.CellWeights
namespace StartupAdjustableSpatialGraph

theorem originalLower {State : Type*} (parameters : PhaseParameters) (order grade : ℕ) (strict : order<grade)
    (cores : State → ACore parameters 3) :
    StartupAdjustableSpatialGraph order (fun state => (originalSourceMoments parameters (cores state)).field)
      (fun state => originalGradeNorm grade (cores state)) (fun state => originalCellNorm parameters grade (cores state)) := by
  intro epsilon positive
  obtain ⟨constant,nonnegative,bounded⟩ := startupOriginalGraph_lower_fullAdjustable order grade strict epsilon positive
  refine ⟨constant,nonnegative,?_⟩
  intro state
  let existsGraph := startupOriginal_reservedGraph parameters (cores state) (L := 1) (ell := 1) one_ne_zero one_ne_zero order 0
  exact ⟨existsGraph.choose,existsGraph.choose_spec,bounded 3 parameters (cores state) existsGraph.choose existsGraph.choose_spec⟩

theorem phaseFirst {State : Type*} (parameters : PhaseParameters) (scale : Scale) (order grade : ℕ)
    (allocated : order+1≤grade) (direction : Fin 2) (cores : State → ACore parameters 3)
    (moments : State → StartupL2 3)
    (same : ∀ state,StartupRadialRelated (fun cell _ => cellWeight cell) (moments state) (originalSourceMoments parameters (cores state)).field) :
    StartupAdjustableSpatialGraph order (fun state => startupScaledPhaseFirstField parameters.sigma0 parameters.gamma scale.val
      parameters.gamma_pos.le scale.property.1.le scale.property.2 direction (moments state))
      (fun state => originalGradeNorm grade (cores state)) (fun state => originalCellNorm parameters grade (cores state)) := by
  intro epsilon positive
  obtain ⟨constant,nonnegative,bounded⟩ := startupActualPhaseFirst_graph_fullAdjustable parameters scale order grade allocated direction epsilon positive
  refine ⟨constant,nonnegative,?_⟩
  intro state
  let regular := startupOriginal_reservedGraph parameters (cores state) (L := 1) (ell := 1) one_ne_zero one_ne_zero order (order+1)
  let existsGraph := startupScaledPhaseFirstField_spatialGraph parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le
    scale.property.1.le scale.property.2 order direction (originalSourceMoments parameters (cores state)).field (moments state) regular (same state)
  exact ⟨existsGraph.choose,existsGraph.choose_spec,bounded (cores state) (moments state) existsGraph.choose (same state) existsGraph.choose_spec⟩

theorem phaseSecond {State : Type*} (parameters : PhaseParameters) (scale : Scale) (order grade : ℕ)
    (allocated : order+2≤grade) (outer inner : Fin 2) (cores : State → ACore parameters 3)
    (moments : State → StartupL2 3)
    (same : ∀ state,StartupRadialRelated (fun cell _ => cellWeight cell^2) (moments state) (originalSourceMoments parameters (cores state)).field) :
    StartupAdjustableSpatialGraph order (fun state => startupScaledPhaseSecondField parameters.sigma0 parameters.gamma scale.val
      parameters.gamma_pos.le scale.property.1.le scale.property.2 outer inner (moments state))
      (fun state => originalGradeNorm grade (cores state)) (fun state => originalCellNorm parameters grade (cores state)) := by
  intro epsilon positive
  obtain ⟨constant,nonnegative,bounded⟩ := startupActualPhaseSecond_graph_fullAdjustable parameters scale order grade allocated outer inner epsilon positive
  refine ⟨constant,nonnegative,?_⟩
  intro state
  let regular := startupOriginal_reservedGraph parameters (cores state) (L := 1) (ell := 1) one_ne_zero one_ne_zero order (order+2)
  let existsGraph := startupScaledPhaseSecondField_spatialGraph parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le
    scale.property.1.le scale.property.2 order outer inner (originalSourceMoments parameters (cores state)).field (moments state) regular (same state)
  exact ⟨existsGraph.choose,existsGraph.choose_spec,bounded (cores state) (moments state) existsGraph.choose (same state) existsGraph.choose_spec⟩

/-- The checked one-high current/principal endpoint transports every
actual lower graph formula back to its same original input core. -/
theorem transportEndpoint {State : Type*} {parameters : PhaseParameters} {order grade : ℕ}
    {budget : State → ℝ} {kernel : State → StartupL2 3 →L[ℂ] StartupL2 3}
    {ranked : State → StartupL2 (startupTensorDimension 3 grade) →L[ℂ] StartupL2 (startupTensorDimension 3 grade)}
    (actual : StartupUniformOriginalEndpoint parameters budget kernel ranked) (budgetNonnegative : ∀ state,0≤budget state)
    (cores images : State → ACore parameters 3)
    (same : ∀ state,originalSourceFieldLinear parameters (images state)=kernel state (originalSourceFieldLinear parameters (cores state)))
    {field : State → StartupL2 3}
    (lower : StartupAdjustableSpatialGraph order field (fun state => originalGradeNorm grade (images state))
      (fun state => originalCellNorm parameters grade (images state))) :
    StartupAdjustableSpatialGraph order field (fun state => originalGradeNorm grade (cores state))
      (fun state => originalCellNorm parameters grade (cores state)+budget state*originalGradeNorm 0 (cores state)) := by
  intro epsilon positive
  obtain ⟨delta,deltaPositive,transport⟩ := actual.absorbLower budgetNonnegative epsilon positive
  obtain ⟨remainder,remainderNonnegative,lowerBound⟩ := lower delta deltaPositive
  obtain ⟨constant,nonnegative,bounded⟩ := transport remainder remainderNonnegative
  refine ⟨constant,nonnegative,?_⟩
  intro state
  obtain ⟨graph,graphSame,graphBound⟩ := lowerBound state
  exact ⟨graph,graphSame,bounded state (cores state) (images state) ‖graph‖ (same state) graphBound⟩

end StartupAdjustableSpatialGraph
end Grad.CartesianStartup
