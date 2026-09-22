import AKDP77ActualSignedLowerFluxAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.NonlinearProduct
open Grad.ActualOriginalSourceFirst Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate Grad.SpatialDilation Grad.CellWeights
namespace StartupAdjustableSpatialGraph

theorem signedAxialLower {State : Type*} (parameters : PhaseParameters) (order grade : ℕ) (allocated : order≤grade)
    (cores : State → ACore parameters 3) :
    StartupAdjustableSpatialGraph order (fun state => (originalSourceMoments parameters
      (originalSignedAxialCore parameters (cores state) 1 1 1)).field)
      (fun state => originalGradeNorm (grade+1) (cores state))
      (fun state => originalCellNorm parameters (grade+1) (cores state)) := by
  intro epsilon positive
  obtain ⟨constant,nonnegative,bounded⟩ := startupSignedAxial_lowerGraph_fullAdjustable order grade allocated epsilon positive
  refine ⟨constant,nonnegative,?_⟩
  intro state
  let image := originalSignedAxialCore parameters (cores state) 1 1 1
  let regular := startupOriginal_reservedGraph parameters image (L := 1) (ell := 1) one_ne_zero one_ne_zero order 0
  exact ⟨regular.choose,regular.choose_spec,bounded 3 parameters (cores state) regular.choose regular.choose_spec⟩

theorem signedAxialPhaseFirst {State : Type*} (parameters : PhaseParameters) (scale : Scale)
    (order grade : ℕ) (allocated : order+1≤grade) (direction : Fin 2)
    (cores : State → ACore parameters 3) (moments : State → StartupL2 3)
    (same : ∀ state,StartupRadialRelated (fun cell _ => cellWeight cell) (moments state)
      (originalSourceMoments parameters (originalSignedAxialCore parameters (cores state) 1 1 1)).field) :
    StartupAdjustableSpatialGraph order (fun state => startupScaledPhaseFirstField parameters.sigma0 parameters.gamma scale.val
      parameters.gamma_pos.le scale.property.1.le scale.property.2 direction (moments state))
      (fun state => originalGradeNorm (grade+1) (cores state))
      (fun state => originalCellNorm parameters (grade+1) (cores state)) := by
  intro epsilon positive
  obtain ⟨constant,nonnegative,bounded⟩ := startupSignedAxial_phaseFirst_fullAdjustable parameters scale order grade allocated direction epsilon positive
  refine ⟨constant,nonnegative,?_⟩
  intro state
  let image := originalSignedAxialCore parameters (cores state) 1 1 1
  let regular := startupOriginal_reservedGraph parameters image (L := 1) (ell := 1) one_ne_zero one_ne_zero order (order+1)
  let existsGraph := startupScaledPhaseFirstField_spatialGraph parameters.sigma0 parameters.gamma scale.val parameters.gamma_pos.le
    scale.property.1.le scale.property.2 order direction (originalSourceMoments parameters image).field (moments state) regular (same state)
  exact ⟨existsGraph.choose,existsGraph.choose_spec,bounded (cores state) (moments state) existsGraph.choose (same state) existsGraph.choose_spec⟩

end StartupAdjustableSpatialGraph
end Grad.CartesianStartup
