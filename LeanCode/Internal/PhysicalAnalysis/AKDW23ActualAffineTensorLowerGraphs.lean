import AKDW17AffineLowerEndpointTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.SourceCollarCoefficients Grad.OriginalCoreRealization Grad.OriginalCartesianTameEstimate Grad.SpatialDilation Grad.CellWeights
namespace StartupAdjustableSpatialGraph

variable {State : Type*} (parameters : PhaseParameters) (length radius : ℝ) (radiusNonnegative : 0≤radius)
    (grade : ℕ) (coefficient : State → OriginalUnitRankState parameters length radius)
    (cores images known : State → ACore parameters 3) (outer inner : Fin 2)
    (same : ∀ state,originalSourceFieldLinear parameters (images state)=
      startupGenuinePrincipalTensorKernel (unitDiskAdmissible parameters) (coefficient state).data
        ((coefficient state).coherent radiusNonnegative) ((coefficient state).inverseCoherent radiusNonnegative) outer inner
        (originalSourceFieldLinear parameters (cores state)))
    (payment : State → ℝ) (paid : ∀ state,originalGradeNorm grade (known state)≤payment state)

include same paid

theorem actualTensorLower (order : ℕ) (strict : order<grade) :
    StartupAdjustableSpatialGraph order (fun state => originalSourceFieldLinear parameters (images state+known state))
      (fun state => originalGradeNorm grade (cores state))
      (fun state => originalCellNorm parameters grade (cores state)+OriginalUnitRankState.budget grade (coefficient state)*originalGradeNorm 0 (cores state)+payment state) := by
  let endpoint := (OriginalUnitRankState.principal_endpoint parameters length radius radiusNonnegative grade outer inner).reindex coefficient
  exact transportAffineEndpoint endpoint (fun state => OriginalUnitRankState.budget_nonnegative grade (coefficient state))
    cores images known same payment paid (originalLower parameters order grade strict (fun state => images state+known state))

theorem actualTensorPhaseFirst (order : ℕ) (allocated : order+1≤grade) (direction : Fin 2)
    (moments : State → StartupL2 3)
    (momentSame : ∀ state,StartupRadialRelated (fun cell _ => cellWeight cell) (moments state)
      (originalSourceFieldLinear parameters (images state+known state))) :
    StartupAdjustableSpatialGraph order (fun state => startupScaledPhaseFirstField parameters.sigma0 parameters.gamma 1
      parameters.gamma_pos.le zero_le_one le_rfl direction (moments state))
      (fun state => originalGradeNorm grade (cores state))
      (fun state => originalCellNorm parameters grade (cores state)+OriginalUnitRankState.budget grade (coefficient state)*originalGradeNorm 0 (cores state)+payment state) := by
  let endpoint := (OriginalUnitRankState.principal_endpoint parameters length radius radiusNonnegative grade outer inner).reindex coefficient
  exact transportAffineEndpoint endpoint (fun state => OriginalUnitRankState.budget_nonnegative grade (coefficient state))
    cores images known same payment paid
      (phaseFirst parameters startupOriginalUnitScale order grade allocated direction (fun state => images state+known state) moments momentSame)

theorem actualTensorPhaseSecond (order : ℕ) (allocated : order+2≤grade) (first second : Fin 2)
    (moments : State → StartupL2 3)
    (momentSame : ∀ state,StartupRadialRelated (fun cell _ => cellWeight cell^2) (moments state)
      (originalSourceFieldLinear parameters (images state+known state))) :
    StartupAdjustableSpatialGraph order (fun state => startupScaledPhaseSecondField parameters.sigma0 parameters.gamma 1
      parameters.gamma_pos.le zero_le_one le_rfl first second (moments state))
      (fun state => originalGradeNorm grade (cores state))
      (fun state => originalCellNorm parameters grade (cores state)+OriginalUnitRankState.budget grade (coefficient state)*originalGradeNorm 0 (cores state)+payment state) := by
  let endpoint := (OriginalUnitRankState.principal_endpoint parameters length radius radiusNonnegative grade outer inner).reindex coefficient
  exact transportAffineEndpoint endpoint (fun state => OriginalUnitRankState.budget_nonnegative grade (coefficient state))
    cores images known same payment paid
      (phaseSecond parameters startupOriginalUnitScale order grade allocated first second (fun state => images state+known state) moments momentSame)

end StartupAdjustableSpatialGraph
end Grad.CartesianStartup
