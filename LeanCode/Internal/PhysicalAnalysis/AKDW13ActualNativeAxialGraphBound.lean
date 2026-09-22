import AKDW11SameNativePreAxialCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst
open Grad.SourceCollarCoefficients Grad.SpatialDilation Grad.CellWeights
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger

/-- The genuine physical-L coefficient flux, including its one axial
shift, is lower order at the SAME total rank and original width. -/
theorem startupOriginalNativeAxial_lowerGraph {State : Type*} (parameters : PhaseParameters)
    (length radius : ℝ) (radiusNonnegative : 0≤radius) (order grade : ℕ) (strict : order<grade)
    (direction : Fin 2) (coefficient : State → OriginalUnitRankState parameters length radius)
    (cores images : State → ACore parameters 3)
    (same : ∀ state,originalSourceFieldLinear parameters (images state)=
      startupNativePreAxialFluxKernel
        (startupGenuineForceKernel (unitDiskAdmissible parameters) (coefficient state).data
          ((coefficient state).coherent radiusNonnegative) ((coefficient state).inverseCoherent radiusNonnegative))
        (originalScalarFluxKernel (unitDiskAdmissible parameters) (coefficient state).data
          ((coefficient state).coherent radiusNonnegative) ((coefficient state).inverseCoherent radiusNonnegative)) direction
        (originalSourceFieldLinear parameters (cores state))) :
    StartupAdjustableSpatialGraph order
      (fun state => originalSourceFieldLinear parameters (originalSignedAxialCore parameters (images state) 1 1 1))
      (fun state => originalGradeNorm grade (cores state))
      (fun state => OriginalCartesianTameEstimate.originalCellNorm parameters grade (cores state)+
        OriginalUnitRankState.budget grade (coefficient state)*originalGradeNorm 0 (cores state)) := by
  have rankPositive : 0<grade := lt_of_le_of_lt (Nat.zero_le order) strict
  have degreeSame : grade-1+1=grade := Nat.sub_add_cancel rankPositive
  have lower := StartupAdjustableSpatialGraph.signedAxialLower parameters order (grade-1) (by omega) images
  rw [degreeSame] at lower
  let certificate := OriginalUnitRankState.nativePreAxial_endpoint parameters length radius radiusNonnegative grade direction
  have endpoint := certificate.choose_spec.reindex coefficient
  exact StartupAdjustableSpatialGraph.transportEndpoint endpoint (fun state => OriginalUnitRankState.budget_nonnegative grade (coefficient state)) cores images same lower

/-- The first original phase derivative of that same signed axial image
still has total rank at most grade; no second unknown derivative is charged. -/
theorem startupOriginalNativeAxial_phaseFirst {State : Type*} (parameters : PhaseParameters)
    (length radius : ℝ) (radiusNonnegative : 0≤radius) (order grade : ℕ) (allocated : order+2≤grade)
    (direction phaseDirection : Fin 2) (coefficient : State → OriginalUnitRankState parameters length radius)
    (cores images : State → ACore parameters 3)
    (same : ∀ state,originalSourceFieldLinear parameters (images state)=
      startupNativePreAxialFluxKernel
        (startupGenuineForceKernel (unitDiskAdmissible parameters) (coefficient state).data
          ((coefficient state).coherent radiusNonnegative) ((coefficient state).inverseCoherent radiusNonnegative))
        (originalScalarFluxKernel (unitDiskAdmissible parameters) (coefficient state).data
          ((coefficient state).coherent radiusNonnegative) ((coefficient state).inverseCoherent radiusNonnegative)) direction
        (originalSourceFieldLinear parameters (cores state)))
    (moments : State → StartupL2 3)
    (momentSame : ∀ state,StartupRadialRelated (fun cell _ => cellWeight cell) (moments state)
      (originalSourceFieldLinear parameters (originalSignedAxialCore parameters (images state) 1 1 1))) :
    StartupAdjustableSpatialGraph order
      (fun state => startupScaledPhaseFirstField parameters.sigma0 parameters.gamma 1 parameters.gamma_pos.le zero_le_one le_rfl phaseDirection (moments state))
      (fun state => originalGradeNorm grade (cores state))
      (fun state => OriginalCartesianTameEstimate.originalCellNorm parameters grade (cores state)+
        OriginalUnitRankState.budget grade (coefficient state)*originalGradeNorm 0 (cores state)) := by
  have rankPositive : 0<grade := by omega
  have degreeSame : grade-1+1=grade := Nat.sub_add_cancel rankPositive
  have lower := StartupAdjustableSpatialGraph.signedAxialPhaseFirst parameters startupOriginalUnitScale order (grade-1)
    (by omega) phaseDirection images moments momentSame
  rw [degreeSame] at lower
  let certificate := OriginalUnitRankState.nativePreAxial_endpoint parameters length radius radiusNonnegative grade direction
  have endpoint := certificate.choose_spec.reindex coefficient
  exact StartupAdjustableSpatialGraph.transportEndpoint endpoint (fun state => OriginalUnitRankState.budget_nonnegative grade (coefficient state)) cores images same lower

end Grad.CartesianStartup
