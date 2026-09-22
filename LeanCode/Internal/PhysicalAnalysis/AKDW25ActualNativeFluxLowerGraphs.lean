import AKDW24ActualRemainderPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.SourceCollarCoefficients Grad.OriginalCoreRealization Grad.OriginalCartesianTameEstimate Grad.ActualOriginalSourceFirst Grad.CellWeights
namespace StartupAdjustableSpatialGraph

variable {State : Type*} (parameters : PhaseParameters) (length radius : ℝ) (radiusNonnegative : 0≤radius)
    (grade : ℕ) (coefficient : State → OriginalUnitRankState parameters length radius)
    (cores images known : State → ACore parameters 3) (direction : Fin 2)
    (same : ∀ state,originalSourceFieldLinear parameters (images state)=
      startupNativePreAxialFluxKernel
        (startupGenuineForceKernel (unitDiskAdmissible parameters) (coefficient state).data
          ((coefficient state).coherent radiusNonnegative) ((coefficient state).inverseCoherent radiusNonnegative))
        (originalScalarFluxKernel (unitDiskAdmissible parameters) (coefficient state).data
          ((coefficient state).coherent radiusNonnegative) ((coefficient state).inverseCoherent radiusNonnegative)) direction
        (originalSourceFieldLinear parameters (cores state)))
    (scale : ℝ) (payment : State → ℝ) (paid : ∀ state,originalGradeNorm grade (known state)≤payment state)
    (field : State → StartupL2 3)
    (fieldSame : ∀ state,field state=(scale : ℂ) •
      originalSourceFieldLinear parameters (originalSignedAxialCore parameters (images state) 1 1 1)+
        originalSourceFieldLinear parameters (known state))

include same paid fieldSame

theorem actualNativeFluxLower (order : ℕ) (strict : order<grade) :
    StartupAdjustableSpatialGraph order field (fun state => originalGradeNorm grade (cores state))
      (startupOriginalRemainderPayment parameters grade coefficient cores payment) := by
  have high0 (state : State) := originalGradeNorm_nonnegative grade (cores state)
  have payment0 (state : State) := (originalGradeNorm_nonnegative grade (known state)).trans (paid state)
  have unknown := (startupOriginalNativeAxial_lowerGraph parameters length radius radiusNonnegative order grade strict direction coefficient cores images same).enlargeLow
    (startupOriginalRemainderPayment_unknown parameters grade coefficient cores payment payment0)
  have source := sourcePaid parameters grade known (originalLower parameters order grade strict known) high0 paid
  have sourceLarger := source.enlargeLow (startupOriginalRemainderPayment_source parameters grade coefficient cores payment)
  exact ((unknown.smul (scale : ℂ) high0).add sourceLarger).congr (fun state => (fieldSame state).symm)

theorem actualNativeFluxPhaseFirst (order : ℕ) (allocated : order+2≤grade) (phaseDirection : Fin 2)
    (moments : State → StartupL2 3)
    (momentSame : ∀ state,StartupRadialRelated (fun cell _ => cellWeight cell) (moments state) (field state)) :
    StartupAdjustableSpatialGraph order (fun state => startupScaledPhaseFirstField parameters.sigma0 parameters.gamma 1
      parameters.gamma_pos.le zero_le_one le_rfl phaseDirection (moments state))
      (fun state => originalGradeNorm grade (cores state))
      (startupOriginalRemainderPayment parameters grade coefficient cores payment) := by
  have high0 (state : State) := originalGradeNorm_nonnegative grade (cores state)
  have payment0 (state : State) := (originalGradeNorm_nonnegative grade (known state)).trans (paid state)
  let axial := fun state => originalSignedAxialCore parameters (images state) 1 1 1
  let first := fun state => startupOriginalFirstNaturalMoment parameters (axial state)
  let second := fun state => startupOriginalFirstNaturalMoment parameters (known state)
  have firstSame (state : State) := startupOriginalFirstNaturalMoment_same parameters (axial state)
  have secondSame (state : State) := startupOriginalFirstNaturalMoment_same parameters (known state)
  have unknown := (startupOriginalNativeAxial_phaseFirst parameters length radius radiusNonnegative order grade allocated
    direction phaseDirection coefficient cores images same first firstSame).enlargeLow
    (startupOriginalRemainderPayment_unknown parameters grade coefficient cores payment payment0)
  have source := sourcePaid parameters grade known
    (phaseFirst parameters startupOriginalUnitScale order grade (by omega) phaseDirection known second secondSame) high0 paid
  have sourceLarger := source.enlargeLow (startupOriginalRemainderPayment_source parameters grade coefficient cores payment)
  apply ((unknown.smul (scale : ℂ) high0).add sourceLarger).congr
  intro state
  exact (startupScaledPhaseFirstField_affine parameters.sigma0 parameters.gamma 1 parameters.gamma_pos.le zero_le_one le_rfl
    phaseDirection (scale : ℂ) (field state) (originalSourceFieldLinear parameters (axial state))
    (originalSourceFieldLinear parameters (known state)) (moments state) (first state) (second state)
    (fieldSame state) (momentSame state) (firstSame state) (secondSame state)).symm

end StartupAdjustableSpatialGraph
end Grad.CartesianStartup
