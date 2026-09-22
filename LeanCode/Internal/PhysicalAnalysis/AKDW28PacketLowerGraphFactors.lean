import AKDW27OriginalPacketSourcePayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 4000
namespace Grad.CartesianStartup.StartupOriginalUnitNormPacket
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.OriginalCartesianTameEstimate Grad.CellWeights
open StartupAdjustableSpatialGraph
variable (parameters : PhaseParameters) (length radius : ℝ)

abbrev high (grade : ℕ) (packet : StartupOriginalUnitNormPacket parameters length radius) : ℝ := originalGradeNorm grade packet.core

abbrev low (grade : ℕ) (scale : ℝ) : StartupOriginalUnitNormPacket parameters length radius → ℝ :=
  startupOriginalRemainderPayment parameters grade (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.coefficient) (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.core) (sourcePayment grade scale)

theorem high_nonnegative (grade : ℕ) (packet : StartupOriginalUnitNormPacket parameters length radius) : 0≤high parameters length radius grade packet :=
  originalGradeNorm_nonnegative grade packet.core

theorem cell_le_low (grade : ℕ) (scale : ℝ) (packet : StartupOriginalUnitNormPacket parameters length radius) :
    originalCellNorm parameters grade packet.core≤low parameters length radius grade scale packet := by
  change originalCellNorm parameters grade packet.core≤originalCellNorm parameters grade packet.core+
    OriginalUnitRankState.budget grade packet.coefficient*originalGradeNorm 0 packet.core+sourcePayment grade scale packet
  have budget0 := mul_nonneg (OriginalUnitRankState.budget_nonnegative grade packet.coefficient) (originalGradeNorm_nonnegative 0 packet.core)
  linarith only [budget0,sourcePayment_nonnegative grade scale packet]

variable {parameters length radius}

theorem field_natural_same (packet : StartupOriginalUnitNormPacket parameters length radius) (weight : ℕ) :
    StartupRadialRelated (fun cell _ => cellWeight cell^weight)
      (packet.field.naturalMoment one_ne_zero one_ne_zero 0 weight) (originalSourceFieldLinear parameters packet.core) := by
  have same := packet.field.naturalMoment_same one_ne_zero one_ne_zero 0 weight
  rw [StartupSignedFamily.zero,packet.fieldSame] at same
  exact same

theorem tensor_natural_same (radiusNonnegative : 0≤radius) (packet : StartupOriginalUnitNormPacket parameters length radius)
    (outer inner : Fin 2) (weight : ℕ) :
    StartupRadialRelated (fun cell _ => cellWeight cell^weight)
      ((packet.tensorFamily radiusNonnegative outer inner).naturalMoment one_ne_zero one_ne_zero 0 weight)
      (originalSourceFieldLinear parameters (packet.principalCore radiusNonnegative outer inner+packet.knownTensorCore outer inner)) := by
  have same := (packet.tensorFamily radiusNonnegative outer inner).naturalMoment_same one_ne_zero one_ne_zero 0 weight
  rw [StartupSignedFamily.zero,packet.tensorFamily_same radiusNonnegative] at same
  exact same

variable (parameters length radius) (grade : ℕ) (scale : ℝ)

theorem field_lower (order : ℕ) (strict : order<grade) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.field.field)
      (high parameters length radius grade) (low parameters length radius grade scale) :=
  ((originalLower (State := StartupOriginalUnitNormPacket parameters length radius) parameters order grade strict (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.core)).enlargeLow
    (cell_le_low parameters length radius grade scale)).congr (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.fieldSame.symm)

theorem field_phaseFirst (order : ℕ) (allocated : order+1≤grade) (direction : Fin 2) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius =>
      startupScaledPhaseFirstField parameters.sigma0 parameters.gamma 1 parameters.gamma_pos.le zero_le_one le_rfl direction
        (packet.field.naturalMoment one_ne_zero one_ne_zero 0 1))
      (high parameters length radius grade) (low parameters length radius grade scale) :=
  (phaseFirst (State := StartupOriginalUnitNormPacket parameters length radius) parameters startupOriginalUnitScale order grade allocated direction (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.core)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.field.naturalMoment one_ne_zero one_ne_zero 0 1)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => by
      have result := field_natural_same packet 1
      simp only [pow_one] at result
      exact result)).enlargeLow
      (cell_le_low parameters length radius grade scale)

theorem field_phaseSecond (order : ℕ) (allocated : order+2≤grade) (outer inner : Fin 2) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius =>
      startupScaledPhaseSecondField parameters.sigma0 parameters.gamma 1 parameters.gamma_pos.le zero_le_one le_rfl outer inner
        (packet.field.naturalMoment one_ne_zero one_ne_zero 0 2))
      (high parameters length radius grade) (low parameters length radius grade scale) :=
  (phaseSecond (State := StartupOriginalUnitNormPacket parameters length radius) parameters startupOriginalUnitScale order grade allocated outer inner (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.core)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.field.naturalMoment one_ne_zero one_ne_zero 0 2)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => field_natural_same packet 2)).enlargeLow (cell_le_low parameters length radius grade scale)

variable (radiusNonnegative : 0≤radius)

theorem tensor_lower (order : ℕ) (strict : order<grade) (outer inner : Fin 2) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius =>
      (packet.tensorFamily radiusNonnegative outer inner).field)
      (high parameters length radius grade) (low parameters length radius grade scale) :=
  (actualTensorLower (State := StartupOriginalUnitNormPacket parameters length radius) parameters length radius radiusNonnegative grade (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.coefficient)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.core) (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.principalCore radiusNonnegative outer inner)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.knownTensorCore outer inner) outer inner
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.principalCore_same radiusNonnegative outer inner) (sourcePayment grade scale)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => knownTensor_paid grade scale packet outer inner) order strict).congr
      (fun packet : StartupOriginalUnitNormPacket parameters length radius => (packet.tensorFamily_same radiusNonnegative outer inner).symm)

theorem tensor_phaseFirst (order : ℕ) (allocated : order+1≤grade) (outer inner direction : Fin 2) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius =>
      startupScaledPhaseFirstField parameters.sigma0 parameters.gamma 1 parameters.gamma_pos.le zero_le_one le_rfl direction
        ((packet.tensorFamily radiusNonnegative outer inner).naturalMoment one_ne_zero one_ne_zero 0 1))
      (high parameters length radius grade) (low parameters length radius grade scale) :=
  actualTensorPhaseFirst (State := StartupOriginalUnitNormPacket parameters length radius) parameters length radius radiusNonnegative grade (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.coefficient)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.core) (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.principalCore radiusNonnegative outer inner)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.knownTensorCore outer inner) outer inner
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.principalCore_same radiusNonnegative outer inner) (sourcePayment grade scale)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => knownTensor_paid grade scale packet outer inner) order allocated direction
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => (packet.tensorFamily radiusNonnegative outer inner).naturalMoment one_ne_zero one_ne_zero 0 1)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => by simpa only [pow_one] using tensor_natural_same radiusNonnegative packet outer inner 1)

theorem tensor_phaseSecond (order : ℕ) (allocated : order+2≤grade) (outer inner first second : Fin 2) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius =>
      startupScaledPhaseSecondField parameters.sigma0 parameters.gamma 1 parameters.gamma_pos.le zero_le_one le_rfl first second
        ((packet.tensorFamily radiusNonnegative outer inner).naturalMoment one_ne_zero one_ne_zero 0 2))
      (high parameters length radius grade) (low parameters length radius grade scale) :=
  actualTensorPhaseSecond (State := StartupOriginalUnitNormPacket parameters length radius) parameters length radius radiusNonnegative grade (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.coefficient)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.core) (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.principalCore radiusNonnegative outer inner)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.knownTensorCore outer inner) outer inner
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.principalCore_same radiusNonnegative outer inner) (sourcePayment grade scale)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => knownTensor_paid grade scale packet outer inner) order allocated first second
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => (packet.tensorFamily radiusNonnegative outer inner).naturalMoment one_ne_zero one_ne_zero 0 2)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => tensor_natural_same radiusNonnegative packet outer inner 2)

theorem flux_lower (order : ℕ) (strict : order<grade) (direction : Fin 2) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius =>
      (packet.fluxFamily radiusNonnegative scale direction).field)
      (high parameters length radius grade) (low parameters length radius grade scale) :=
  actualNativeFluxLower (State := StartupOriginalUnitNormPacket parameters length radius) parameters length radius radiusNonnegative grade (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.coefficient)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.core) (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.axialCore radiusNonnegative direction)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.knownFluxCore scale direction) direction
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.axialCore_same radiusNonnegative direction) scale (sourcePayment grade scale)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => knownFlux_paid grade scale packet direction)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => (packet.fluxFamily radiusNonnegative scale direction).field)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.fluxFamily_same radiusNonnegative scale direction) order strict

theorem flux_phaseFirst (order : ℕ) (allocated : order+2≤grade) (direction phaseDirection : Fin 2) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius =>
      startupScaledPhaseFirstField parameters.sigma0 parameters.gamma 1 parameters.gamma_pos.le zero_le_one le_rfl phaseDirection
        ((packet.fluxFamily radiusNonnegative scale direction).naturalMoment one_ne_zero one_ne_zero 0 1))
      (high parameters length radius grade) (low parameters length radius grade scale) :=
  actualNativeFluxPhaseFirst (State := StartupOriginalUnitNormPacket parameters length radius) parameters length radius radiusNonnegative grade (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.coefficient)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.core) (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.axialCore radiusNonnegative direction)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.knownFluxCore scale direction) direction
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.axialCore_same radiusNonnegative direction) scale (sourcePayment grade scale)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => knownFlux_paid grade scale packet direction)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => (packet.fluxFamily radiusNonnegative scale direction).field)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.fluxFamily_same radiusNonnegative scale direction) order allocated phaseDirection
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => (packet.fluxFamily radiusNonnegative scale direction).naturalMoment one_ne_zero one_ne_zero 0 1)
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => by
      have related := (packet.fluxFamily radiusNonnegative scale direction).naturalMoment_same one_ne_zero one_ne_zero 0 1
      simpa only [pow_one,StartupSignedFamily.zero] using related)

end Grad.CartesianStartup.StartupOriginalUnitNormPacket
