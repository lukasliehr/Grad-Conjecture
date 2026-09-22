import AKDW26ActualOriginalNormPacket
import AKDW12OriginalUnitTensorRemainderNorm
import AKDP62OriginalCutoffMixedNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 4000
open Set
open scoped ContDiff
namespace Grad.CartesianStartup.StartupOriginalUnitNormPacket
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.SourceCollarCoefficients Grad.ActualOriginalSourceMoments
variable {parameters : PhaseParameters} {length radius : ℝ}
    (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    (packet : StartupOriginalUnitNormPacket parameters length radius)

def cutoffCore : ACore parameters 3 := (startupOriginalCutoff_core_exists parameters cutoff smooth compact packet.core).choose

theorem cutoffCore_same : originalSourceFieldLinear parameters (packet.cutoffCore cutoff smooth compact)=
    startupCutoffL2 cutoff smooth compact (originalSourceFieldLinear parameters packet.core) :=
  (startupOriginalCutoff_core_exists parameters cutoff smooth compact packet.core).choose_spec

def cutoffKnownTensorCore (outer inner : Fin 2) : ACore parameters 3 :=
  (startupOriginalCutoff_core_exists parameters cutoff smooth compact (packet.knownTensorCore outer inner)).choose

theorem cutoffKnownTensorCore_same (outer inner : Fin 2) :
    originalSourceFieldLinear parameters (packet.cutoffKnownTensorCore cutoff smooth compact outer inner)=
      startupCutoffL2 cutoff smooth compact (originalSourceFieldLinear parameters (packet.knownTensorCore outer inner)) :=
  (startupOriginalCutoff_core_exists parameters cutoff smooth compact (packet.knownTensorCore outer inner)).choose_spec

def cutoffPrincipalCore (radiusNonnegative : 0≤radius) (outer inner : Fin 2) : ACore parameters 3 :=
  (packet.coefficient.principal_core_exists radiusNonnegative (packet.cutoffCore cutoff smooth compact) outer inner).choose

theorem cutoffPrincipalCore_same (radiusNonnegative : 0≤radius) (outer inner : Fin 2) :
    originalSourceFieldLinear parameters (packet.cutoffPrincipalCore cutoff smooth compact radiusNonnegative outer inner)=
      startupGenuinePrincipalTensorKernel (unitDiskAdmissible parameters) packet.coefficient.data
        (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative) outer inner
        (originalSourceFieldLinear parameters (packet.cutoffCore cutoff smooth compact)) :=
  (packet.coefficient.principal_core_exists radiusNonnegative (packet.cutoffCore cutoff smooth compact) outer inner).choose_spec

/-- The full actual cutoff tensor is the principal of the SAME cutoff
w plus the cutoff of the genuine known tensor, at exactly the same rank. -/
theorem cutoffTensor_same (radiusNonnegative : 0≤radius)
    (radial : ∀ first second : Spatial,‖first‖=‖second‖ → cutoff first=cutoff second) (outer inner : Fin 2) :
    startupCutoffL2 cutoff smooth compact (packet.tensorFamily radiusNonnegative outer inner).field=
      originalSourceFieldLinear parameters
        (packet.cutoffPrincipalCore cutoff smooth compact radiusNonnegative outer inner+
          packet.cutoffKnownTensorCore cutoff smooth compact outer inner) := by
  rw [packet.tensorFamily_same radiusNonnegative]
  simp only [map_add]
  rw [packet.cutoffPrincipalCore_same cutoff smooth compact radiusNonnegative,
    packet.cutoffKnownTensorCore_same cutoff smooth compact,packet.cutoffCore_same cutoff smooth compact,
    startupGenuinePrincipalTensor_cutoff (unitDiskAdmissible parameters) packet.coefficient.data
      (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative)
      cutoff smooth compact radial,packet.principalCore_same radiusNonnegative]

end Grad.CartesianStartup.StartupOriginalUnitNormPacket
