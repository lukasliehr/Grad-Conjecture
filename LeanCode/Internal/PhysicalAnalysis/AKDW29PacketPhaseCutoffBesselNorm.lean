import AKDW28PacketLowerGraphFactors
import AKDP70ActualCutoffLowerGraphFormula
import AKDP71ActualPhaseLowerGraphFormula
import AKDP74CompactBesselAdjustableNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 4000
open Set
open scoped ContDiff
namespace Grad.CartesianStartup.StartupAdjustableSpatialGraph
open Grad.GenericCarriers

theorem reindex {State Input : Type*} {order : ℕ} {field : State → StartupL2 3} {high low : State → ℝ}
    (estimate : StartupAdjustableSpatialGraph order field high low) (mapping : Input → State) :
    StartupAdjustableSpatialGraph order (fun input => field (mapping input))
      (fun input => high (mapping input)) (fun input => low (mapping input)) := by
  intro epsilon positive
  let result := estimate epsilon positive
  exact ⟨result.choose,result.choose_spec.1,fun input => result.choose_spec.2 (mapping input)⟩

end Grad.CartesianStartup.StartupAdjustableSpatialGraph

namespace Grad.CartesianStartup.StartupOriginalUnitNormPacket
open Grad.CartesianState Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.ZeroExtension
open StartupAdjustableSpatialGraph
variable (parameters : PhaseParameters) (length radius : ℝ) (radiusNonnegative : 0≤radius) (grade : ℕ) (scale : ℝ)

theorem phaseZeroth_lower (order : ℕ) (allocated : order+2≤grade) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius =>
      startupSignedPhaseZeroth parameters one_ne_zero startupOriginalUnitScale packet.field
        (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative scale) 0)
      (high parameters length radius grade) (low parameters length radius grade scale) :=
  phaseZerothFormula (State := StartupOriginalUnitNormPacket parameters length radius) parameters startupOriginalUnitScale
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.field.naturalMoment one_ne_zero one_ne_zero 0 2)
    (fun outer inner packet => (packet.tensorFamily radiusNonnegative outer inner).naturalMoment one_ne_zero one_ne_zero 0 2)
    (fun direction packet => (packet.fluxFamily radiusNonnegative scale direction).naturalMoment one_ne_zero one_ne_zero 0 1)
    (fun direction => field_phaseSecond parameters length radius grade scale order allocated direction direction)
    (fun outer inner => tensor_phaseSecond parameters length radius grade scale radiusNonnegative order allocated outer inner outer inner)
    (fun direction => flux_phaseFirst parameters length radius grade scale radiusNonnegative order allocated direction direction)
    (high_nonnegative parameters length radius grade)

theorem phaseFlux_lower (order : ℕ) (allocated : order+1≤grade) (direction : Fin 2) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius =>
      startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale packet.field
        (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative scale) 0 direction)
      (high parameters length radius grade) (low parameters length radius grade scale) := by
  have actual := phaseFluxFormula (State := StartupOriginalUnitNormPacket parameters length radius) parameters startupOriginalUnitScale
    (fun packet : StartupOriginalUnitNormPacket parameters length radius => packet.field.naturalMoment one_ne_zero one_ne_zero 0 1)
    (fun outer inner packet => (packet.tensorFamily radiusNonnegative outer inner).naturalMoment one_ne_zero one_ne_zero 0 1)
    (fun dir packet => (packet.fluxFamily radiusNonnegative scale dir).field)
    (fun dir => field_phaseFirst parameters length radius grade scale order allocated dir)
    (fun outer inner dir => tensor_phaseFirst parameters length radius grade scale radiusNonnegative order allocated outer inner dir)
    (fun dir => flux_lower parameters length radius grade scale radiusNonnegative order (by omega) dir)
    direction (high_nonnegative parameters length radius grade)
  apply actual.congr
  intro packet
  simp only [startupSignedPhaseFlux,StartupSignedFamily.zero]
  rfl

variable (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)

theorem cutoffZeroth_lower (order : ℕ) (allocated : order+2≤grade) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius =>
      startupCutoffEquationZeroth cutoff smooth compact packet.field.field
        (startupSignedPhaseZeroth parameters one_ne_zero startupOriginalUnitScale packet.field
          (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative scale) 0)
        (fun outer inner => (packet.tensorFamily radiusNonnegative outer inner).field)
        (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale packet.field
          (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative scale) 0))
      (high parameters length radius grade) (low parameters length radius grade scale) :=
  cutoffZeroth (State := StartupOriginalUnitNormPacket parameters length radius) cutoff smooth compact (field_lower parameters length radius grade scale order (by omega))
    (phaseZeroth_lower parameters length radius radiusNonnegative grade scale order allocated)
    (fun outer inner => tensor_lower parameters length radius grade scale radiusNonnegative order (by omega) outer inner)
    (fun direction => phaseFlux_lower parameters length radius radiusNonnegative grade scale order (by omega) direction)
    (high_nonnegative parameters length radius grade)

theorem cutoffFlux_lower (order : ℕ) (allocated : order+1≤grade) (direction : Fin 2) :
    StartupAdjustableSpatialGraph order (fun packet : StartupOriginalUnitNormPacket parameters length radius =>
      startupCutoffEquationFlux cutoff smooth compact packet.field.field
        (fun outer inner => (packet.tensorFamily radiusNonnegative outer inner).field)
        (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale packet.field
          (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative scale) 0) direction)
      (high parameters length radius grade) (low parameters length radius grade scale) :=
  cutoffFlux (State := StartupOriginalUnitNormPacket parameters length radius) cutoff smooth compact (field_lower parameters length radius grade scale order (by omega))
    (fun outer inner => tensor_lower parameters length radius grade scale radiusNonnegative order (by omega) outer inner)
    (fun dir => phaseFlux_lower parameters length radius radiusNonnegative grade scale order allocated dir)
    direction (high_nonnegative parameters length radius grade)

/-- The genuine compact Bessel remainder uses q-2 value/zeroth and q-1
flux norms. All literal phase and cutoff terms have now been estimated. -/
theorem compactBessel_lower {State : Type*} (packets : State → StartupOriginalUnitNormPacket parameters length radius) (rank : ℕ) (localizer : TestLocalizer openUnitDisk (tsupport cutoff))
    (data : State → StartupCompactSpatialEquation (rank+2) (tsupport cutoff))
    (fieldSame : ∀ packet,base 3 (rank+2) openUnitDisk (fun _ => 0) (data packet).field=
      startupCutoffL2 cutoff smooth compact (packets packet).field.field)
    (zeroSame : ∀ packet,base 3 (rank+2) openUnitDisk (fun _ => 0) (data packet).zeroth=
      startupCutoffEquationZeroth cutoff smooth compact (packets packet).field.field
        (startupSignedPhaseZeroth parameters one_ne_zero startupOriginalUnitScale (packets packet).field
          ((packets packet).tensorFamily radiusNonnegative) ((packets packet).fluxFamily radiusNonnegative scale) 0)
        (fun outer inner => ((packets packet).tensorFamily radiusNonnegative outer inner).field)
        (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale (packets packet).field
          ((packets packet).tensorFamily radiusNonnegative) ((packets packet).fluxFamily radiusNonnegative scale) 0))
    (fluxSame : ∀ packet direction,base 3 (rank+2) openUnitDisk (fun _ => 0) ((data packet).flux direction)=
      startupCutoffEquationFlux cutoff smooth compact (packets packet).field.field
        (fun outer inner => ((packets packet).tensorFamily radiusNonnegative outer inner).field)
        (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale (packets packet).field
          ((packets packet).tensorFamily radiusNonnegative) ((packets packet).fluxFamily radiusNonnegative scale) 0) direction)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ packet,
      ‖startupCompactBesselRemainder (data packet)‖≤epsilon*high parameters length radius (rank+2) (packets packet)+
        constant*low parameters length radius (rank+2) scale (packets packet) := by
  apply startupCompactBesselRemainder_adjustable rank (isClosed_tsupport cutoff) localizer data
    (fun state => high parameters length radius (rank+2) (packets state))
    (fun state => low parameters length radius (rank+2) scale (packets state))
    (fun state => high_nonnegative parameters length radius (rank+2) (packets state))
  · exact (cutoffGraph cutoff smooth compact (field_lower parameters length radius (rank+2) scale rank (by omega))
      (high_nonnegative parameters length radius (rank+2))).reindex packets |>.congr (fun packet : State => (fieldSame packet).symm)
  · exact (cutoffZeroth_lower parameters length radius radiusNonnegative (rank+2) scale cutoff smooth compact rank le_rfl).reindex packets |>.congr
      (fun packet : State => (zeroSame packet).symm)
  · intro direction
    exact (cutoffFlux_lower parameters length radius radiusNonnegative (rank+2) scale cutoff smooth compact (rank+1) (by omega) direction).reindex packets |>.congr
      (fun packet : State => (fluxSame packet direction).symm)
  · exact positive

end Grad.CartesianStartup.StartupOriginalUnitNormPacket
