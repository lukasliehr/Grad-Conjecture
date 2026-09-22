import AKDW7OriginalUnitNativeSpatialEquation
import AKDS34OriginalUnitLedgerFidelity
import AKCX52SameClosedNativeInduction
import AKCX44ActualNativeLowerSpatialGraphs
import AKEF1ExplicitSignedCompactData
import AKEF2ExplicitPhysicalUnitFlux
import AKDW26ActualOriginalNormPacket
import AKCX31ActualKnownAllSpatialGraphs
import AKCX50SameActualRankStep

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.WeightedJets
open Grad.AnalyticWeights.Calculus Grad.SpatialDilation Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Ledger

open Grad.OriginalCoreRealization Grad.ClosedJets Grad.WeightedJets.ZeroExtension Grad.SourceCollarCoefficients
open scoped ContDiff
namespace StartupOriginalUnitNormPacket

/-- The actual native weak rows produce the literal compact data consumed by the norm estimate. -/
theorem explicitCompactData (parameters : PhaseParameters) (length radius : ℝ) (radiusNonnegative : 0≤radius)
    (packet : StartupOriginalUnitNormPacket parameters length radius) (physicalScale : ℝ)
    (rows rawRows : StartupNativeERRows) (psi : StartupL2 1)
    (phase : StartupNativeERRowsRelated (physicalWeight parameters.sigma0 parameters.gamma 1) rows rawRows)
    (weak : StartupNativeWeakRows physicalScale psi rawRows)
    (fieldBase : packet.field.field=rows.circle.field)
    (forceBase : packet.knownForce.field=rows.knownForce.field)
    (thirdBase : packet.knownThird.field=rows.knownThird.field)
    (detBase : packet.determinant.field=rows.determinant.field)
    (forceSame : startupGenuineForceKernel (unitDiskAdmissible parameters) packet.coefficient.data
      (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative) rows.circle.field=rows.forceCorrection.field)
    (thirdSame : originalThirdCorrectionKernel (unitDiskAdmissible parameters) packet.coefficient.data
      (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative) rows.circle.field=rows.thirdCorrection.field)
    (fluxSame : startupGenuinePrincipalFluxKernel (unitDiskAdmissible parameters) packet.coefficient.data
      (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative) rows.circle.field=rows.currentFlux.field)
    (scalarFluxSame : originalScalarFluxKernel (unitDiskAdmissible parameters) packet.coefficient.data
      (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative) rows.circle.field=rows.scalarFlux.field)
    (fieldRegular : ∀ order, packet.field.HasSpatialGrade order)
    (forceRegular : ∀ order, packet.knownForce.toStartupSignedFamily.HasSpatialGrade order)
    (thirdRegular : ∀ order, packet.knownThird.toStartupSignedFamily.HasSpatialGrade order)
    (detRegular : ∀ order, packet.determinant.toStartupSignedFamily.HasSpatialGrade order)
    (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff) (order : ℕ) :
    ∃ data : StartupCompactSpatialEquation order (tsupport cutoff),
      base 3 order openUnitDisk (fun _ => 0) data.field=startupCutoffL2 cutoff smooth compact packet.field.field ∧
      (∀ outer inner,base 3 order openUnitDisk (fun _ => 0) (data.tensor outer inner)=
        startupCutoffL2 cutoff smooth compact (packet.tensorFamily radiusNonnegative outer inner).field) ∧
      base 3 order openUnitDisk (fun _ => 0) data.zeroth=
        startupCutoffEquationZeroth cutoff smooth compact packet.field.field
          (startupSignedPhaseZeroth parameters one_ne_zero startupOriginalUnitScale packet.field
            (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative physicalScale) 0)
          (fun outer inner => (packet.tensorFamily radiusNonnegative outer inner).field)
          (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale packet.field
            (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative physicalScale) 0) ∧
      ∀ direction,base 3 order openUnitDisk (fun _ => 0) (data.flux direction)=
        startupCutoffEquationFlux cutoff smooth compact packet.field.field
          (fun outer inner => (packet.tensorFamily radiusNonnegative outer inner).field)
          (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale packet.field
            (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative physicalScale) 0) direction := by
  have signed := startupOriginalUnitNativeRows_explicitSignedData parameters physicalScale
    (unitDiskAdmissible parameters) packet.coefficient.data (packet.coefficient.coherent radiusNonnegative)
    (packet.coefficient.inverseCoherent radiusNonnegative) rows rawRows psi phase weak packet.field fieldBase
    packet.knownForce packet.knownThird packet.determinant forceRegular detRegular forceBase thirdBase detBase
    forceSame thirdSame fluxSame scalarFluxSame
  have tensorRegular (outer inner : Fin 2) : (packet.tensorFamily radiusNonnegative outer inner).HasSpatialGrade order :=
    (StartupSignedAction.actualPrincipal_allWeightSpatial (unitDiskAdmissible parameters) order packet.coefficient.data
      (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative)
      one_ne_zero one_ne_zero packet.field (fieldRegular order) outer inner).add
      (StartupSignedFirstFamily.knownTensor_allSpatialGrade order packet.knownForce packet.knownThird
        (forceRegular order) (thirdRegular order) outer inner)
  have rawEquation : StartupWeakDivDivEquation (packet.field.unweight parameters startupOriginalUnitScale).field 0
      (fun outer inner => ((packet.tensorFamily radiusNonnegative outer inner).unweight parameters startupOriginalUnitScale).field)
      (fun direction => ((packet.fluxFamily radiusNonnegative physicalScale direction).unweight parameters startupOriginalUnitScale).field) := signed.2.1
  have fluxRegular (direction : Fin 2) : (packet.fluxFamily radiusNonnegative physicalScale direction).HasSpatialGrade order :=
    signed.2.2 order (fieldRegular order) direction
  simpa only [StartupSignedFamily.zero] using startupSame_signedCompactSpatialEquation_explicit cutoff smooth compact parameters one_ne_zero startupOriginalUnitScale order
    packet.field (packet.tensorFamily radiusNonnegative) (packet.fluxFamily radiusNonnegative physicalScale)
    (fieldRegular order) tensorRegular fluxRegular rawEquation 0

end StartupOriginalUnitNormPacket
end Grad.CartesianStartup
