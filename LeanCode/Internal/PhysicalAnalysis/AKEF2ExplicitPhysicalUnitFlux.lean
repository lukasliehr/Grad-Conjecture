import AKDW7OriginalUnitNativeSpatialEquation
import AKDS34OriginalUnitLedgerFidelity
import AKCX52SameClosedNativeInduction
import AKCX44ActualNativeLowerSpatialGraphs

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

/-- The literal physical-scale lower flux, fixed before selecting any equation witness. -/
def startupOriginalUnitExplicitLowerFlux (parameters : PhaseParameters) (physicalScale : ℝ)
    (admissible : Admissible 1 parameters.sigma0 parameters.gamma 1)
    (data : LedgerData 1 parameters.sigma0 parameters.gamma 1) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (field : StartupSignedFamily 3 1 1) (knownForce : StartupSignedFirstFamily 2 1 1)
    (determinant : StartupSignedFirstFamily 1 1 1) : Fin 2 → StartupSignedFamily 3 1 1 :=
  StartupSignedFamily.physicalNativeLowerFlux physicalScale determinant.toStartupSignedFamily
    (field.value toroidalPartMap)
    ((StartupSignedAction.scalarFlux admissible data coherent inverseCoherent).action field)
    ((field.value planarPartMap).recoveredGradient
      (knownForce.toStartupSignedFamily.sub ((StartupSignedAction.force admissible data coherent inverseCoherent).action field)))

theorem startupOriginalUnitNativeRows_explicitSignedData (parameters : PhaseParameters) (physicalScale : ℝ)
    (admissible : Admissible 1 parameters.sigma0 parameters.gamma 1)
    (data : LedgerData 1 parameters.sigma0 parameters.gamma 1) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (rows rawRows : StartupNativeERRows) (psi : StartupL2 1)
    (phase : StartupNativeERRowsRelated (physicalWeight parameters.sigma0 parameters.gamma 1) rows rawRows)
    (weak : StartupNativeWeakRows (physicalScale) psi rawRows)
    (field : StartupSignedFamily 3 1 1) (fieldBase : field.field = rows.circle.field)
    (knownForce : StartupSignedFirstFamily 2 1 1) (knownThird determinant : StartupSignedFirstFamily 1 1 1)
    (forceRegular : ∀ order, knownForce.toStartupSignedFamily.HasSpatialGrade order)
    (detRegular : ∀ order, determinant.toStartupSignedFamily.HasSpatialGrade order)
    (forceBase : knownForce.field = rows.knownForce.field) (thirdBase : knownThird.field = rows.knownThird.field)
    (detBase : determinant.field = rows.determinant.field)
    (forceSame : startupGenuineForceKernel admissible data coherent inverseCoherent rows.circle.field = rows.forceCorrection.field)
    (thirdSame : originalThirdCorrectionKernel admissible data coherent inverseCoherent rows.circle.field = rows.thirdCorrection.field)
    (fluxSame : startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent rows.circle.field = rows.currentFlux.field)
    (scalarFluxSame : originalScalarFluxKernel admissible data coherent inverseCoherent rows.circle.field = rows.scalarFlux.field) :
    let flux := startupOriginalUnitExplicitLowerFlux parameters physicalScale admissible data coherent inverseCoherent field knownForce determinant;
      (∀ direction, (flux direction).field = rows.flux (physicalScale) direction) ∧
      StartupWeakDivDivEquation (field.unweight parameters startupOriginalUnitScale).field 0
        (fun outer inner => ((startupSignedFullTensor admissible data coherent inverseCoherent field
          (StartupSignedFirstFamily.knownTensor knownForce knownThird) outer inner).unweight parameters startupOriginalUnitScale).field)
        (fun direction => ((flux direction).unweight parameters startupOriginalUnitScale).field) ∧
      (∀ order, field.HasSpatialGrade order → ∀ direction, (flux direction).HasSpatialGrade order) := by
  let force := (StartupSignedAction.force admissible data coherent inverseCoherent).action field
  let scalarFlux := (StartupSignedAction.scalarFlux admissible data coherent inverseCoherent).action field
  let scalar := field.value toroidalPartMap
  let vector := field.value planarPartMap
  let gradient := vector.recoveredGradient (knownForce.toStartupSignedFamily.sub force)
  let flux := StartupSignedFamily.physicalNativeLowerFlux physicalScale determinant.toStartupSignedFamily scalar scalarFlux gradient
  have scalarBase : scalar.field = rows.scalar.field := by
    change originalValueKernel toroidalPartMap field.field = _
    rw [fieldBase]
    rfl
  have scalarFluxBase : scalarFlux.field = rows.scalarFlux.field := by
    change ((StartupSignedAction.scalarFlux admissible data coherent inverseCoherent).action field).field = _
    rw [StartupSignedAction.sameField,StartupSignedAction.scalarFlux_coarse,fieldBase,scalarFluxSame]
  have gradientBase : gradient.field = rows.gradient.field := by
    change startupRecoveredGradient (originalValueKernel planarPartMap field.field)
      (knownForce.field - ((StartupSignedAction.force admissible data coherent inverseCoherent).action field).field) = _
    rw [StartupSignedAction.sameField,StartupSignedAction.force_coarse,fieldBase,forceBase,forceSame]
    rfl
  have fluxBase (direction : Fin 2) : (flux direction).field = rows.flux (physicalScale) direction :=
    StartupSignedFamily.physicalNativeLowerFlux_field physicalScale determinant.toStartupSignedFamily scalar scalarFlux gradient
      rows.determinant rows.scalar rows.scalarFlux rows.gradient detBase scalarBase scalarFluxBase gradientBase direction
  have tensorBase (outer inner : Fin 2) :
      (startupSignedFullTensor admissible data coherent inverseCoherent field
        (StartupSignedFirstFamily.knownTensor knownForce knownThird) outer inner).field = rows.tensor outer inner := by
    change ((StartupSignedAction.principalTensor admissible data coherent inverseCoherent outer inner).action field).field +
      (StartupSignedFirstFamily.knownTensor knownForce knownThird outer inner).field = _
    rw [StartupSignedAction.sameField,StartupSignedAction.principalTensor_coarse,fieldBase,
      startupNative_actualPrincipalTensor admissible data coherent inverseCoherent rows forceSame thirdSame fluxSame,
      StartupSignedFirstFamily.knownTensor_field,forceBase,thirdBase]
    rfl
  have phaseRadial : ∀ cell (first second : Spatial), ‖first‖ = ‖second‖ →
      physicalWeight parameters.sigma0 parameters.gamma 1 cell first =
        physicalWeight parameters.sigma0 parameters.gamma 1 cell second := by
    intro cell first second same
    simp only [physicalWeight,same]
  have rawField : (field.unweight parameters startupOriginalUnitScale).field = rawRows.circle.field :=
    field.unweight_sameBase parameters startupOriginalUnitScale rawRows.circle.field (by rw [fieldBase]; exact phase.circle phaseRadial)
  have rawTensor (outer inner : Fin 2) :
      ((startupSignedFullTensor admissible data coherent inverseCoherent field
        (StartupSignedFirstFamily.knownTensor knownForce knownThird) outer inner).unweight parameters startupOriginalUnitScale).field =
        rawRows.tensor outer inner :=
    StartupSignedFamily.unweight_sameBase parameters startupOriginalUnitScale _ (rawRows.tensor outer inner)
      (by rw [tensorBase]; exact phase.tensor phaseRadial outer inner)
  have rawFlux (direction : Fin 2) : ((flux direction).unweight parameters startupOriginalUnitScale).field = rawRows.flux (physicalScale) direction :=
    (flux direction).unweight_sameBase parameters startupOriginalUnitScale _ (by rw [fluxBase]; exact phase.flux phaseRadial (physicalScale) direction)
  refine ⟨fluxBase,?_,?_⟩
  · change StartupWeakDivDivEquation (field.unweight parameters startupOriginalUnitScale).field 0
      (fun outer inner => ((startupSignedFullTensor admissible data coherent inverseCoherent field
        (StartupSignedFirstFamily.knownTensor knownForce knownThird) outer inner).unweight parameters startupOriginalUnitScale).field)
      (fun direction => ((flux direction).unweight parameters startupOriginalUnitScale).field)
    simpa only [rawField,rawTensor,rawFlux] using weak.divDiv
  · intro order regular direction
    exact StartupSignedFamily.HasSpatialGrade.physicalNativeLowerFlux physicalScale (detRegular order)
      (regular.value toroidalPartMap)
      (StartupSignedAction.actualScalarFlux_allSpatialGrade admissible data coherent inverseCoherent one_ne_zero one_ne_zero order field regular)
      ((regular.value planarPartMap).recoveredGradient ((forceRegular order).sub
        (StartupSignedAction.actualForce_allSpatialGrade admissible data coherent inverseCoherent one_ne_zero one_ne_zero order field regular))) direction

end Grad.CartesianStartup
