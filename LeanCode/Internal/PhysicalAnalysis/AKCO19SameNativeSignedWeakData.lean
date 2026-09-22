import AKCO17ActualSignedLowerFlux
import AKCO16SameAllPowerStartupInduction
import AKBP31SameNativeRowsH1

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

/-- The existing genuine native weak rows supply exactly the base equation
required by the signed startup induction. Every completed coefficient
output and lower flux is constructed here from the SAME input family. -/
theorem startupNativeRows_sameSignedWeakData (parameters : PhaseParameters) (L : ℝ) (scale : Scale)
    (admissible : Admissible L parameters.sigma0 parameters.gamma scale.val)
    (data : LedgerData L parameters.sigma0 parameters.gamma scale.val) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (rows rawRows : StartupNativeERRows) (psi : StartupL2 1)
    (phase : StartupNativeERRowsRelated (physicalWeight parameters.sigma0 parameters.gamma scale.val) rows rawRows)
    (weak : StartupNativeWeakRows (scale.val/L) psi rawRows)
    (field : StartupSignedFamily 3 L scale.val) (fieldBase : field.field = rows.circle.field)
    (knownForce : StartupSignedFirstFamily 2 L scale.val) (knownThird determinant : StartupSignedFirstFamily 1 L scale.val)
    (forceBase : knownForce.field = rows.knownForce.field) (thirdBase : knownThird.field = rows.knownThird.field)
    (detBase : determinant.field = rows.determinant.field)
    (forceSame : startupGenuineForceKernel admissible data coherent inverseCoherent rows.circle.field = rows.forceCorrection.field)
    (thirdSame : originalThirdCorrectionKernel admissible data coherent inverseCoherent rows.circle.field = rows.thirdCorrection.field)
    (fluxSame : startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent rows.circle.field = rows.currentFlux.field)
    (scalarFluxSame : originalScalarFluxKernel admissible data coherent inverseCoherent rows.circle.field = rows.scalarFlux.field) :
    ∃ flux : Fin 2 → StartupSignedFamily 3 L scale.val,
      (∀ direction, (flux direction).field = rows.flux (scale.val/L) direction) ∧
      StartupWeakDivDivEquation (field.unweight parameters scale).field 0
        (fun outer inner => ((startupSignedFullTensor admissible data coherent inverseCoherent field
          (StartupSignedFirstFamily.knownTensor knownForce knownThird) outer inner).unweight parameters scale).field)
        (fun direction => ((flux direction).unweight parameters scale).field) := by
  let force := (StartupSignedAction.force admissible data coherent inverseCoherent).action field
  let scalarFlux := (StartupSignedAction.scalarFlux admissible data coherent inverseCoherent).action field
  let scalar := field.value toroidalPartMap
  let vector := field.value planarPartMap
  let gradient := vector.recoveredGradient (knownForce.toStartupSignedFamily.sub force)
  let flux := StartupSignedFamily.nativeLowerFlux determinant.toStartupSignedFamily scalar scalarFlux gradient
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
  have fluxBase (direction : Fin 2) : (flux direction).field = rows.flux (scale.val/L) direction :=
    StartupSignedFamily.nativeLowerFlux_field determinant.toStartupSignedFamily scalar scalarFlux gradient
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
      physicalWeight parameters.sigma0 parameters.gamma scale.val cell first =
        physicalWeight parameters.sigma0 parameters.gamma scale.val cell second := by
    intro cell first second same
    simp only [physicalWeight,same]
  have rawField : (field.unweight parameters scale).field = rawRows.circle.field :=
    field.unweight_sameBase parameters scale rawRows.circle.field (by rw [fieldBase]; exact phase.circle phaseRadial)
  have rawTensor (outer inner : Fin 2) :
      ((startupSignedFullTensor admissible data coherent inverseCoherent field
        (StartupSignedFirstFamily.knownTensor knownForce knownThird) outer inner).unweight parameters scale).field =
        rawRows.tensor outer inner :=
    StartupSignedFamily.unweight_sameBase parameters scale _ (rawRows.tensor outer inner)
      (by rw [tensorBase]; exact phase.tensor phaseRadial outer inner)
  have rawFlux (direction : Fin 2) : ((flux direction).unweight parameters scale).field = rawRows.flux (scale.val/L) direction :=
    (flux direction).unweight_sameBase parameters scale _ (by rw [fluxBase]; exact phase.flux phaseRadial (scale.val/L) direction)
  refine ⟨flux,fluxBase,?_⟩
  simpa only [rawField,rawTensor,rawFlux] using weak.divDiv

end Grad.CartesianStartup
