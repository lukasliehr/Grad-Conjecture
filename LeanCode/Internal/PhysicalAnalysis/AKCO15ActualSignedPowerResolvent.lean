import AKCO14ActualAllPowerKnownTensor
import AKBP25SamePhaseTensorResolvent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.WeightedJets
open Grad.AnalyticWeights.Calculus Grad.SpatialDilation
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Ledger

theorem startupSame_signed_weakDivDiv_zero {L ell : ℝ}
    (field : StartupSignedFamily 3 L ell)
    (tensor : Fin 2 → Fin 2 → StartupSignedFamily 3 L ell)
    (flux : Fin 2 → StartupSignedFamily 3 L ell)
    (equation : StartupWeakDivDivEquation field.field 0
      (fun outer inner => (tensor outer inner).field) (fun direction => (flux direction).field))
    (power : ℕ) :
    StartupWeakDivDivEquation (field.moment power) 0
      (fun outer inner => (tensor outer inner).moment power) (fun direction => (flux direction).moment power) := by
  intro cell vector test
  simp only [StartupSignedFamily.pairing,map_zero]
  simpa only [Fin.sum_univ_two,mul_add,map_zero,mul_zero] using
    congrArg (fun value : ℂ => startupAxialFrequency L ell cell ^ power * value) (equation cell vector test)

def startupSignedFullTensor {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (field : StartupSignedFamily 3 L ell)
    (known : Fin 2 → Fin 2 → StartupSignedFirstFamily 3 L ell) (outer inner : Fin 2) :
    StartupSignedFamily 3 L ell :=
  ((StartupSignedAction.principalTensor admissible data coherent inverseCoherent outer inner).action field).add
    (known outer inner).toStartupSignedFamily

/-- One genuine signed-power startup step. The only input graph premises
are at strictly smaller powers; the complete actual principal composition
is retained, and every phase reserve is synthesized from its SAME output. -/
theorem startupSame_signedPower_h1 (parameters : PhaseParameters) (L : ℝ) (lengthNonzero : L ≠ 0)
    (scale : Scale) (admissible : Admissible L parameters.sigma0 parameters.gamma scale.val)
    (data : LedgerData L parameters.sigma0 parameters.gamma scale.val) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inside : Spatial → ℝ) (outerSmooth : ContDiff ℝ ∞ outer) (insideSmooth : ContDiff ℝ ∞ inside)
    (outerCompact : HasCompactSupport outer) (insideCompact : HasCompactSupport inside)
    (insideDisk : tsupport inside ⊆ openUnitDisk)
    (plateau : Set.EqOn outer (fun _ => 1) (tsupport inside))
    (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → inside first = inside second)
    (regular : FieldH1 →L[ℂ] FieldH1)
    (compatible : ∀ input, valueInclusion (regular input) =
      startupGenuinePrincipalL2 outer outerSmooth outerCompact admissible data coherent inverseCoherent (valueInclusion input))
    (coarseSmall : ‖startupGenuinePrincipalL2 outer outerSmooth outerCompact admissible data coherent inverseCoherent‖ < 1)
    (fineSmall : ‖regular‖ < 1)
    (field : StartupSignedFamily 3 L scale.val)
    (known : Fin 2 → Fin 2 → StartupSignedFirstFamily 3 L scale.val)
    (flux : Fin 2 → StartupSignedFamily 3 L scale.val)
    (equation : StartupWeakDivDivEquation (field.unweight parameters scale).field 0
      (fun outer inner => ((startupSignedFullTensor admissible data coherent inverseCoherent field known outer inner).unweight parameters scale).field)
      (fun direction => ((flux direction).unweight parameters scale).field))
    (power : ℕ) (lower : ∀ q < power, ∃ graph : StartupFirst 3,
      base 3 1 openUnitDisk (fun _ => 0) graph = field.moment q) :
    ∃ improved : FieldH1, valueInclusion improved =
      startupPlaneExtension (startupCutoffL2 inside insideSmooth insideCompact (field.moment power)) := by
  let tensor := startupSignedFullTensor admissible data coherent inverseCoherent field known
  have leading := StartupSignedAction.actualPrincipal_signedLeadingFirst admissible data coherent inverseCoherent field power lower
  let remainder (first second : Fin 2) : StartupFirst 3 := (leading first second).choose
  let knownFirst (first second : Fin 2) : StartupFirst 3 := remainder first second + (known first second).first power
  have tensorEqual (first second : Fin 2) : (tensor first second).moment power =
      startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent first second (field.moment power) +
        base 3 1 openUnitDisk (fun _ => 0) (knownFirst first second) := by
    change ((StartupSignedAction.principalTensor admissible data coherent inverseCoherent first second).action field).moment power +
      (known first second).moment power = _
    rw [(leading first second).choose_spec]
    simp only [knownFirst,map_add,StartupSignedFirstFamily.firstBase]
    exact add_assoc _ _ _
  let fieldNatural := (field.shift power).toNatural lengthNonzero scale.property.1.ne'
  let tensorNatural (first second : Fin 2) := ((tensor first second).shift power).toNatural lengthNonzero scale.property.1.ne'
  let fluxNatural (direction : Fin 2) := ((flux direction).shift power).toNatural lengthNonzero scale.property.1.ne'
  have tensorPhase (first second : Fin 2) := (tensor first second).unweight_phase parameters scale power
  have tensorFirst (first second : Fin 2) := (tensorNatural first second).same.mono (fun _ same => same 1)
  have tensorSecond (first second : Fin 2) := (tensorNatural first second).same.mono (fun _ same => same 2)
  simp only [tensorEqual] at tensorPhase
  change ∀ first second, StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ 1)
    ((tensorNatural first second).moment 1) ((tensor first second).moment power) at tensorFirst
  change ∀ first second, StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ 2)
    ((tensorNatural first second).moment 2) ((tensor first second).moment power) at tensorSecond
  simp only [pow_one,tensorEqual] at tensorFirst tensorSecond
  have fieldFirst := fieldNatural.same.mono (fun _ same => same 1)
  change StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ 1)
    (fieldNatural.moment 1) (field.moment power) at fieldFirst
  simp only [pow_one] at fieldFirst
  have fluxFirst (direction : Fin 2) := (fluxNatural direction).same.mono (fun _ same => same 1)
  change ∀ direction, StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ 1)
    ((fluxNatural direction).moment 1) ((flux direction).moment power) at fluxFirst
  simp only [pow_one] at fluxFirst
  exact startupSame_phase_actualTensor_h1 admissible data coherent inverseCoherent parameters.gamma_pos.le
    scale.property.1.le scale.property.2 outer inside outerSmooth insideSmooth outerCompact insideCompact insideDisk plateau radial
    regular compatible coarseSmall fineSmall (field.moment power) ((field.unweight parameters scale).moment power)
    (fieldNatural.moment 1) (fieldNatural.moment 2) knownFirst
    (fun first second => ((tensor first second).unweight parameters scale).moment power)
    (fun first second => (tensorNatural first second).moment 1) (fun first second => (tensorNatural first second).moment 2)
    (fun direction => (flux direction).moment power) (fun direction => ((flux direction).unweight parameters scale).moment power)
    (fun direction => (fluxNatural direction).moment 1) (field.unweight_phase parameters scale power)
    tensorPhase (fun direction => (flux direction).unweight_phase parameters scale power)
    fieldFirst
    (fieldNatural.same.mono (fun _ same => same 2)) tensorFirst tensorSecond
    fluxFirst
    (startupSame_signed_weakDivDiv_zero (field.unweight parameters scale)
      (fun first second => (tensor first second).unweight parameters scale)
      (fun direction => (flux direction).unweight parameters scale) equation power)

end Grad.CartesianStartup
