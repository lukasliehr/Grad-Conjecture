import AKBP30SameNativeERRows
import AKBP25SamePhaseTensorResolvent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.AnalyticWeights.Calculus Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

theorem startupNative_actualPrincipalTensor {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (rows : StartupNativeERRows)
    (forceSame : startupGenuineForceKernel admissible data coherent inverseCoherent rows.circle.field = rows.forceCorrection.field)
    (thirdSame : originalThirdCorrectionKernel admissible data coherent inverseCoherent rows.circle.field = rows.thirdCorrection.field)
    (fluxSame : startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent rows.circle.field = rows.currentFlux.field)
    (outer inside : Fin 2) :
    startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inside rows.circle.field =
      rows.principalTensor outer inside := by
  have rowSame (row : Fin 3) : startupGenuineERKernelRow admissible data coherent inverseCoherent row rows.circle.field =
      ![originalValueKernel planarInclusionMap rows.forceCorrection.field,
        originalValueKernel toroidalInclusionMap rows.thirdCorrection.field,
        originalValueKernel planarInclusionMap rows.currentFlux.field] row := by
    fin_cases row
    · exact congrArg (originalValueKernel planarInclusionMap) forceSame
    · exact congrArg (originalValueKernel toroidalInclusionMap) thirdSame
    · exact congrArg (originalValueKernel planarInclusionMap) fluxSame
  simp only [startupGenuinePrincipalTensorKernel,sum_apply,ContinuousLinearMap.comp_apply,rowSame]
  rfl

/-- Public analytic startup consumer. Genuine native weak rows, exact
original-phase representatives, paid native output moments and known-source
first graphs yield H1 of SAME Q0(a_C), using the literal actual tensor and
unchanged width. No unknown H1, elliptic equation or extra moment is assumed. -/
theorem startupSame_nativeRows_h1 {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (gammaNonnegative : 0 ≤ gamma) (ellNonnegative : 0 ≤ ell) (ellOne : ell ≤ 1)
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
    (rows rawRows : StartupNativeERRows) (psi : StartupL2 1)
    (phase : StartupNativeERRowsRelated (physicalWeight sigma gamma ell) rows rawRows)
    (weak : StartupNativeWeakRows (ell/L) psi rawRows)
    (forceFirst : StartupFirst 2) (thirdFirst : StartupFirst 1)
    (forceBase : base 2 1 openUnitDisk (fun _ => 0) forceFirst = rows.knownForce.field)
    (thirdBase : base 1 1 openUnitDisk (fun _ => 0) thirdFirst = rows.knownThird.field)
    (forceSame : startupGenuineForceKernel admissible data coherent inverseCoherent rows.circle.field = rows.forceCorrection.field)
    (thirdSame : originalThirdCorrectionKernel admissible data coherent inverseCoherent rows.circle.field = rows.thirdCorrection.field)
    (fluxSame : startupGenuinePrincipalFluxKernel admissible data coherent inverseCoherent rows.circle.field = rows.currentFlux.field) :
    ∃ improved : FieldH1, valueInclusion improved =
      startupPlaneExtension (startupCutoffL2 inside insideSmooth insideCompact rows.circle.field) := by
  have phaseRadial : ∀ cell (first second : Spatial), ‖first‖ = ‖second‖ →
      physicalWeight sigma gamma ell cell first = physicalWeight sigma gamma ell cell second := by
    intro cell first second same
    simp only [physicalWeight,same]
  have principal := startupNative_actualPrincipalTensor admissible data coherent inverseCoherent rows forceSame thirdSame fluxSame
  have known (first second : Fin 2) : base 3 1 openUnitDisk (fun _ => 0) (startupKnownTensorFirst forceFirst thirdFirst first second) =
      rows.knownTensor first second := by
    rw [startupKnownTensorFirst_base,forceBase,thirdBase]
    rfl
  apply startupSame_phase_actualTensor_h1 admissible data coherent inverseCoherent gammaNonnegative ellNonnegative ellOne
    outer inside outerSmooth insideSmooth outerCompact insideCompact insideDisk plateau radial regular compatible coarseSmall fineSmall
    rows.circle.field rawRows.circle.field (rows.circle.moment 1) (rows.circle.moment 2)
    (startupKnownTensorFirst forceFirst thirdFirst) rawRows.tensor (rows.tensorMoment 1) (rows.tensorMoment 2)
    (rows.flux (ell/L)) (rawRows.flux (ell/L)) (rows.fluxFirst (ell/L))
    (phase.circle phaseRadial) _ (phase.flux phaseRadial (ell/L))
    rows.circle.first_related rows.circle.second_related _ _ (rows.flux_first (ell/L)) weak.divDiv
  · intro first second
    rw [principal,known]
    exact phase.tensor phaseRadial first second
  · intro first second
    rw [principal,known]
    exact rows.tensor_first first second
  · intro first second
    rw [principal,known]
    exact rows.tensor_second first second

end Grad.CartesianStartup
