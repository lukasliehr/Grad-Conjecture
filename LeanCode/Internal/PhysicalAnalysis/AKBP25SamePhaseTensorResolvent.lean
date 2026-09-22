import AKBP17SameActualWeakTensorH1
import AKBP24KnownSourceTensorFirstGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- Exact unweighted compact equation → original-phase equation → two cutoffs
→ both existing resolvents. Every tensor/flux moment is for its actual output;
no frequency multiplier is moved through the coefficient matrix. -/
theorem startupSame_phase_actualTensor_h1 {L sigma gamma ell : ℝ}
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
    (field rawField fieldFirst fieldSecond : StartupL2 3)
    (known : Fin 2 → Fin 2 → StartupFirst 3)
    (rawTensor tensorFirst tensorSecond : Fin 2 → Fin 2 → StartupL2 3)
    (flux rawFlux fluxFirst : Fin 2 → StartupL2 3)
    (fieldSame : StartupRadialRelated (physicalWeight sigma gamma ell) field rawField)
    (tensorSame : ∀ first second, StartupRadialRelated (physicalWeight sigma gamma ell)
      (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent first second field +
        base 3 1 openUnitDisk (fun _ => 0) (known first second)) (rawTensor first second))
    (fluxSame : ∀ direction, StartupRadialRelated (physicalWeight sigma gamma ell) (flux direction) (rawFlux direction))
    (fieldFirstSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) fieldFirst field)
    (fieldSecondSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ 2) fieldSecond field)
    (tensorFirstSame : ∀ first second, StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell)
      (tensorFirst first second)
      (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent first second field +
        base 3 1 openUnitDisk (fun _ => 0) (known first second)))
    (tensorSecondSame : ∀ first second, StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ 2)
      (tensorSecond first second)
      (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent first second field +
        base 3 1 openUnitDisk (fun _ => 0) (known first second)))
    (fluxFirstSame : ∀ direction, StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell)
      (fluxFirst direction) (flux direction))
    (equation : StartupWeakDivDivEquation rawField 0 rawTensor rawFlux) :
    ∃ improved : FieldH1, valueInclusion improved =
      startupPlaneExtension (startupCutoffL2 inside insideSmooth insideCompact field) := by
  let tensor : Fin 2 → Fin 2 → StartupL2 3 := fun first second =>
    startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent first second field +
      base 3 1 openUnitDisk (fun _ => 0) (known first second)
  have weighted := startupSame_phase_divDiv sigma gamma ell gammaNonnegative ellNonnegative ellOne
    field rawField 0 0 fieldFirst fieldSecond tensor rawTensor tensorFirst tensorSecond flux rawFlux fluxFirst
    fieldSame StartupRadialRelated.zero tensorSame fluxSame fieldFirstSame fieldSecondSame
    tensorFirstSame tensorSecondSame fluxFirstSame equation
  have absorbed := startupKnownFirstTensor_absorb field
    (startupPhaseEquationZeroth sigma gamma ell gammaNonnegative ellNonnegative ellOne 0 fieldSecond tensorSecond fluxFirst)
    (fun first second => startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent first second field)
    known (startupPhaseEquationFlux sigma gamma ell gammaNonnegative ellNonnegative ellOne fieldFirst tensorFirst flux) weighted
  exact startupSame_actualWeakTensor_h1 admissible data coherent inverseCoherent outer inside outerSmooth insideSmooth
    outerCompact insideCompact insideDisk plateau radial regular compatible coarseSmall fineSmall field _ _ absorbed

end Grad.CartesianStartup
