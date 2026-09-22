import AKBP16SameNestedCutoffTensor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.ZeroExtension
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- The actual small tensor and a genuine compact weak equation force first
regularity of the SAME interior cutoff of the rough field. Phase and original
row specialization are separate proved inputs; no H1 of the unknown occurs. -/
theorem startupSame_actualWeakTensor_h1 {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
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
    (field zeroth : StartupL2 3) (flux : Fin 2 → StartupL2 3)
    (equation : StartupWeakDivDivEquation field zeroth
      (fun first second => startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent first second field) flux) :
    ∃ improved : FieldH1, valueInclusion improved =
      startupPlaneExtension (startupCutoffL2 inside insideSmooth insideCompact field) := by
  let tensor : Fin 2 → Fin 2 → StartupL2 3 :=
    fun first second => startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent first second field
  let kernels : TensorIndex → Grad.PDEBootstrap.FieldL2 →L[ℂ] Grad.PDEBootstrap.FieldL2 :=
    fun index => startupLocalizedKernel outer outerSmooth outerCompact
      (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent index.1 index.2)
  have localized := startupSame_cutoff_divDiv inside insideSmooth insideCompact field zeroth tensor flux equation
  have supported := startupCutoffEquation_supported inside insideSmooth insideCompact field zeroth tensor flux
  have distribution := startupCompact_divDiv_distribution
    (compactLocalizer openUnitDisk (tsupport inside) insideCompact openUnitDisk_isOpen insideDisk)
    (startupCutoffL2 inside insideSmooth insideCompact field)
    (startupCutoffEquationZeroth inside insideSmooth insideCompact field zeroth tensor flux)
    (fun first second => startupCutoffL2 inside insideSmooth insideCompact (tensor first second))
    (startupCutoffEquationFlux inside insideSmooth insideCompact field tensor flux)
    supported.1 supported.2.1 supported.2.2.1 supported.2.2.2 localized
  apply startupSameField_divDiv_h1 kernels regular compatible coarseSmall fineSmall
    (startupPlaneExtension (startupCutoffL2 inside insideSmooth insideCompact field))
    (startupPlaneExtension (startupCutoffEquationZeroth inside insideSmooth insideCompact field zeroth tensor flux))
    (fun direction => -startupPlaneExtension (startupCutoffEquationFlux inside insideSmooth insideCompact field tensor flux direction))
  have nested (first second : Fin 2) := startupGenuinePrincipalTensor_nested admissible data coherent inverseCoherent
    outer inside outerSmooth insideSmooth outerCompact insideCompact plateau radial field first second
  simp only [kernels,Fintype.sum_prod_type,nested,map_neg,Finset.sum_neg_distrib,← sub_eq_add_neg]
  exact distribution

end Grad.CartesianStartup
