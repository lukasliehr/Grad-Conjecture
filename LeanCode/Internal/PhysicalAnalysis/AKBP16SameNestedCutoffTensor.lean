import AKBP15SameCompactDivDivDistribution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.ZeroExtension
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

theorem startupPlaneRestriction_extension (field : StartupL2 3) :
    startupPlaneRestriction (startupPlaneExtension field) = field := by
  change Restriction.fieldRestriction (CellValues 3) (Set.subset_univ openUnitDisk)
    (startupWholePlaneField.symm (startupWholePlaneField
      (fieldExtension (CellValues 3) openUnitDisk openUnitDisk_isOpen.measurableSet field))) = field
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact restriction_extension (CellValues 3) openUnitDisk openUnitDisk_isOpen.measurableSet field

theorem startupCutoff_absorb (outer inside : Spatial → ℝ)
    (outerSmooth : ContDiff ℝ ∞ outer) (insideSmooth : ContDiff ℝ ∞ inside)
    (outerCompact : HasCompactSupport outer) (insideCompact : HasCompactSupport inside)
    (plateau : Set.EqOn outer (fun _ => 1) (tsupport inside)) (field : StartupL2 3) :
    startupCutoffL2 outer outerSmooth outerCompact (startupCutoffL2 inside insideSmooth insideCompact field) =
      startupCutoffL2 inside insideSmooth insideCompact field := by
  have product (point : Spatial) : outer point * inside point = inside point := by
    by_cases zero : inside point = 0
    · simp only [zero,mul_zero]
    · rw [plateau (subset_tsupport inside (Function.mem_support.mpr zero)),one_mul]
  apply startupField_ae_ext
  filter_upwards [startupCutoff_related outer outerSmooth outerCompact (startupCutoffL2 inside insideSmooth insideCompact field),
    startupCutoff_related inside insideSmooth insideCompact field] with point first second
  intro cell
  rw [first cell,second cell,smul_smul,product]

/-- The outer cutoff is one on the inner cutoff's support. This exact
identity replaces the invalid single-cutoff square and preserves the SAME
localized field in the retained whole-plane coefficient operator. -/
theorem startupLocalizedKernel_nested (outer inside : Spatial → ℝ)
    (outerSmooth : ContDiff ℝ ∞ outer) (insideSmooth : ContDiff ℝ ∞ inside)
    (outerCompact : HasCompactSupport outer) (insideCompact : HasCompactSupport inside)
    (plateau : Set.EqOn outer (fun _ => 1) (tsupport inside))
    (kernel : StartupL2 3 →L[ℂ] StartupL2 3)
    (commutes : ∀ field, kernel (startupCutoffL2 inside insideSmooth insideCompact field) =
      startupCutoffL2 inside insideSmooth insideCompact (kernel field)) (field : StartupL2 3) :
    startupLocalizedKernel outer outerSmooth outerCompact kernel
      (startupPlaneExtension (startupCutoffL2 inside insideSmooth insideCompact field)) =
      startupPlaneExtension (startupCutoffL2 inside insideSmooth insideCompact (kernel field)) := by
  rw [startupLocalizedKernel_apply,startupPlaneRestriction_extension,commutes,
    startupCutoff_absorb outer inside outerSmooth insideSmooth outerCompact insideCompact plateau]

theorem startupGenuinePrincipalTensor_nested {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inside : Spatial → ℝ) (outerSmooth : ContDiff ℝ ∞ outer) (insideSmooth : ContDiff ℝ ∞ inside)
    (outerCompact : HasCompactSupport outer) (insideCompact : HasCompactSupport inside)
    (plateau : Set.EqOn outer (fun _ => 1) (tsupport inside))
    (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → inside first = inside second)
    (field : StartupL2 3) (first second : Fin 2) :
    startupLocalizedKernel outer outerSmooth outerCompact (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent first second)
      (startupPlaneExtension (startupCutoffL2 inside insideSmooth insideCompact field)) =
      startupPlaneExtension (startupCutoffL2 inside insideSmooth insideCompact
        (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent first second field)) :=
  startupLocalizedKernel_nested outer inside outerSmooth insideSmooth outerCompact insideCompact plateau
    (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent first second)
    (fun field => startupGenuinePrincipalTensor_cutoff admissible data coherent inverseCoherent inside insideSmooth insideCompact radial field first second) field

end Grad.CartesianStartup
