import AKBP2SameOriginalCorrectedERRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

theorem startupCoordinate_value_component {input output : ℕ} (mapping : OperatorValue input output)
    (target : Fin output) (source : Fin input) (constant : ℂ)
    (law : ∀ value, mapping value target = constant * value source)
    (field : StartupL2 input) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell target test (originalValueKernel mapping field) =
      constant * startupCoordinateTestPairing cell source test field := by
  rw [startupCoordinateTestPairing_apply, startupCoordinateTestPairing_apply, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) field] with point value
  change ∀ index : ℤ, originalValueKernel mapping field point index = mapping (field point index) at value
  rw [value cell, law]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
  ring

theorem startupAdjoint_embedding_component {input : ℕ} (mapping : OperatorValue 3 3)
    (embedding : OperatorValue input 3) (target : Fin 3) (source : Fin input) (constant : ℂ)
    (law : ∀ value, mapping (embedding value) target = constant * value source)
    (field : StartupL2 input) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupTestPairing cell (mapping.adjoint (EuclideanSpace.single target 1)) test
      (originalValueKernel embedding field) = constant * startupCoordinateTestPairing cell source test field := by
  have transpose := congrArg (fun pairing : StartupL2 3 →L[ℂ] ℂ => pairing (originalValueKernel embedding field))
    (startupTestPairing_valueMap mapping cell (EuclideanSpace.single target 1) test)
  change startupCoordinateTestPairing cell target test
    (originalValueKernel mapping (originalValueKernel embedding field)) = _ at transpose
  have composition := congrArg (fun operator : StartupL2 input →L[ℂ] StartupL2 3 => operator field)
    (originalValueKernel_comp mapping embedding)
  change originalValueKernel mapping (originalValueKernel embedding field) =
    originalValueKernel (mapping.comp embedding) field at composition
  rw [composition] at transpose
  exact transpose.symm.trans (startupCoordinate_value_component (mapping.comp embedding) target source constant law field cell test)

theorem startupPrincipalEntry_pairing (outer inner : Fin 2) (target : Fin 3)
    (field : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupTestPairing cell ((startupPlanarEntryMap outer inner).adjoint (EuclideanSpace.single target 1)) test
      (originalValueKernel planarInclusionMap field) =
      (if target = outer.castSucc then 1 else 0 : ℂ) * startupCoordinateTestPairing cell inner test field := by
  apply startupAdjoint_embedding_component
  intro value
  fin_cases outer <;> fin_cases inner <;> fin_cases target <;>
    simp [startupPlanarEntryMap, planarInclusionMap, planarPartMap, LinearMap.toContinuousLinearMap]

theorem startupPrincipalRotatedEntry_pairing (outer inner : Fin 2) (target : Fin 3)
    (field : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupTestPairing cell ((startupPlanarRotatedEntryMap outer inner).adjoint (EuclideanSpace.single target 1)) test
      (originalValueKernel planarInclusionMap field) =
      (if target = 0 then (if outer = 1 then -1 else 0) else
        if target = 1 then (if outer = 0 then 1 else 0) else 0 : ℂ) *
        startupCoordinateTestPairing cell inner test field := by
  apply startupAdjoint_embedding_component
  intro value
  fin_cases outer <;> fin_cases inner <;> fin_cases target <;>
    simp [startupPlanarRotatedEntryMap, planarInclusionMap, planarPartMap, quarterValueMap,
      quarterValueLinear, LinearMap.toContinuousLinearMap]

theorem startupToroidalEmbedding_pairing (target : Fin 3) (field : StartupL2 1)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupTestPairing cell (EuclideanSpace.single target 1) test (originalValueKernel toroidalInclusionMap field) =
      (if target = 2 then 1 else 0 : ℂ) * startupCoordinateTestPairing cell 0 test field := by
  change startupCoordinateTestPairing cell target test _ = _
  apply startupCoordinate_value_component
  intro value
  fin_cases target <;> simp [toroidalInclusionMap, LinearMap.toContinuousLinearMap]

end Grad.CartesianStartup
