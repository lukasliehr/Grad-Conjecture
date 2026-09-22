import AKBE13ProjectedTestsAvoidAxis

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.PDEBootstrap Grad.CartesianStartup Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- A continuous physical disk field has the original radial projection's
exact compact-test transpose. The existing one-cell injection supplies L2;
there is no extra regularity or all-cell summability premise. -/
theorem closedRadialProjection_rawTranspose (raw : ClosedDisk → ComplexEuclidean 2)
    (continuousRaw : Continuous raw) (source : Fin 2) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    (∫ point in openUnitDisk, test point • closedFieldExtension (closedRadialReflectionValue raw) point source) =
      ∑ target : Fin 2, ∫ point in openUnitDisk,
        startupRawQradTest source test target point • closedFieldExtension raw point target := by
  let value : C(ClosedDisk,ComplexEuclidean 2) := ⟨raw,continuousRaw⟩
  let field := apDiskInjection 2 (closedContinuousToDiskL2 value)
  have same : (fun point => field point (0 : ℤ)) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw := by
    filter_upwards [apDiskInjection_ae (closedContinuousToDiskL2 value),closedContinuousToDiskL2_ae value] with point injection actual
    change (apDiskInjection 2 (closedContinuousToDiskL2 value)) point 0 = _
    rw [injection,cellSingle_apply,if_pos rfl,actual]
    rfl
  have projected := originalQrad_closedRepresentative field 0 raw continuousRaw same
  calc
    _ = ∫ point in openUnitDisk, test point • (startupGenuineQradKernel field) point 0 source := by
      apply integral_congr_ae
      filter_upwards [projected] with point actual
      rw [actual]
    _ = _ := startupGenuineQrad_rawTranspose field 0 source test smooth compact
    _ = _ := by
      apply Finset.sum_congr rfl
      intro target _
      apply integral_congr_ae
      filter_upwards [same] with point actual
      rw [actual]

end Grad.ActualCartesianWeakEquations
