import AKBJ21ProjectedScalarAxisRemoval
import AKAD2PuncturedClassicalWeakEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualScalarWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianStartup Grad.CartesianState
open Grad.ActualCartesianWeakEquations Grad.PhysicalAxisEquation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.RepresentedKernel.SpatialProduct

/-- Local compact testing needs only continuity on the punctured disk. -/
theorem scalarPunctured_testIntegrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (raw : Spatial → E) (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (supported : tsupport test ⊆ openUnitDisk) (away : (0 : Spatial) ∉ tsupport test) :
    IntegrableOn (fun point => test point • raw point) openUnitDisk := by
  have puncturedSupport : tsupport test ⊆ openUnitDisk \ {(0 : Spatial)} := by
    intro point member
    refine ⟨supported member,?_⟩
    simpa only [mem_singleton_iff] using (show point ≠ 0 from fun zero => away (zero ▸ member))
  exact (smul_integrable_of_tsupport_subset (openUnitDisk \ {(0 : Spatial)})
    (openUnitDisk_isOpen.sdiff isClosed_singleton) test smooth.continuous compact puncturedSupport raw continuousRaw).integrableOn

/-- A literal scalar mean-free equation has its exact P0 compact transpose, with the source unprojected. -/
theorem scalarProjected_classicalTest (raw : Spatial → ComplexEuclidean 1)
    (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (source : Spatial → ℂ) (sourceIntegrable : IntegrableOn source openUnitDisk)
    (equation : ∀ point : ClosedDisk, 0 < ‖point.val‖ → ‖point.val‖ < 1 →
      source point.val = raw point.val 0 - closedAngularMean (fun closed : ClosedDisk => raw closed.val) point 0)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (supported : tsupport test ⊆ openUnitDisk) (away : (0 : Spatial) ∉ tsupport test) :
    (∫ point in openUnitDisk, test point • source point) =
      ∫ point in openUnitDisk, scalarP0Test test point • raw point 0 := by
  have rawContinuous : ContinuousOn (fun point => raw point 0) (openUnitDisk \ {(0 : Spatial)}) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp_continuousOn continuousRaw
  have first := scalarPunctured_testIntegrable (fun point => raw point 0) rawContinuous test smooth compact supported away
  have averaged := scalarPunctured_testIntegrable (fun point => raw point 0) rawContinuous
    (startupAngularTest (fun _ => 1) test) (startupAngularTest_smooth _ contDiff_const test smooth)
    (startupAngularTest_compact _ test compact) (startupAngularTest_supported _ test supported)
    (originalAngularTest_away (fun _ => 1) test away)
  have sourceTest := Grad.WeightedAxisRemoval.compactTest_smul_integrable (volume.restrict openUnitDisk)
    test smooth compact source sourceIntegrable
  have same : (fun point => test point • source point) =ᵐ[volume.restrict openUnitDisk]
      fun point => test point • raw point 0 - test point • (closedFieldExtension
        (closedAngularMean (fun closed : ClosedDisk => raw closed.val)) point) 0 := by
    have punctured : ∀ᵐ point ∂volume.restrict openUnitDisk, point ∈ openUnitDisk \ {(0 : Spatial)} := by
      rw [← puncturedDisk_restrict_measure]
      exact ae_restrict_mem (openUnitDisk_isOpen.sdiff isClosed_singleton).measurableSet
    filter_upwards [punctured] with point inside
    let closed : ClosedDisk := ⟨point,by change ‖point‖ ≤ 1; exact inside.1.le⟩
    have positive : 0 < ‖point‖ := norm_pos_iff.mpr (by simpa only [mem_singleton_iff] using inside.2)
    have actual := equation closed positive inside.1
    have extension := closedFieldExtension_value (closedAngularMean (fun closed : ClosedDisk => raw closed.val)) closed
    rw [extension,actual,smul_sub]
  have meanIntegrable : IntegrableOn (fun point => test point •
      (closedFieldExtension (closedAngularMean (fun closed : ClosedDisk => raw closed.val)) point) 0) openUnitDisk := by
    apply (MeasureTheory.Integrable.sub first sourceTest).congr
    filter_upwards [same] with point actual
    simp only [Pi.sub_apply]
    rw [actual]
    abel
  calc
    _ = (∫ point in openUnitDisk, test point • raw point 0) -
        ∫ point in openUnitDisk, test point • (closedFieldExtension
          (closedAngularMean (fun closed : ClosedDisk => raw closed.val)) point) 0 :=
      (integral_congr_ae same).trans (integral_sub first meanIntegrable)
    _ = (∫ point in openUnitDisk, test point • raw point 0) -
        ∫ point in openUnitDisk, startupAngularTest (fun _ => 1) test point • raw point 0 := by
      rw [scalarMean_puncturedTranspose raw continuousRaw test smooth compact supported away]
    _ = _ := by
      rw [← integral_sub first averaged]
      apply integral_congr_ae
      filter_upwards [] with point
      exact (sub_smul _ _ _).symm

end Grad.ActualScalarWeakEquations
