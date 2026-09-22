import AJU2UniformPhysicalJetSummability
import AAZJ5ClosedRadialSeriesDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff Interval ENNReal
namespace Grad.AnnularPhysicalFourier
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularSmoothCore Grad.SourceCollarCoefficients
open Grad.AnnularJointRegularity Grad.AnnularRegularity

theorem sectionIntegral_extension (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (sectionValue : RadialContinuousSection 1 lower) (radius : Icc lower (1 : ℝ)) :
    annularSectionIntegral lower positive bounded radius sectionValue =
      ∫ point in lower..radius.val, radialSectionExtension 1 lower bounded sectionValue point := by
  change radialIntervalIntegral 1 lower radius (radialSectionL2 1 lower positive bounded sectionValue) = _
  rw [radialIntervalIntegral_apply, intervalIntegral.integral_of_le radius.property.1,
    intervalIntegral.integral_of_le radius.property.1, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  apply ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc le_rfl radius.property.2)
  filter_upwards [radialSectionL2_ae 1 lower positive bounded sectionValue] with point equality
  exact equality.symm

/-- The actual closed Hilbert radial jets satisfy the accepted section
integral law, so all subsequent termwise radial differentiation uses their
proved derivatives, including both original endpoints. -/
theorem hilbertRadialJetSection_primitive (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (curve : ℕ → ℝ → CellL2 1)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))
    (order grade : ℕ) (mode : ℤ × ℤ) :
    AnnularSectionDerivative lower positive bounded.le
      (hilbertRadialJetSection lower bounded curve smooth order grade mode)
      (hilbertRadialJetSection lower bounded curve smooth (order + 1) grade mode) := by
  intro radius
  let value := fun point => iteratedDerivWithin order (curve grade) (Icc lower 1) point mode
  let derivative := radialSectionExtension 1 lower bounded.le
    (hilbertRadialJetSection lower bounded curve smooth (order + 1) grade mode)
  have valueContinuous : ContinuousOn value (Icc lower radius.val) :=
    ((lp.evalCLM ℝ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
      (radialJet_continuous lower bounded (curve grade) (smooth grade) order)).mono
      (Icc_subset_Icc le_rfl radius.property.2)
  have law (point : ℝ) (inside : point ∈ Ioo lower radius.val) : HasDerivAt value (derivative point) point := by
    have collar : point ∈ Icc lower 1 := ⟨inside.1.le, inside.2.le.trans radius.property.2⟩
    have differentiated := hilbertRadialJetSection_derivative lower bounded curve smooth order grade mode point collar
    rw [← annularSectionExtension_eval lower bounded.le _ point collar] at differentiated
    exact differentiated.hasDerivAt (Icc_mem_nhds inside.1 (inside.2.trans_le radius.property.2))
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le radius.property.1
    valueContinuous law (derivative.continuous.intervalIntegrable lower radius.val)
  rw [sectionIntegral_extension]
  change value radius.val = value lower + ∫ point in lower..radius.val, derivative point
  rw [fundamental]
  abel

end Grad.AnnularPhysicalFourier
