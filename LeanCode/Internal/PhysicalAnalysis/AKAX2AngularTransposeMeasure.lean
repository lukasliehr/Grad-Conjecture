import AKAX1AngularCompactTests

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.KernelPullback.Domain
open Grad.RepresentedKernel.WeakDerivatives

/-- Compact tests stay strictly inside the original disk under the angular transpose. -/
theorem startupAngularTest_supported (weight : ℝ → ℝ) (test : Spatial → ℝ)
    (supported : tsupport test ⊆ openUnitDisk) :
    tsupport (startupAngularTest weight test) ⊆ openUnitDisk := by
  have insideBall : tsupport test ⊆ Metric.ball (0 : Spatial) 1 := by
    intro point inside
    rw [Metric.mem_ball, dist_zero_right]
    exact supported inside
  obtain ⟨radius, radiusInside, bound⟩ :=
    exists_pos_lt_subset_ball zero_lt_one (isClosed_tsupport test) insideBall
  intro point inside
  have bounded := startupAngularTest_tsupport weight test radius
    (bound.trans Metric.ball_subset_closedBall) inside
  change ‖point‖ < 1
  have normBound : ‖point‖ ≤ radius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using bounded
  exact normBound.trans_lt radiusInside.2

def startupAngularCompactTest (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (test : Grad.WeightedJets.TestFunction openUnitDisk) : Grad.WeightedJets.TestFunction openUnitDisk where
  toFun := startupAngularTest weight test.toFun
  smooth := startupAngularTest_smooth weight smooth test.toFun test.smooth
  compact := startupAngularTest_compact weight test.toFun test.compact
  supported := startupAngularTest_supported weight test.toFun test.supported

theorem startupRotation_disk_preserving (angle : ℝ) :
    MeasurePreserving (planeRotationEquiv angle) (volume.restrict openUnitDisk)
      (volume.restrict openUnitDisk) :=
  domainMeasurePreserving openUnitDisk openUnitDisk_isOpen.measurableSet
    (planeRotationEquiv angle) (fun point => by
      change ‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1
      rw [LinearIsometryEquiv.norm_map])

theorem startupInverseRotationProduct_preserving :
    MeasurePreserving (fun pair : ℝ × Spatial => (pair.1, planeRotationEquiv (-pair.1) pair.2))
      ((volume.restrict (Icc (0 : ℝ) (2 * Real.pi))).prod (volume.restrict openUnitDisk))
      ((volume.restrict (Icc (0 : ℝ) (2 * Real.pi))).prod (volume.restrict openUnitDisk)) := by
  have measurable : Measurable (fun pair : ℝ × Spatial => planeRotationEquiv (-pair.1) pair.2) := by
    change Measurable (fun pair : ℝ × Spatial => planeRotation (-pair.1) pair.2)
    exact (continuous_planeRotation_joint.comp (continuous_fst.neg.prodMk continuous_snd)).measurable
  exact (MeasurePreserving.id (volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))).skew_product measurable
    (Filter.Eventually.of_forall (fun angle => (startupRotation_disk_preserving (-angle)).map_eq))

/-- Fubini's integrability survives the literal inverse rotation of the spatial variable. -/
theorem startupAngular_transposed_integrable (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (field : StartupL2 3) (cell : ℤ) (vector : PhysicalValue 3)
    (test : Spatial → ℝ) (testMeasurable : Measurable test)
    (testLp : MemLp test 2 (volume.restrict openUnitDisk)) :
    Integrable (fun pair : ℝ × Spatial => test (planeRotationEquiv (-pair.1) pair.2) •
      inner ℂ vector (startupAngularCoefficient 3 weight pair.1 (field pair.2 cell)))
      ((volume.restrict (Icc (0 : ℝ) (2 * Real.pi))).prod (volume.restrict openUnitDisk)) := by
  have original := testedCell_integrable (startupAngularRawData weight smooth)
    cell cell field test testMeasurable testLp vector
  simp only [startupAngularRawData, startupFixedRawData, startupFixedKernelData, if_true] at original
  have transformed := (startupInverseRotationProduct_preserving.integrable_comp
    original.aestronglyMeasurable).mpr original
  simpa only [Function.comp_def, planeRotationEquiv_apply, planeRotation_neg_right] using transformed

end Grad.CartesianStartup
