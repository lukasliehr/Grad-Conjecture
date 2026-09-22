import AKBE12ClosedRepresentativeRadialProjection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.ActualCartesianWeakEquations
open Grad.Constraints Grad.PDEBootstrap Grad.CartesianStartup Grad.ClosedJets Grad.GaugeCoefficients.Radial Grad.WeightedJets

/-- The angular transpose retains a neighborhood of the axis on which a
compact test vanishes. It never transports support toward the axis. -/
theorem originalAngularTest_away (weight : ℝ → ℝ) (test : Spatial → ℝ)
    (away : (0 : Spatial) ∉ tsupport test) :
    (0 : Spatial) ∉ tsupport (startupAngularTest weight test) := by
  have germ := notMem_tsupport_iff_eventuallyEq.mp away
  obtain ⟨radius,positive,near⟩ := Metric.mem_nhds_iff.mp germ
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [Metric.ball_mem_nhds (0 : Spatial) positive] with point inside
  have row (angle : ℝ) : test (planeRotationEquiv (-angle) point) = 0 := by
    apply near
    simpa only [Metric.mem_ball,dist_zero_right,LinearIsometryEquiv.norm_map] using inside
  simp only [startupAngularTest,row,mul_zero,integral_zero,Pi.zero_apply]

theorem originalReflectedTest_away (test : Spatial → ℝ)
    (away : (0 : Spatial) ∉ tsupport test) :
    (0 : Spatial) ∉ tsupport (fun point => test (cartesianReflectionEquiv point)) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have pulled := (notMem_tsupport_iff_eventuallyEq.mp away).comp_tendsto
    (show Tendsto cartesianReflectionEquiv (𝓝 (0 : Spatial)) (𝓝 0) by
      simpa only [map_zero] using cartesianReflectionEquiv.continuous.tendsto (0 : Spatial))
  filter_upwards [pulled] with point actual
  exact actual

/-- Every actual radial-projected scalar test remains strictly away from
 the axis, as required for classical integration by parts. -/
theorem originalRawQradTest_away (source target : Fin 2) (test : Spatial → ℝ)
    (away : (0 : Spatial) ∉ tsupport test) :
    (0 : Spatial) ∉ tsupport (startupRawQradTest source test target) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp away,
    notMem_tsupport_iff_eventuallyEq.mp (originalAngularTest_away (fun angle => startupInverseRotationEntry source target (-angle)) test away),
    notMem_tsupport_iff_eventuallyEq.mp (originalAngularTest_away (fun angle => startupInverseRotationEntry source target (-angle))
      (fun point => test (cartesianReflectionEquiv point)) (originalReflectedTest_away test away))]
    with point first average reflected
  simp [startupRawQradTest,first,average,reflected]

/-- The same projected tests also preserve the original open disk. -/
theorem originalRawQradTest_supported (source target : Fin 2) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (supported : tsupport test ⊆ openUnitDisk) :
    tsupport (startupRawQradTest source test target) ⊆ openUnitDisk :=
  (startupQradTestComponent target source ⟨test,smooth,compact,supported⟩).supported

end Grad.ActualCartesianWeakEquations
