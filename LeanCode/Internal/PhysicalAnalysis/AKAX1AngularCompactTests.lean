import AKAS12OriginalB10PrincipalContraction
import AKAS6AngularTestFubini

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped ContDiff Topology

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.PhysicalFamily Grad.ActualSmoothPDE

/-- Actual inverse rotation applied to the test, with the original parameter weight. -/
def startupAngularTest (weight : ℝ → ℝ) (test : Spatial → ℝ) (point : Spatial) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    weight angle * test (planeRotationEquiv (-angle) point)

theorem startupInverseTestRotation_smooth :
    ContDiff ℝ ∞ (fun argument : Spatial × ℝ => planeRotationEquiv (-argument.2) argument.1) := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [planeRotation] <;> fun_prop

theorem startupAngularTest_smooth (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test) :
    ContDiff ℝ ∞ (startupAngularTest weight test) := by
  have smooth : ContDiff ℝ ∞ (fun argument : Spatial × ℝ =>
      weight argument.2 * test (planeRotationEquiv (-argument.2) argument.1)) :=
    (weightSmooth.comp contDiff_snd).mul (testSmooth.comp startupInverseTestRotation_smooth)
  exact contDiff_const.mul (contDiffOn_univ.mp
    (contDiffOn_compactIntegral isOpen_univ smooth.contDiffOn 0 (2 * Real.pi)))

theorem startupAngularTest_tsupport (weight : ℝ → ℝ) (test : Spatial → ℝ)
    (radius : ℝ) (supported : tsupport test ⊆ Metric.closedBall (0 : Spatial) radius) :
    tsupport (startupAngularTest weight test) ⊆ Metric.closedBall (0 : Spatial) radius := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro point nonzero
  by_contra outside
  have row (angle : ℝ) : test (planeRotationEquiv (-angle) point) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro inside
    have bounded := supported inside
    have normEquality : dist (planeRotationEquiv (-angle) point) 0 = dist point 0 := by
      simp only [dist_zero_right, LinearIsometryEquiv.norm_map]
    apply outside
    change dist point 0 ≤ radius
    change dist (planeRotationEquiv (-angle) point) 0 ≤ radius at bounded
    exact normEquality ▸ bounded
  have zero : startupAngularTest weight test point = 0 := by
    simp only [startupAngularTest, row, mul_zero, integral_zero]
  exact nonzero zero

theorem startupAngularTest_compact (weight : ℝ → ℝ) (test : Spatial → ℝ)
    (compact : HasCompactSupport test) : HasCompactSupport (startupAngularTest weight test) := by
  obtain ⟨radius, supported⟩ := compact.isBounded.subset_closedBall (0 : Spatial)
  exact (isCompact_closedBall (0 : Spatial) radius).of_isClosed_subset (isClosed_tsupport _)
    (startupAngularTest_tsupport weight test radius supported)

end Grad.CartesianStartup
