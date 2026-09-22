import ASG19CompletedPrimitive

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def testAverage (lower : ℝ) (test : C(ℝ, ℝ)) : ℝ := (∫ point in lower..1, test point) / (1 - lower)

def zeroMeanPrimitiveTest (lower : ℝ) (bounded : lower < 1) (test : C(ℝ, ℝ)) : CollarTest lower where
  value := ⟨fun radius => (∫ point in lower..radius, test point) - (radius - lower) * testAverage lower test,
    by
      have continuousPrimitive : Continuous (fun radius => ∫ point in lower..radius, test point) := by
        apply Differentiable.continuous (𝕜 := ℝ)
        intro radius
        exact (intervalIntegral.integral_hasDerivAt_right (test.continuous.intervalIntegrable lower radius)
          test.continuous.stronglyMeasurable.stronglyMeasurableAtFilter test.continuous.continuousAt).differentiableAt
      exact continuousPrimitive.sub ((continuous_id.sub continuous_const).mul continuous_const)⟩
  derivative := test - ContinuousMap.const ℝ (testAverage lower test)
  derivativeLaw := by
    intro radius
    have primitive := intervalIntegral.integral_hasDerivAt_right (test.continuous.intervalIntegrable lower radius)
      test.continuous.stronglyMeasurable.stronglyMeasurableAtFilter test.continuous.continuousAt
    have linear := ((hasDerivAt_id radius).sub_const lower).mul_const (testAverage lower test)
    convert primitive.sub linear using 1 <;> first | rfl | simp only [one_mul, ContinuousMap.sub_apply, ContinuousMap.const_apply]

  lowerZero := by simp
  upperZero := by
    change (∫ point in lower..1, test point) - (1 - lower) * testAverage lower test = 0
    unfold testAverage
    field_simp [(sub_pos.mpr bounded).ne']
    ring

theorem collarPairing_test_sub (dimension : ℕ) (lower : ℝ) (first second : C(ℝ, ℝ))
    (vector : ComplexEuclidean dimension) (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarPairing lower (first - second) vector field =
      collarPairing lower first vector field - collarPairing lower second vector field := by
  have curves : collarTestCurve (first - second) vector =
      collarTestCurve first vector - collarTestCurve second vector := by
    apply ContinuousMap.ext
    intro radius
    exact sub_smul _ _ _
  change inner ℂ (collarContinuousL2 _ lower (collarTestCurve (first - second) vector)) field =
    inner ℂ (collarContinuousL2 _ lower (collarTestCurve first vector)) field -
      inner ℂ (collarContinuousL2 _ lower (collarTestCurve second vector)) field
  rw [curves, map_sub, inner_sub_left]

theorem collarPairing_constant_test (dimension : ℕ) (lower scalar : ℝ)
    (vector : ComplexEuclidean dimension) (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarPairing lower (ContinuousMap.const ℝ scalar) vector field =
      scalar • collarPairing lower (ContinuousMap.const ℝ 1) vector field := by
  have curves : collarTestCurve (ContinuousMap.const ℝ scalar) vector =
      scalar • collarTestCurve (ContinuousMap.const ℝ 1) vector := by
    apply ContinuousMap.ext
    intro radius
    simp [collarTestCurve]
  change inner ℂ (collarContinuousL2 _ lower (collarTestCurve (ContinuousMap.const ℝ scalar) vector)) field = _
  rw [curves, map_smul, inner_smul_left_eq_smul]
  rfl

/-- Primitive tests show that a weakly constant field pairs with every
continuous test exactly as its average does. -/
theorem weakZero_pairing (dimension : ℕ) (lower : ℝ) (bounded : lower < 1)
    (field : CollarL2 (ComplexEuclidean dimension) lower) (weak : CollarWeakDerivative lower field 0)
    (test : C(ℝ, ℝ)) (vector : ComplexEuclidean dimension) :
    collarPairing lower test vector field =
      testAverage lower test • collarPairing lower (ContinuousMap.const ℝ 1) vector field := by
  have identity := weak (zeroMeanPrimitiveTest lower bounded test) vector
  rw [map_zero] at identity
  have vanished := neg_eq_zero.mp identity.symm
  change collarPairing lower (test - ContinuousMap.const ℝ (testAverage lower test)) vector field = 0 at vanished
  rw [collarPairing_test_sub, collarPairing_constant_test, sub_eq_zero] at vanished
  exact vanished

end Grad.AnnularSourceGraph
