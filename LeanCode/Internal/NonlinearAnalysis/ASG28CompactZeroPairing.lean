import ASG27CompactScalarPrimitives

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarPairing_scaled_test (dimension : ℕ) (lower scalar : ℝ) (test : C(ℝ, ℝ))
    (vector : ComplexEuclidean dimension) (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarPairing lower (scalar • test) vector field = scalar • collarPairing lower test vector field := by
  have curves : collarTestCurve (scalar • test) vector = scalar • collarTestCurve test vector := by
    apply ContinuousMap.ext
    intro radius
    exact mul_smul _ _ _
  change inner ℂ (collarContinuousL2 _ lower (collarTestCurve (scalar • test) vector)) field = _
  rw [curves, map_smul, inner_smul_left_eq_smul]
  rfl

/-- AG2's integral-zero compact primitive argument uses only the original
compact C∞ distributional tests. -/
theorem compactWeakZero_pairing (dimension : ℕ) (lower : ℝ) (bounded : lower < 1)
    (field : CollarL2 (ComplexEuclidean dimension) lower) (weak : CompactWeakDerivative dimension lower field 0)
    (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (supported : tsupport test ⊆ Ioo lower 1) (vector : ComplexEuclidean dimension) :
    collarPairing lower ⟨test, smooth.continuous⟩ vector field =
      (∫ radius in lower..1, test radius) •
        collarPairing lower ⟨normalizedInteriorTest lower bounded, (normalizedInteriorTest_smooth lower bounded).continuous⟩ vector field := by
  let average := ∫ radius in lower..1, test radius
  let adjusted := fun radius => test radius - average * normalizedInteriorTest lower bounded radius
  have adjustedSmooth : ContDiff ℝ ∞ adjusted :=
    smooth.sub (contDiff_const.mul (normalizedInteriorTest_smooth lower bounded))
  have adjustedCompact : HasCompactSupport adjusted :=
    compact.sub (HasCompactSupport.mul_left (normalizedInteriorTest_compact lower bounded))
  have adjustedSupported : tsupport adjusted ⊆ Ioo lower 1 := by
    apply (tsupport_sub test (fun radius => average * normalizedInteriorTest lower bounded radius)).trans
    exact union_subset supported
      (tsupport_mul_subset_right.trans (normalizedInteriorTest_support lower bounded))
  have integralZero : (∫ radius in lower..1, adjusted radius) = 0 := by
    rw [show adjusted = fun radius => test radius - average * normalizedInteriorTest lower bounded radius from rfl,
      intervalIntegral.integral_sub (μ := volume) (f := test)
        (g := fun radius => average * normalizedInteriorTest lower bounded radius)
        (smooth.continuous.intervalIntegrable lower 1)
        ((continuous_const.mul (normalizedInteriorTest_smooth lower bounded).continuous).intervalIntegrable lower 1),
      intervalIntegral.integral_const_mul, normalizedInteriorTest_integral, mul_one]
    exact sub_self _
  have primitiveSmooth := scalarAnchoredPrimitive_smooth lower adjusted adjustedSmooth
  obtain ⟨primitiveCompact, primitiveSupported⟩ := scalarAnchoredPrimitive_compact lower bounded adjusted adjustedSmooth
    adjustedCompact adjustedSupported integralZero
  have identity := weak (scalarAnchoredPrimitive lower adjusted) primitiveSmooth primitiveCompact primitiveSupported vector
  rw [map_zero] at identity
  have vanished := neg_eq_zero.mp identity.symm
  have derivative : deriv (scalarAnchoredPrimitive lower adjusted) = adjusted :=
    funext (fun radius => (scalarAnchoredPrimitive_derivative lower adjusted adjustedSmooth.continuous radius).deriv)
  have testMap : (⟨deriv (scalarAnchoredPrimitive lower adjusted),
      (contDiff_infty_iff_deriv.mp primitiveSmooth).2.continuous⟩ : C(ℝ, ℝ)) =
      ⟨test, smooth.continuous⟩ - average •
        ⟨normalizedInteriorTest lower bounded, (normalizedInteriorTest_smooth lower bounded).continuous⟩ := by
    apply ContinuousMap.ext
    intro radius
    exact congrFun derivative radius
  rw [testMap, collarPairing_test_sub, collarPairing_scaled_test, sub_eq_zero] at vanished
  exact vanished

end Grad.AnnularSourceGraph
