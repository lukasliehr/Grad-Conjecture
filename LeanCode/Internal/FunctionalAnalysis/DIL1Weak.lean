import DIL1Tests

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open Grad.WeightedJets
open scoped ContDiff

namespace Grad.SpatialDilation

theorem derivativeTestPairing_pulled (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (index : JetIndex order) (test : TestFunction (expandedDisk radius scale))
    (field : FieldL2 dimension (disk radius)) (cell : ℤ) (vector : PhysicalValue dimension) :
    derivativeTestPairing dimension order (disk radius) index cell vector (pulledTest radius scale test) field =
      scale.val⁻¹ ^ degree index • ∫ point in disk radius,
        Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun
          (scale.val⁻¹ • point) • inner ℂ vector (field point cell) := by
  rw [derivativeTestPairing_apply, pulledTest_derivative]
  simp only [mul_smul]
  rw [integral_smul]

theorem derivativeTestPairing_raw (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (index : JetIndex order) (test : TestFunction (expandedDisk radius scale))
    (field : FieldL2 dimension (disk radius)) (cell : ℤ) (vector : PhysicalValue dimension) :
    derivativeTestPairing dimension order (expandedDisk radius scale) index cell vector test
        (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale field) =
      (scale.val ^ 2)⁻¹ • ∫ point in disk radius,
        Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun
          (scale.val⁻¹ • point) • inner ℂ vector (field point cell) := by
  erw [derivativeTestPairing_apply]
  exact integral_rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale _ field cell vector

theorem scaled_recovery_weak (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order (disk radius) exponent)
    (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : TestFunction (expandedDisk radius scale)) :
    testPairing dimension (expandedDisk radius scale) cell vector test
        ((scale.val ^ degree index : ℂ) • rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
          (Realization.recoveredDerivative dimension order (disk radius) exponent index jet)) =
      (-1 : ℂ) ^ degree index * derivativeTestPairing dimension order (expandedDisk radius scale)
        index cell vector test (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
          (base dimension order (disk radius) exponent jet)) := by
  erw [map_smul, testPairing_rawValue, Realization.recoveredDerivative_weak,
    derivativeTestPairing_pulled, derivativeTestPairing_raw]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_pow, Complex.ofReal_inv]
  have nonzero : (scale.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scale.property.1.ne'
  have cancellation : (scale.val : ℂ) ^ degree index * ((scale.val : ℂ)⁻¹) ^ degree index = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ nonzero, one_pow]
  calc
    _ = ((scale.val : ℂ) ^ degree index * ((scale.val : ℂ)⁻¹) ^ degree index) *
        ((-1 : ℂ) ^ degree index * ((scale.val : ℂ) ^ 2)⁻¹ *
          ∫ point in disk radius, Grad.WeakTesting.orderedTestDerivative (degree index)
            (derivativeWord index) test.toFun (scale.val⁻¹ • point) •
              inner ℂ vector (base dimension order (disk radius) exponent jet point cell)) := by
      simp only [Complex.real_smul]
      ring
    _ = _ := by
      rw [cancellation]
      simp only [Complex.real_smul]
      ring

theorem weak_goal : WeakGoal := by
  intro dimension order radius scale exponent jet index cell vector test smooth compact supported
  change testPairing dimension (expandedDisk radius scale) cell vector ⟨test, smooth, compact, supported⟩
      ((scale.val ^ degree index : ℂ) • rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (Realization.recoveredDerivative dimension order (disk radius) exponent index jet)) =
    (-1 : ℂ) ^ degree index * derivativeTestPairing dimension order (expandedDisk radius scale)
      index cell vector ⟨test, smooth, compact, supported⟩
        (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
          (base dimension order (disk radius) exponent jet))
  exact scaled_recovery_weak dimension order radius scale exponent jet index cell vector _

theorem tupleValue_base (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (tuple : JetTuple dimension order (disk radius)) :
    ambientBase dimension order (expandedDisk radius scale) exponent (tupleValue dimension order radius scale tuple) =
      rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (ambientBase dimension order (disk radius) exponent tuple) := by
  rw [ambientBase_apply, ambientBase_apply]
  change Grad.CellWeights.inverseFieldCLM dimension (expandedDisk radius scale) (exponent (zeroIndex order))
      ((scale.val ^ degree (zeroIndex order) : ℂ) •
        rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale (tuple (zeroIndex order))) = _
  erw [degree_zero, pow_zero, one_smul, rawValue_inverse]
  rfl

theorem tupleValue_recovery (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (tuple : JetTuple dimension order (disk radius)) (index : JetIndex order) :
    Grad.CellWeights.inverseFieldCLM dimension (expandedDisk radius scale) (exponent index)
        (tupleValue dimension order radius scale tuple index) =
      (scale.val ^ degree index : ℂ) • rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (Grad.CellWeights.inverseFieldCLM dimension (disk radius) (exponent index) (tuple index)) := by
  change Grad.CellWeights.inverseFieldCLM dimension (expandedDisk radius scale) (exponent index)
      ((scale.val ^ degree index : ℂ) • rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (tuple index)) = _
  erw [map_smul, rawValue_inverse]
  rfl

theorem tupleValue_mem_graph (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order (disk radius) exponent) :
    tupleValue dimension order radius scale jet.val ∈ jetGraph dimension order (expandedDisk radius scale) exponent := by
  apply (jetGraph_mem dimension order (expandedDisk radius scale) exponent _).mpr
  intro index cell vector test
  have recovery := congrArg (testPairing dimension (expandedDisk radius scale) cell vector test)
    (tupleValue_recovery dimension order radius scale exponent jet.val index)
  change testPairing dimension (expandedDisk radius scale) cell vector test
      (Grad.CellWeights.inverseFieldCLM dimension (expandedDisk radius scale) (exponent index)
        (tupleValue dimension order radius scale jet.val index)) =
    testPairing dimension (expandedDisk radius scale) cell vector test
      ((scale.val ^ degree index : ℂ) • rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (Realization.recoveredDerivative dimension order (disk radius) exponent index jet)) at recovery
  rw [Inclusions.testPairing_inverse, scaled_recovery_weak] at recovery
  rw [tupleValue_base]
  change testPairing dimension (expandedDisk radius scale) cell vector test
      (tupleValue dimension order radius scale jet.val index) =
    _ * derivativeTestPairing dimension order (expandedDisk radius scale) index cell vector test
      (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (base dimension order (disk radius) exponent jet))
  calc
    _ = Grad.CellWeights.positiveFactor (exponent index) cell *
        (Grad.CellWeights.inverseFactor (exponent index) cell *
          testPairing dimension (expandedDisk radius scale) cell vector test
            (tupleValue dimension order radius scale jet.val index)) := by
      rw [← mul_assoc, mul_comm (Grad.CellWeights.positiveFactor _ _),
        Realization.inverse_positiveFactor, one_mul]
    _ = _ := by rw [recovery]; ring

end Grad.SpatialDilation
