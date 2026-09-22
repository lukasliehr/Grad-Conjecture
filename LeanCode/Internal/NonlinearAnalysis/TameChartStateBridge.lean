import TameChartGenuine

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct
open Grad.Constraints.Multipliers

/-! Bridges from the coefficient-level envelopes to the literal Q16 chart
state norms: the tangential and original components against the combined
norm, the planar envelope against the state norm with the literal
`√2^s C_ax` constant, the reordered multiplier bound, and the uniform
envelope bounds of the affine tangential part and of the root factor on
the half ball. -/

variable {parameters : PhaseParameters}

theorem tangentNorm_succ_le_chartStateNorm (grade : ℕ) (state : ChartState parameters) :
    tangentNorm (grade + 1) state.1 ≤ chartStateNorm grade state := by
  have first := originalGradeNorm_nonnegative grade state.2.1
  have second := originalGradeNorm_nonnegative grade state.2.2
  rw [chartStateNorm]
  linarith

theorem field_le_chartStateNorm (grade : ℕ) (state : ChartState parameters) :
    originalGradeNorm grade state.2.1 ≤ chartStateNorm grade state := by
  have first := tangentNorm_nonneg (grade + 1) state.1
  have second := originalGradeNorm_nonnegative grade state.2.2
  rw [chartStateNorm]
  linarith

theorem scalar_le_chartStateNorm (grade : ℕ) (state : ChartState parameters) :
    originalGradeNorm grade state.2.2 ≤ chartStateNorm grade state := by
  have first := tangentNorm_nonneg (grade + 1) state.1
  have second := originalGradeNorm_nonnegative grade state.2.1
  rw [chartStateNorm]
  linarith

/-- The planar envelope against the same-grade state norm. -/
theorem planarEnvelope_le_state (grade : ℕ) (state : ChartState parameters) :
    tangentPlanarEnvelope grade state.1 ≤
      Real.sqrt 2 ^ grade * axisConstant * chartStateNorm grade state := by
  have bridge := tangentPlanarEnvelope_le grade state.1
  have state_le := tangentNorm_succ_le_chartStateNorm grade state
  have sqrt_pow_nonneg : (0 : ℝ) ≤ Real.sqrt 2 ^ grade :=
    pow_nonneg (Real.sqrt_nonneg 2) grade
  have axis_nonneg := axisConstant_pos.le
  calc tangentPlanarEnvelope grade state.1
      ≤ Real.sqrt 2 ^ grade * (axisConstant * tangentNorm (grade + 1) state.1) := bridge
    _ ≤ Real.sqrt 2 ^ grade * (axisConstant * chartStateNorm grade state) := by
        apply mul_le_mul_of_nonneg_left _ sqrt_pow_nonneg
        exact mul_le_mul_of_nonneg_left state_le axis_nonneg
    _ = Real.sqrt 2 ^ grade * axisConstant * chartStateNorm grade state := by ring

/-- The grade-zero planar envelope against the `X⁴` state norm. -/
theorem planarEnvelope_zero_le_state (state : ChartState parameters) :
    tangentPlanarEnvelope 0 state.1 ≤ axisConstant * chartStateNorm 4 state := by
  have bridge := tangentPlanarEnvelope_le 0 state.1
  rw [pow_zero, one_mul] at bridge
  have bridge_one : tangentPlanarEnvelope 0 state.1 ≤
      axisConstant * tangentNorm 1 state.1 := bridge
  have mono : tangentNorm 1 state.1 ≤ tangentNorm 5 state.1 :=
    tangentNorm_mono (by omega) state.1
  have state_le : tangentNorm 5 state.1 ≤ chartStateNorm 4 state :=
    tangentNorm_succ_le_chartStateNorm 4 state
  have axis_nonneg := axisConstant_pos.le
  calc tangentPlanarEnvelope 0 state.1
      ≤ axisConstant * tangentNorm 1 state.1 := bridge_one
    _ ≤ axisConstant * tangentNorm 5 state.1 :=
        mul_le_mul_of_nonneg_left mono axis_nonneg
    _ ≤ axisConstant * chartStateNorm 4 state :=
        mul_le_mul_of_nonneg_left state_le axis_nonneg

theorem chartAxis_planar_le_half {base : ChartState parameters}
    (axis : ChartAxisCondition base) : tangentPlanarEnvelope 0 base.1 ≤ 1 / 2 :=
  (chartAxis_planar_lt_half axis).le

theorem tameMultiplierConstant_nonneg (grade : ℕ) :
    0 ≤ multiplierConstant grade parameters.gamma :=
  multiplierConstant_nonnegative grade parameters.gamma parameters.gamma_pos.le

/-- The multiplier bound with the fixed field pulled to the middle. -/
theorem tameMultiplier_norm_reordered (dimension : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (grade : ℕ)
    (family : TameCoefficient parameters) (field : ACore parameters dimension) :
    originalGradeNorm grade (tameScalarMultiplier dimension family field) ≤
      multiplierConstant grade parameters.gamma * originalGradeNorm grade field *
        coefficientEnvelope grade family := by
  calc originalGradeNorm grade (tameScalarMultiplier dimension family field)
      ≤ multiplierConstant grade parameters.gamma * coefficientEnvelope grade family *
          originalGradeNorm grade field := tameScalarMultiplier_bound dimension family field grade
    _ = multiplierConstant grade parameters.gamma * originalGradeNorm grade field *
          coefficientEnvelope grade family := by ring

/-- Uniform norm bound of the affine tangential part by the planar envelope. -/
theorem chartTangentPart_norm_le (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ family : TangentCoefficient parameters,
        originalGradeNorm grade (chartTangentPart parameters family) ≤
          constant * tangentPlanarEnvelope grade family := by
  have mC := tameMultiplierConstant_nonneg (parameters := parameters) grade
  have y0 := originalGradeNorm_nonnegative grade (tameCoordinateScalarField parameters 0)
  have y1 := originalGradeNorm_nonnegative grade (tameCoordinateScalarField parameters 1)
  refine ⟨‖tameTangentInclusion‖ * (multiplierConstant grade parameters.gamma *
      (originalGradeNorm grade (tameCoordinateScalarField parameters 0) +
        originalGradeNorm grade (tameCoordinateScalarField parameters 1))),
    mul_nonneg (norm_nonneg _) (mul_nonneg mC (add_nonneg y0 y1)), ?_⟩
  intro family
  have inner_le : originalGradeNorm grade
      (tameScalarMultiplier 1 (tangentComponent family 0)
          (tameCoordinateScalarField parameters 0) +
        tameScalarMultiplier 1 (tangentComponent family 1)
          (tameCoordinateScalarField parameters 1)) ≤
      multiplierConstant grade parameters.gamma *
        (originalGradeNorm grade (tameCoordinateScalarField parameters 0) +
          originalGradeNorm grade (tameCoordinateScalarField parameters 1)) *
        tangentPlanarEnvelope grade family := by
    have comp0 := tameMultiplier_norm_reordered 1 grade (tangentComponent family 0)
      (tameCoordinateScalarField parameters 0)
    have comp1 := tameMultiplier_norm_reordered 1 grade (tangentComponent family 1)
      (tameCoordinateScalarField parameters 1)
    have env0 := tangentComponent_envelope_le grade family 0
    have env1 := tangentComponent_envelope_le grade family 1
    have step1 := originalGradeNorm_add_le grade
      (tameScalarMultiplier 1 (tangentComponent family 0)
        (tameCoordinateScalarField parameters 0))
      (tameScalarMultiplier 1 (tangentComponent family 1)
        (tameCoordinateScalarField parameters 1))
    have step2 := add_le_add comp0 comp1
    have step3 := add_le_add
      (mul_le_mul_of_nonneg_left env0 (mul_nonneg mC y0))
      (mul_le_mul_of_nonneg_left env1 (mul_nonneg mC y1))
    exact (step1.trans (step2.trans step3)).trans_eq (by ring)
  rw [chartTangentPart]
  have outer_le := valueMapCore_bound tameTangentInclusion
    (tameScalarMultiplier 1 (tangentComponent family 0)
        (tameCoordinateScalarField parameters 0) +
      tameScalarMultiplier 1 (tangentComponent family 1)
        (tameCoordinateScalarField parameters 1)) grade
  have chain := outer_le.trans
    (mul_le_mul_of_nonneg_left inner_le (norm_nonneg tameTangentInclusion))
  exact chain.trans_eq (by ring)

/-- Uniform envelope bound of the root factor on the half ball. -/
theorem rootQuadratic_envelope_le_state (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ family : TangentCoefficient parameters,
        tangentPlanarEnvelope 0 family ≤ 1 / 2 →
        coefficientEnvelope grade (tameRootShifted 0 (tangentQuadratic family)) ≤
          constant * (1 + tangentPlanarEnvelope grade family) := by
  have head_nonneg : 0 ≤ |rootDerivativeCoefficient 0 0| * Real.exp parameters.sigma0 :=
    mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have slope_nonneg : 0 ≤ rootSlopeBound 0 grade (5 / 8) :=
    rootSlopeBound_nonneg 0 grade (by norm_num)
  have power_nonneg : (0 : ℝ) ≤ 2 ^ (grade + 1) := pow_nonneg (by norm_num) _
  refine ⟨|rootDerivativeCoefficient 0 0| * Real.exp parameters.sigma0 +
      rootSlopeBound 0 grade (5 / 8) * 2 ^ (grade + 1),
    add_nonneg head_nonneg (mul_nonneg slope_nonneg power_nonneg), ?_⟩
  intro family ball
  have planar_zero_nonneg := tangentPlanarEnvelope_nonneg 0 family
  have planar_grade_nonneg := tangentPlanarEnvelope_nonneg grade family
  have planar_small : tangentPlanarEnvelope 0 family < 1 :=
    lt_of_le_of_lt ball (by norm_num)
  have quad_small := tangentQuadratic_small planar_small
  have quad_quarter : coefficientEnvelope 0 (tangentQuadratic family) ≤ 1 / 4 := by
    have square_le : tangentPlanarEnvelope 0 family * tangentPlanarEnvelope 0 family ≤
        (1 / 2 : ℝ) * (1 / 2) :=
      mul_le_mul ball ball planar_zero_nonneg (by norm_num)
    have quad_le := tangentQuadratic_envelope_zero_le family
    linarith
  have radius_le : rootSmallRadius (tangentQuadratic family) ≤ 5 / 8 := by
    rw [rootSmallRadius]
    linarith
  have slope_bound := tameRootShifted_envelope_le_slope 0 grade quad_small
    (by norm_num : (5 : ℝ) / 8 < 1) radius_le
  have quad_grade_le := tangentQuadratic_envelope_le grade family
  have product_le : tangentPlanarEnvelope grade family * tangentPlanarEnvelope 0 family ≤
      tangentPlanarEnvelope grade family := by
    calc tangentPlanarEnvelope grade family * tangentPlanarEnvelope 0 family
        ≤ tangentPlanarEnvelope grade family * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) planar_grade_nonneg
      _ = tangentPlanarEnvelope grade family := mul_one _
  calc coefficientEnvelope grade (tameRootShifted 0 (tangentQuadratic family))
      ≤ |rootDerivativeCoefficient 0 0| * Real.exp parameters.sigma0 +
          rootSlopeBound 0 grade (5 / 8) *
            coefficientEnvelope grade (tangentQuadratic family) := slope_bound
    _ ≤ |rootDerivativeCoefficient 0 0| * Real.exp parameters.sigma0 +
          rootSlopeBound 0 grade (5 / 8) *
            ((2 : ℝ) ^ (grade + 1) *
              (tangentPlanarEnvelope grade family * tangentPlanarEnvelope 0 family)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left quad_grade_le slope_nonneg)
    _ ≤ |rootDerivativeCoefficient 0 0| * Real.exp parameters.sigma0 +
          rootSlopeBound 0 grade (5 / 8) *
            ((2 : ℝ) ^ (grade + 1) * tangentPlanarEnvelope grade family) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left product_le power_nonneg) slope_nonneg)
    _ ≤ (|rootDerivativeCoefficient 0 0| * Real.exp parameters.sigma0 +
          rootSlopeBound 0 grade (5 / 8) * 2 ^ (grade + 1)) *
          (1 + tangentPlanarEnvelope grade family) := by
        nlinarith [mul_nonneg (mul_nonneg slope_nonneg power_nonneg) planar_grade_nonneg,
          mul_nonneg head_nonneg planar_grade_nonneg]

end Grad.NonlinearQuotientBounds
