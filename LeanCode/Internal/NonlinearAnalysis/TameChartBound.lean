import TameChartStateBridge

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct
open Grad.Constraints.Multipliers

/-! The exact Q20 one-high bound of the chart derivative family: the tower's
range estimate converted from planar envelopes to the literal Q16 state
norms, the multiplier and seed constants absorbed, and the affine order-one
parts landing in the one-high sum. -/

variable {parameters : PhaseParameters}

/-- The low index product against the `X⁴` state norms. -/
theorem lowIndexProd_le_state {order : ℕ}
    (directions : Fin order → ChartState parameters) :
    lowIndexProd (chartTangentDirections directions) (List.range order) ≤
      (1 + axisConstant) ^ order *
        ∏ position, chartStateNorm 4 (directions position) := by
  have axis_nonneg := axisConstant_pos.le
  rw [lowIndexProd_range]
  have convert : (∏ index : Fin order,
      tangentPlanarEnvelope 0 (chartTangentDirections directions index.val)) =
      ∏ index : Fin order, tangentPlanarEnvelope 0 (directions index).1 :=
    Finset.prod_congr rfl fun index _ => by
      rw [chartTangentDirections_fin directions index]
  rw [convert]
  have pointwise : ∀ index ∈ (Finset.univ : Finset (Fin order)),
      tangentPlanarEnvelope 0 (directions index).1 ≤
        (1 + axisConstant) * chartStateNorm 4 (directions index) := by
    intro index _
    have zero_le := planarEnvelope_zero_le_state (directions index)
    have state_nonneg := chartStateNorm_nonneg 4 (directions index)
    nlinarith
  have entries_nonneg : ∀ index ∈ (Finset.univ : Finset (Fin order)),
      0 ≤ tangentPlanarEnvelope 0 (directions index).1 :=
    fun index _ => tangentPlanarEnvelope_nonneg 0 (directions index).1
  calc (∏ index : Fin order, tangentPlanarEnvelope 0 (directions index).1)
      ≤ ∏ index, (1 + axisConstant) * chartStateNorm 4 (directions index) :=
        Finset.prod_le_prod entries_nonneg pointwise
    _ = (1 + axisConstant) ^ order *
          ∏ position, chartStateNorm 4 (directions position) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

/-- The one-high index sum against the literal state-norm one-high sum. -/
theorem oneHighIndex_le_state (grade : ℕ) {order : ℕ}
    (directions : Fin order → ChartState parameters) :
    oneHighIndex grade (chartTangentDirections directions) (List.range order) ≤
      Real.sqrt 2 ^ grade * axisConstant * (1 + axisConstant) ^ order *
        ∑ position, chartStateNorm grade (directions position) *
          ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (directions other) := by
  have axis_nonneg := axisConstant_pos.le
  have one_le_base : (1 : ℝ) ≤ 1 + axisConstant := by linarith
  rw [oneHighIndex_range]
  have convert : (∑ index : Fin order,
      tangentPlanarEnvelope grade (chartTangentDirections directions index.val) *
        ∏ other ∈ Finset.univ.erase index,
          tangentPlanarEnvelope 0 (chartTangentDirections directions other.val)) =
      ∑ index : Fin order, tangentPlanarEnvelope grade (directions index).1 *
        ∏ other ∈ Finset.univ.erase index,
          tangentPlanarEnvelope 0 (directions other).1 := by
    apply Finset.sum_congr rfl
    intro index _
    rw [chartTangentDirections_fin directions index]
    congr 1
    exact Finset.prod_congr rfl fun other _ => by
      rw [chartTangentDirections_fin directions other]
  rw [convert]
  have pointwise : ∀ index ∈ (Finset.univ : Finset (Fin order)),
      tangentPlanarEnvelope grade (directions index).1 *
        ∏ other ∈ Finset.univ.erase index, tangentPlanarEnvelope 0 (directions other).1 ≤
      Real.sqrt 2 ^ grade * axisConstant * (1 + axisConstant) ^ order *
        (chartStateNorm grade (directions index) *
          ∏ other ∈ Finset.univ.erase index, chartStateNorm 4 (directions other)) := by
    intro index _
    have high_le := planarEnvelope_le_state grade (directions index)
    have erase_entries_nonneg : ∀ other ∈ Finset.univ.erase index,
        0 ≤ tangentPlanarEnvelope 0 (directions other).1 :=
      fun other _ => tangentPlanarEnvelope_nonneg 0 (directions other).1
    have erase_pointwise : ∀ other ∈ Finset.univ.erase index,
        tangentPlanarEnvelope 0 (directions other).1 ≤
          (1 + axisConstant) * chartStateNorm 4 (directions other) := by
      intro other _
      have zero_le := planarEnvelope_zero_le_state (directions other)
      have state_nonneg := chartStateNorm_nonneg 4 (directions other)
      nlinarith
    have card_le : (Finset.univ.erase index).card ≤ order := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ index), Finset.card_univ,
        Fintype.card_fin]
      omega
    have erase_prod_nonneg : 0 ≤ ∏ other ∈ Finset.univ.erase index,
        chartStateNorm 4 (directions other) :=
      Finset.prod_nonneg fun other _ => chartStateNorm_nonneg 4 (directions other)
    have low_le : (∏ other ∈ Finset.univ.erase index,
        tangentPlanarEnvelope 0 (directions other).1) ≤
        (1 + axisConstant) ^ order *
          ∏ other ∈ Finset.univ.erase index, chartStateNorm 4 (directions other) := by
      calc (∏ other ∈ Finset.univ.erase index,
            tangentPlanarEnvelope 0 (directions other).1)
          ≤ ∏ other ∈ Finset.univ.erase index,
              (1 + axisConstant) * chartStateNorm 4 (directions other) :=
            Finset.prod_le_prod erase_entries_nonneg erase_pointwise
        _ = (1 + axisConstant) ^ (Finset.univ.erase index).card *
              ∏ other ∈ Finset.univ.erase index, chartStateNorm 4 (directions other) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
        _ ≤ (1 + axisConstant) ^ order *
              ∏ other ∈ Finset.univ.erase index, chartStateNorm 4 (directions other) :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ one_le_base card_le) erase_prod_nonneg
    have high_nonneg : 0 ≤ Real.sqrt 2 ^ grade * axisConstant *
        chartStateNorm grade (directions index) :=
      mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) grade) axis_nonneg)
        (chartStateNorm_nonneg grade (directions index))
    have low_entry_nonneg : 0 ≤ ∏ other ∈ Finset.univ.erase index,
        tangentPlanarEnvelope 0 (directions other).1 :=
      Finset.prod_nonneg erase_entries_nonneg
    have combined := mul_le_mul high_le low_le low_entry_nonneg high_nonneg
    exact combined.trans_eq (by ring)
  calc (∑ index : Fin order, tangentPlanarEnvelope grade (directions index).1 *
        ∏ other ∈ Finset.univ.erase index, tangentPlanarEnvelope 0 (directions other).1)
      ≤ ∑ index : Fin order, Real.sqrt 2 ^ grade * axisConstant *
          (1 + axisConstant) ^ order * (chartStateNorm grade (directions index) *
            ∏ other ∈ Finset.univ.erase index, chartStateNorm 4 (directions other)) :=
        Finset.sum_le_sum pointwise
    _ = Real.sqrt 2 ^ grade * axisConstant * (1 + axisConstant) ^ order *
          ∑ position, chartStateNorm grade (directions position) *
            ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (directions other) := by
        rw [Finset.mul_sum]

/-- The tower's range form against the literal one-high bracket. -/
theorem towerRange_le_bracket (grade : ℕ) {order : ℕ}
    (base : ChartState parameters) (directions : Fin order → ChartState parameters) :
    (1 + tangentPlanarEnvelope grade base.1) *
        lowIndexProd (chartTangentDirections directions) (List.range order) +
      oneHighIndex grade (chartTangentDirections directions) (List.range order) ≤
      (1 + Real.sqrt 2 ^ grade * axisConstant) * (1 + axisConstant) ^ order *
        ((1 + chartStateNorm grade base) *
            ∏ position, chartStateNorm 4 (directions position) +
          ∑ position, chartStateNorm grade (directions position) *
            ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (directions other)) := by
  have axis_nonneg := axisConstant_pos.le
  have sqrtK_nonneg : (0 : ℝ) ≤ Real.sqrt 2 ^ grade * axisConstant :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) grade) axis_nonneg
  have base_pow_nonneg : (0 : ℝ) ≤ (1 + axisConstant) ^ order :=
    pow_nonneg (by linarith) order
  have base_nonneg := chartStateNorm_nonneg grade base
  have prod_nonneg : 0 ≤ ∏ position, chartStateNorm 4 (directions position) :=
    Finset.prod_nonneg fun position _ => chartStateNorm_nonneg 4 (directions position)
  have sum_nonneg : 0 ≤ ∑ position, chartStateNorm grade (directions position) *
      ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (directions other) :=
    Finset.sum_nonneg fun position _ =>
      mul_nonneg (chartStateNorm_nonneg grade (directions position))
        (Finset.prod_nonneg fun other _ => chartStateNorm_nonneg 4 (directions other))
  have low_nonneg := lowIndexProd_nonneg
    (chartTangentDirections directions) (List.range order)
  have base_high := planarEnvelope_le_state grade base
  have one_plus_le : 1 + tangentPlanarEnvelope grade base.1 ≤
      (1 + Real.sqrt 2 ^ grade * axisConstant) * (1 + chartStateNorm grade base) := by
    nlinarith
  have low_le := lowIndexProd_le_state directions
  have high_le := oneHighIndex_le_state grade directions
  have first_piece := mul_le_mul one_plus_le low_le low_nonneg
    (mul_nonneg (by linarith) (by linarith))
  have first_piece' : (1 + tangentPlanarEnvelope grade base.1) *
      lowIndexProd (chartTangentDirections directions) (List.range order) ≤
      (1 + Real.sqrt 2 ^ grade * axisConstant) * (1 + axisConstant) ^ order *
        ((1 + chartStateNorm grade base) *
          ∏ position, chartStateNorm 4 (directions position)) :=
    first_piece.trans_eq (by ring)
  have second_piece : oneHighIndex grade (chartTangentDirections directions)
      (List.range order) ≤
      (1 + Real.sqrt 2 ^ grade * axisConstant) * (1 + axisConstant) ^ order *
        ∑ position, chartStateNorm grade (directions position) *
          ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (directions other) := by
    apply high_le.trans
    have factor_le : Real.sqrt 2 ^ grade * axisConstant * (1 + axisConstant) ^ order ≤
        (1 + Real.sqrt 2 ^ grade * axisConstant) * (1 + axisConstant) ^ order :=
      mul_le_mul_of_nonneg_right (by linarith) base_pow_nonneg
    exact mul_le_mul_of_nonneg_right factor_le sum_nonneg
  exact (add_le_add first_piece' second_piece).trans_eq (by ring)

/-- The tower multiplied into the seed field, against the literal bracket. -/
theorem towerMultiplier_norm_bound (parameters : PhaseParameters)
    (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain) (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : ChartState parameters) (directions : Fin order → ChartState parameters),
        ChartAxisCondition base →
        originalGradeNorm grade (tameScalarMultiplier 3
            (chartTower order base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside)) ≤
          constant * ((1 + chartStateNorm grade base) *
              ∏ position, chartStateNorm 4 (directions position) +
            ∑ position, chartStateNorm grade (directions position) *
              ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (directions other)) := by
  have ballNonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have ballLt : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨towerC, towerC_nonneg, towerBound⟩ :=
    chartTower_range_envelope_le (parameters := parameters) grade order ballNonneg ballLt
  have mC_nonneg := tameMultiplierConstant_nonneg (parameters := parameters) grade
  have field_nonneg := originalGradeNorm_nonnegative grade
    (tameSeedField parameters seed inside)
  have mCF_nonneg : 0 ≤ multiplierConstant grade parameters.gamma *
      originalGradeNorm grade (tameSeedField parameters seed inside) :=
    mul_nonneg mC_nonneg field_nonneg
  have sqrtK_nonneg : (0 : ℝ) ≤ Real.sqrt 2 ^ grade * axisConstant :=
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) grade) axisConstant_pos.le
  have base_pow_nonneg : (0 : ℝ) ≤ (1 + axisConstant) ^ order :=
    pow_nonneg (by have := axisConstant_pos; linarith) order
  refine ⟨multiplierConstant grade parameters.gamma *
      originalGradeNorm grade (tameSeedField parameters seed inside) * towerC *
      ((1 + Real.sqrt 2 ^ grade * axisConstant) * (1 + axisConstant) ^ order),
    mul_nonneg (mul_nonneg mCF_nonneg towerC_nonneg)
      (mul_nonneg (by linarith) base_pow_nonneg), ?_⟩
  intro base directions axis
  have env_le := towerBound base.1 (chartTangentDirections directions)
    (chartAxis_planar_le_half axis)
  have range_le := towerRange_le_bracket grade base directions
  have mult_le := tameMultiplier_norm_reordered 3 grade
    (chartTower order base.1 (chartTangentDirections directions))
    (tameSeedField parameters seed inside)
  have step2 := mult_le.trans (mul_le_mul_of_nonneg_left env_le mCF_nonneg)
  have step3 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left range_le towerC_nonneg) mCF_nonneg
  exact (step2.trans step3).trans_eq (by ring)

/-- The Q20 one-high bound of the full derivative family on the axis ball. -/
theorem chartDerivativeFamily_bound (parameters : PhaseParameters)
    (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain) (grade : ℕ) :
    ∀ order : ℕ, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : ChartState parameters) (directions : Fin order → ChartState parameters),
        ChartAxisCondition base →
        chartOutputNorm grade
            (chartDerivativeFamily parameters seed inside order base directions) ≤
          constant * ((1 + chartStateNorm grade base) *
              ∏ position, chartStateNorm 4 (directions position) +
            ∑ position, chartStateNorm grade (directions position) *
              ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (directions other))
  | 0 => by
    obtain ⟨rootC, rootC_nonneg, rootBound⟩ :=
      rootQuadratic_envelope_le_state (parameters := parameters) grade
    obtain ⟨tangC, tangC_nonneg, tangBound⟩ :=
      chartTangentPart_norm_le (parameters := parameters) grade
    have mC_nonneg := tameMultiplierConstant_nonneg (parameters := parameters) grade
    have field_nonneg := originalGradeNorm_nonnegative grade
      (tameSeedField parameters seed inside)
    have mCF_nonneg : 0 ≤ multiplierConstant grade parameters.gamma *
        originalGradeNorm grade (tameSeedField parameters seed inside) :=
      mul_nonneg mC_nonneg field_nonneg
    have sqrtK_nonneg : (0 : ℝ) ≤ Real.sqrt 2 ^ grade * axisConstant :=
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) grade) axisConstant_pos.le
    have w_nonneg := originalGradeNorm_nonnegative grade
      (tameSeedScalar parameters seed inside)
    refine ⟨multiplierConstant grade parameters.gamma *
        originalGradeNorm grade (tameSeedField parameters seed inside) * rootC *
        (1 + Real.sqrt 2 ^ grade * axisConstant) +
        tangC * (Real.sqrt 2 ^ grade * axisConstant) +
        originalGradeNorm grade (tameSeedScalar parameters seed inside) + 2,
      by positivity, ?_⟩
    intro base directions axis
    rw [Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]
    have N_nonneg := chartStateNorm_nonneg grade base
    have ball := chartAxis_planar_le_half axis
    have root_reordered := tameMultiplier_norm_reordered 3 grade
      (tameRootShifted 0 (tangentQuadratic base.1)) (tameSeedField parameters seed inside)
    have root_env := rootBound base.1 ball
    have planar_le := planarEnvelope_le_state grade base
    have one_plus_le : 1 + tangentPlanarEnvelope grade base.1 ≤
        (1 + Real.sqrt 2 ^ grade * axisConstant) * (1 + chartStateNorm grade base) := by
      nlinarith
    have env_le2 := root_env.trans (mul_le_mul_of_nonneg_left one_plus_le rootC_nonneg)
    have root_le := (root_reordered.trans
      (mul_le_mul_of_nonneg_left env_le2 mCF_nonneg)).trans_eq
      (by ring : multiplierConstant grade parameters.gamma *
          originalGradeNorm grade (tameSeedField parameters seed inside) *
          (rootC * ((1 + Real.sqrt 2 ^ grade * axisConstant) *
            (1 + chartStateNorm grade base))) =
        multiplierConstant grade parameters.gamma *
          originalGradeNorm grade (tameSeedField parameters seed inside) * rootC *
          (1 + Real.sqrt 2 ^ grade * axisConstant) * (1 + chartStateNorm grade base))
    have tangent_raw := tangBound base.1
    have tangent_le : originalGradeNorm grade (chartTangentPart parameters base.1) ≤
        tangC * (Real.sqrt 2 ^ grade * axisConstant) * (1 + chartStateNorm grade base) := by
      have chain := tangent_raw.trans (mul_le_mul_of_nonneg_left planar_le tangC_nonneg)
      nlinarith [mul_nonneg tangC_nonneg sqrtK_nonneg]
    have v_le := field_le_chartStateNorm grade base
    have s_le := scalar_le_chartStateNorm grade base
    have w_le : originalGradeNorm grade (tameSeedScalar parameters seed inside) ≤
        originalGradeNorm grade (tameSeedScalar parameters seed inside) *
          (1 + chartStateNorm grade base) := by
      nlinarith [mul_nonneg w_nonneg N_nonneg]
    have split1 := (originalGradeNorm_add_le grade
        (tameScalarMultiplier 3 (tameRootShifted 0 (tangentQuadratic base.1))
            (tameSeedField parameters seed inside) +
          chartTangentPart parameters base.1) base.2.1).trans
      (add_le_add (originalGradeNorm_add_le grade _ _) le_rfl)
    have split2 := originalGradeNorm_add_le grade
      (tameSeedScalar parameters seed inside) base.2.2
    have combined : originalGradeNorm grade
        (tameScalarMultiplier 3 (tameRootShifted 0 (tangentQuadratic base.1))
            (tameSeedField parameters seed inside) +
          chartTangentPart parameters base.1 + base.2.1) +
        originalGradeNorm grade (tameSeedScalar parameters seed inside + base.2.2) ≤
        (multiplierConstant grade parameters.gamma *
          originalGradeNorm grade (tameSeedField parameters seed inside) * rootC *
          (1 + Real.sqrt 2 ^ grade * axisConstant) +
          tangC * (Real.sqrt 2 ^ grade * axisConstant) +
          originalGradeNorm grade (tameSeedScalar parameters seed inside) + 2) *
          (1 + chartStateNorm grade base) := by
      nlinarith [split1, split2, root_le, tangent_le, v_le, s_le, w_le]
    exact combined
  | 1 => by
    obtain ⟨towC, towC_nonneg, towBound⟩ :=
      towerMultiplier_norm_bound parameters seed inside grade 1
    obtain ⟨tangC, tangC_nonneg, tangBound⟩ :=
      chartTangentPart_norm_le (parameters := parameters) grade
    have sqrtK_nonneg : (0 : ℝ) ≤ Real.sqrt 2 ^ grade * axisConstant :=
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) grade) axisConstant_pos.le
    refine ⟨towC + (tangC * (Real.sqrt 2 ^ grade * axisConstant) + 2), by positivity, ?_⟩
    intro base directions axis
    have erase_empty : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
    have prod_eq : (∏ position, chartStateNorm 4 (directions position)) =
        chartStateNorm 4 (directions 0) := Fin.prod_univ_one _
    have sum_eq : (∑ position, chartStateNorm grade (directions position) *
        ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (directions other)) =
        chartStateNorm grade (directions 0) := by
      rw [Fin.sum_univ_one, erase_empty, Finset.prod_empty, mul_one]
    rw [prod_eq, sum_eq]
    have tower_le := towBound base directions axis
    rw [prod_eq, sum_eq] at tower_le
    have N_nonneg := chartStateNorm_nonneg grade base
    have d4_nonneg := chartStateNorm_nonneg 4 (directions 0)
    have dg_nonneg := chartStateNorm_nonneg grade (directions 0)
    have part1_nonneg : 0 ≤ (1 + chartStateNorm grade base) *
        chartStateNorm 4 (directions 0) := mul_nonneg (by linarith) d4_nonneg
    have d0_le_bracket : chartStateNorm grade (directions 0) ≤
        (1 + chartStateNorm grade base) * chartStateNorm 4 (directions 0) +
          chartStateNorm grade (directions 0) := le_add_of_nonneg_left part1_nonneg
    have tangent_raw := tangBound (directions 0).1
    have planar_le := planarEnvelope_le_state grade (directions 0)
    have tangent_le := tangent_raw.trans
      (mul_le_mul_of_nonneg_left planar_le tangC_nonneg)
    have v_le := field_le_chartStateNorm grade (directions 0)
    have s_le := scalar_le_chartStateNorm grade (directions 0)
    have split1 := (originalGradeNorm_add_le grade
        (tameScalarMultiplier 3
            (chartTower 1 base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside) +
          chartTangentPart parameters (directions 0).1) (directions 0).2.1).trans
      (add_le_add (originalGradeNorm_add_le grade _ _) le_rfl)
    have scaled_le := mul_le_mul_of_nonneg_left d0_le_bracket
      (mul_nonneg tangC_nonneg sqrtK_nonneg)
    have combined : originalGradeNorm grade
        (tameScalarMultiplier 3
            (chartTower 1 base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside) +
          chartTangentPart parameters (directions 0).1 + (directions 0).2.1) +
        originalGradeNorm grade (directions 0).2.2 ≤
        (towC + (tangC * (Real.sqrt 2 ^ grade * axisConstant) + 2)) *
          ((1 + chartStateNorm grade base) * chartStateNorm 4 (directions 0) +
            chartStateNorm grade (directions 0)) := by
      nlinarith [split1, tower_le, tangent_le, v_le, s_le, scaled_le, d0_le_bracket]
    exact combined
  | (order + 2) => by
    obtain ⟨towC, towC_nonneg, towBound⟩ :=
      towerMultiplier_norm_bound parameters seed inside grade (order + 2)
    refine ⟨towC, towC_nonneg, ?_⟩
    intro base directions axis
    have tower_le := towBound base directions axis
    have zero_norm : originalGradeNorm grade (0 : ACore parameters 1) = 0 :=
      originalGradeNorm_zero grade
    have combined : originalGradeNorm grade
        (tameScalarMultiplier 3
            (chartTower (order + 2) base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside)) +
        originalGradeNorm grade (0 : ACore parameters 1) ≤
        towC * ((1 + chartStateNorm grade base) *
            ∏ position, chartStateNorm 4 (directions position) +
          ∑ position, chartStateNorm grade (directions position) *
            ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (directions other)) := by
      rw [zero_norm, add_zero]
      exact tower_le
    exact combined

end Grad.NonlinearQuotientBounds
