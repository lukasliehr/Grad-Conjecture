import TameChartTowerBound

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The master one-high estimate of the chart tower: the structural
induction over pairs and singles with the simultaneous zero-grade
invariant, permutation transport to range form, and the tower bound. -/

variable {parameters : PhaseParameters}

/-- The one-high value of an index list against a direction assignment. -/
noncomputable def oneHighIndex (grade : ℕ) (directions : ℕ → TangentCoefficient parameters) :
    List ℕ → ℝ
  | [] => 0
  | index :: rest =>
      tangentPlanarEnvelope grade (directions index) *
        (rest.map (fun other => tangentPlanarEnvelope 0 (directions other))).prod +
      tangentPlanarEnvelope 0 (directions index) * oneHighIndex grade directions rest

/-- The low product of an index list. -/
def lowIndexProd (directions : ℕ → TangentCoefficient parameters)
    (indices : List ℕ) : ℝ :=
  (indices.map (fun index => tangentPlanarEnvelope 0 (directions index))).prod

theorem lowIndexProd_nonneg (directions : ℕ → TangentCoefficient parameters)
    (indices : List ℕ) : 0 ≤ lowIndexProd directions indices := by
  apply List.prod_nonneg
  intro value membership
  obtain ⟨index, _, index_eq⟩ := List.mem_map.mp membership
  exact index_eq ▸ tangentPlanarEnvelope_nonneg 0 (directions index)

theorem lowIndexProd_cons (directions : ℕ → TangentCoefficient parameters)
    (index : ℕ) (rest : List ℕ) :
    lowIndexProd directions (index :: rest) =
      tangentPlanarEnvelope 0 (directions index) * lowIndexProd directions rest := by
  rw [lowIndexProd, lowIndexProd, List.map_cons, List.prod_cons]

theorem oneHighIndex_nonneg (grade : ℕ) (directions : ℕ → TangentCoefficient parameters) :
    ∀ indices : List ℕ, 0 ≤ oneHighIndex grade directions indices := by
  intro indices
  induction indices with
  | nil =>
    rw [oneHighIndex]
  | cons head rest inductive_step =>
    rw [oneHighIndex]
    have prod_nonneg := lowIndexProd_nonneg directions rest
    rw [lowIndexProd] at prod_nonneg
    exact add_nonneg
      (mul_nonneg (tangentPlanarEnvelope_nonneg _ _) prod_nonneg)
      (mul_nonneg (tangentPlanarEnvelope_nonneg _ _) inductive_step)

/-- Permutation invariance of the one-high value. -/
theorem oneHighIndex_perm (grade : ℕ) (directions : ℕ → TangentCoefficient parameters)
    {first second : List ℕ} (perm : first.Perm second) :
    oneHighIndex grade directions first = oneHighIndex grade directions second := by
  induction perm with
  | nil => rfl
  | cons head tail_perm inner =>
    rw [oneHighIndex, oneHighIndex, inner,
      (tail_perm.map (fun other => tangentPlanarEnvelope 0 (directions other))).prod_eq]
  | swap first_index second_index rest =>
    rw [oneHighIndex, oneHighIndex, oneHighIndex, oneHighIndex,
      List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    ring
  | trans _ _ left right =>
    rw [left, right]

theorem lowIndexProd_perm (directions : ℕ → TangentCoefficient parameters)
    {first second : List ℕ} (perm : first.Perm second) :
    lowIndexProd directions first = lowIndexProd directions second := by
  rw [lowIndexProd, lowIndexProd]
  exact (perm.map _).prod_eq

/-- The flattened pair low product. -/
theorem lowIndexProd_pairsFlat (directions : ℕ → TangentCoefficient parameters) :
    ∀ pairs : List (ℕ × ℕ),
    lowIndexProd directions (pairs.flatMap (fun pair => [pair.1, pair.2])) =
      (pairs.map (fun pair => tangentPlanarEnvelope 0 (directions pair.1) *
        tangentPlanarEnvelope 0 (directions pair.2))).prod := by
  intro pairs
  induction pairs with
  | nil =>
    rw [List.flatMap_nil, lowIndexProd, List.map_nil, List.prod_nil, List.map_nil,
      List.prod_nil]
  | cons head rest inductive_step =>
    rw [List.flatMap_cons, List.map_cons, List.prod_cons, ← inductive_step]
    show lowIndexProd directions
      (head.1 :: head.2 :: rest.flatMap (fun pair => [pair.1, pair.2])) = _
    rw [lowIndexProd_cons, lowIndexProd_cons]
    ring

/-- The append decomposition of the low product. -/
theorem lowIndexProd_append (directions : ℕ → TangentCoefficient parameters)
    (first second : List ℕ) :
    lowIndexProd directions (first ++ second) =
      lowIndexProd directions first * lowIndexProd directions second := by
  rw [lowIndexProd, lowIndexProd, lowIndexProd, List.map_append, List.prod_append]

/-- The ball ratio of the slope bound. -/
def chartBallRatio (ballBound : ℝ) : ℝ := (1 + ballBound ^ 2) / 2

theorem chartBallRatio_pos {ballBound : ℝ} (_ballNonneg : 0 ≤ ballBound) :
    0 < chartBallRatio ballBound := by
  rw [chartBallRatio]
  nlinarith [sq_nonneg ballBound]

theorem chartBallRatio_lt_one {ballBound : ℝ} (ballNonneg : 0 ≤ ballBound)
    (ballLt : ballBound < 1) : chartBallRatio ballBound < 1 := by
  rw [chartBallRatio]
  nlinarith [ballNonneg, ballLt]

theorem quadratic_ball_facts {ballBound : ℝ} (ballNonneg : 0 ≤ ballBound)
    (ballLt : ballBound < 1) (base : TangentCoefficient parameters)
    (ball : tangentPlanarEnvelope 0 base ≤ ballBound) :
    coefficientEnvelope 0 (tangentQuadratic base) < 1 ∧
      rootSmallRadius (tangentQuadratic base) ≤ chartBallRatio ballBound := by
  have planar_nonneg := tangentPlanarEnvelope_nonneg 0 base
  have square_le : coefficientEnvelope 0 (tangentQuadratic base) ≤ ballBound ^ 2 := by
    apply (tangentQuadratic_envelope_zero_le base).trans
    nlinarith
  constructor
  · nlinarith
  · rw [rootSmallRadius, chartBallRatio]
    nlinarith

theorem lowIndexProd_nil (directions : ℕ → TangentCoefficient parameters) :
    lowIndexProd directions [] = 1 := by
  rw [lowIndexProd, List.map_nil, List.prod_nil]

theorem oneHighIndex_nil (grade : ℕ) (directions : ℕ → TangentCoefficient parameters) :
    oneHighIndex grade directions [] = 0 := by
  rw [oneHighIndex]

theorem oneHighIndex_cons (grade : ℕ) (directions : ℕ → TangentCoefficient parameters)
    (index : ℕ) (rest : List ℕ) :
    oneHighIndex grade directions (index :: rest) =
      tangentPlanarEnvelope grade (directions index) * lowIndexProd directions rest +
        tangentPlanarEnvelope 0 (directions index) * oneHighIndex grade directions rest := by
  rw [oneHighIndex, lowIndexProd]

/-- The simultaneous graded and zero-grade structural estimate of one
formal chart term. -/
theorem eval_structure_envelope_le (grade : ℕ) {ballBound : ℝ}
    (ballNonneg : 0 ≤ ballBound) (ballLt : ballBound < 1) (gOrder : ℕ) :
    ∀ (pairs : List (ℕ × ℕ)) (singles : List ℕ),
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (base : TangentCoefficient parameters)
      (directions : ℕ → TangentCoefficient parameters),
      tangentPlanarEnvelope 0 base ≤ ballBound →
      (coefficientEnvelope grade (evalChartTerm base directions ⟨gOrder, pairs, singles⟩) ≤
        constant * ((1 + tangentPlanarEnvelope grade base) *
            lowIndexProd directions (singles ++ pairs.flatMap (fun pair => [pair.1, pair.2])) +
          oneHighIndex grade directions
            (singles ++ pairs.flatMap (fun pair => [pair.1, pair.2]))) ∧
      coefficientEnvelope 0 (evalChartTerm base directions ⟨gOrder, pairs, singles⟩) ≤
        constant *
          lowIndexProd directions (singles ++ pairs.flatMap (fun pair => [pair.1, pair.2]))) := by
  have ratio_pos := chartBallRatio_pos ballNonneg
  have ratio_lt := chartBallRatio_lt_one ballNonneg ballLt
  have slope_g_nonneg := rootSlopeBound_nonneg gOrder grade ratio_pos
  have slope_z_nonneg := rootSlopeBound_nonneg gOrder 0 ratio_pos
  have exp_nonneg := (Real.exp_pos parameters.sigma0).le
  have coefficient_nonneg := abs_nonneg (rootDerivativeCoefficient gOrder 0)
  intro pairs singles
  induction singles generalizing pairs with
  | nil =>
    induction pairs with
    | nil =>
      refine ⟨(|rootDerivativeCoefficient gOrder 0| * Real.exp parameters.sigma0 +
        rootSlopeBound gOrder grade (chartBallRatio ballBound) *
          ((2 : ℝ) ^ (grade + 1) * ballBound)) +
        (|rootDerivativeCoefficient gOrder 0| * Real.exp parameters.sigma0 +
          rootSlopeBound gOrder 0 (chartBallRatio ballBound) * ballBound ^ 2), ?_, ?_⟩
      · positivity
      · intro base directions ball
        obtain ⟨quad_small, radius_le⟩ := quadratic_ball_facts ballNonneg ballLt base ball
        have planar_nonneg := tangentPlanarEnvelope_nonneg 0 base
        have graded_nonneg := tangentPlanarEnvelope_nonneg grade base
        have eval_eq : evalChartTerm base directions
            (⟨gOrder, [], []⟩ : ChartTermData) =
            tameRootShifted gOrder (tangentQuadratic base) := by
          simp [evalChartTerm]
        have quad_graded : coefficientEnvelope grade (tangentQuadratic base) ≤
            (2 : ℝ) ^ (grade + 1) * ballBound * tangentPlanarEnvelope grade base := by
          apply (tangentQuadratic_envelope_le grade base).trans
          have pow_nonneg' := pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) (grade + 1)
          have step := mul_le_mul_of_nonneg_left ball
            (mul_nonneg pow_nonneg' graded_nonneg)
          nlinarith [step]
        have quad_zero : coefficientEnvelope 0 (tangentQuadratic base) ≤ ballBound ^ 2 := by
          apply (tangentQuadratic_envelope_zero_le base).trans
          have step := mul_le_mul ball ball planar_nonneg ballNonneg
          nlinarith [step]
        have slope_g_le := tameRootShifted_envelope_le_slope gOrder grade quad_small
          ratio_lt radius_le
        have slope_z_le := tameRootShifted_envelope_le_slope gOrder 0 quad_small
          ratio_lt radius_le
        simp only [List.flatMap_nil, List.nil_append, lowIndexProd_nil, oneHighIndex_nil]
        rw [eval_eq]
        constructor
        · have graded_chain : coefficientEnvelope grade
              (tameRootShifted gOrder (tangentQuadratic base)) ≤
              |rootDerivativeCoefficient gOrder 0| * Real.exp parameters.sigma0 +
                rootSlopeBound gOrder grade (chartBallRatio ballBound) *
                  ((2 : ℝ) ^ (grade + 1) * ballBound) *
                  tangentPlanarEnvelope grade base := by
            apply slope_g_le.trans
            apply add_le_add le_rfl
            calc rootSlopeBound gOrder grade (chartBallRatio ballBound) *
                  coefficientEnvelope grade (tangentQuadratic base)
                ≤ rootSlopeBound gOrder grade (chartBallRatio ballBound) *
                    ((2 : ℝ) ^ (grade + 1) * ballBound *
                      tangentPlanarEnvelope grade base) :=
                  mul_le_mul_of_nonneg_left quad_graded slope_g_nonneg
              _ = _ := by ring
          apply graded_chain.trans
          have expand : ((|rootDerivativeCoefficient gOrder 0| * Real.exp parameters.sigma0 +
              rootSlopeBound gOrder grade (chartBallRatio ballBound) *
                ((2 : ℝ) ^ (grade + 1) * ballBound)) +
              (|rootDerivativeCoefficient gOrder 0| * Real.exp parameters.sigma0 +
                rootSlopeBound gOrder 0 (chartBallRatio ballBound) * ballBound ^ 2)) *
              ((1 + tangentPlanarEnvelope grade base) * 1 + 0) =
              ((|rootDerivativeCoefficient gOrder 0| * Real.exp parameters.sigma0 +
                rootSlopeBound gOrder grade (chartBallRatio ballBound) *
                  ((2 : ℝ) ^ (grade + 1) * ballBound)) +
                (|rootDerivativeCoefficient gOrder 0| * Real.exp parameters.sigma0 +
                  rootSlopeBound gOrder 0 (chartBallRatio ballBound) * ballBound ^ 2)) *
              (1 + tangentPlanarEnvelope grade base) := by ring
          rw [expand]
          have two_pow_nonneg : (0:ℝ) ≤ (2 : ℝ) ^ (grade + 1) * ballBound := by positivity
          have slope_term_nonneg : (0:ℝ) ≤ rootSlopeBound gOrder grade
              (chartBallRatio ballBound) * ((2 : ℝ) ^ (grade + 1) * ballBound) :=
            mul_nonneg slope_g_nonneg two_pow_nonneg
          have zero_term_nonneg : (0:ℝ) ≤ rootSlopeBound gOrder 0
              (chartBallRatio ballBound) * ballBound ^ 2 :=
            mul_nonneg slope_z_nonneg (sq_nonneg ballBound)
          have head_nonneg : (0:ℝ) ≤ |rootDerivativeCoefficient gOrder 0| *
              Real.exp parameters.sigma0 := mul_nonneg coefficient_nonneg exp_nonneg
          nlinarith [mul_nonneg slope_term_nonneg graded_nonneg,
            mul_nonneg zero_term_nonneg graded_nonneg,
            mul_nonneg head_nonneg graded_nonneg]
        · rw [mul_one]
          apply slope_z_le.trans
          have zero_chain : rootSlopeBound gOrder 0 (chartBallRatio ballBound) *
              coefficientEnvelope 0 (tangentQuadratic base) ≤
              rootSlopeBound gOrder 0 (chartBallRatio ballBound) * ballBound ^ 2 :=
            mul_le_mul_of_nonneg_left quad_zero slope_z_nonneg
          have first_nonneg : (0:ℝ) ≤ |rootDerivativeCoefficient gOrder 0| *
              Real.exp parameters.sigma0 +
              rootSlopeBound gOrder grade (chartBallRatio ballBound) *
                ((2 : ℝ) ^ (grade + 1) * ballBound) := by positivity
          linarith
    | cons pairHead pairTail pair_step =>
      obtain ⟨tailConstant, tailNonneg, tailBound⟩ := pair_step
      refine ⟨(2 : ℝ) ^ grade * tailConstant * ((2 : ℝ) ^ (grade + 1) + 2), ?_, ?_⟩
      · positivity
      · intro base directions ball
        obtain ⟨tail_graded, tail_zero⟩ := tailBound base directions ball
        have graded_nonneg := tangentPlanarEnvelope_nonneg grade base
        set firstHigh := tangentPlanarEnvelope grade (directions pairHead.1)
        set firstLow := tangentPlanarEnvelope 0 (directions pairHead.1)
        set secondHigh := tangentPlanarEnvelope grade (directions pairHead.2)
        set secondLow := tangentPlanarEnvelope 0 (directions pairHead.2)
        set tailProd := lowIndexProd directions
          ([] ++ pairTail.flatMap (fun pair => [pair.1, pair.2]))
        set tailHigh := oneHighIndex grade directions
          ([] ++ pairTail.flatMap (fun pair => [pair.1, pair.2]))
        have firstHigh_nonneg : 0 ≤ firstHigh := tangentPlanarEnvelope_nonneg _ _
        have firstLow_nonneg : 0 ≤ firstLow := tangentPlanarEnvelope_nonneg _ _
        have secondHigh_nonneg : 0 ≤ secondHigh := tangentPlanarEnvelope_nonneg _ _
        have secondLow_nonneg : 0 ≤ secondLow := tangentPlanarEnvelope_nonneg _ _
        have tailProd_nonneg : 0 ≤ tailProd := lowIndexProd_nonneg _ _
        have tailHigh_nonneg : 0 ≤ tailHigh := oneHighIndex_nonneg _ _ _
        have regroup : evalChartTerm base directions
            (⟨gOrder, pairHead :: pairTail, []⟩ : ChartTermData) =
            tangentDot (directions pairHead.1) (directions pairHead.2) *
              evalChartTerm base directions (⟨gOrder, pairTail, []⟩ : ChartTermData) := by
          simp only [evalChartTerm, List.map_cons, List.prod_cons]
          ring
        have factor_graded := tangentDot_envelope_le grade
          (directions pairHead.1) (directions pairHead.2)
        have factor_zero := tangentDot_envelope_zero_le
          (directions pairHead.1) (directions pairHead.2)
        have list_shape : ([] : List ℕ) ++
            ((pairHead :: pairTail).flatMap (fun pair => [pair.1, pair.2])) =
            pairHead.1 :: pairHead.2 ::
              ([] ++ pairTail.flatMap (fun pair => [pair.1, pair.2])) := rfl
        rw [regroup, list_shape, lowIndexProd_cons, lowIndexProd_cons, oneHighIndex_cons,
          oneHighIndex_cons, lowIndexProd_cons]
        constructor
        · have split := tameMul_envelope_le grade
            (tangentDot (directions pairHead.1) (directions pairHead.2))
            (evalChartTerm base directions (⟨gOrder, pairTail, []⟩ : ChartTermData))
          apply split.trans
          have piece_one : coefficientEnvelope grade
              (tangentDot (directions pairHead.1) (directions pairHead.2)) *
              coefficientEnvelope 0
                (evalChartTerm base directions (⟨gOrder, pairTail, []⟩ : ChartTermData)) ≤
              ((2 : ℝ) ^ (grade + 1) * (firstHigh * secondLow + firstLow * secondHigh)) *
                (tailConstant * tailProd) := by
            apply mul_le_mul factor_graded tail_zero (coefficientEnvelope_nonneg 0 _)
            positivity
          have piece_two : coefficientEnvelope 0
              (tangentDot (directions pairHead.1) (directions pairHead.2)) *
              coefficientEnvelope grade
                (evalChartTerm base directions (⟨gOrder, pairTail, []⟩ : ChartTermData)) ≤
              (2 * (firstLow * secondLow)) *
                (tailConstant * ((1 + tangentPlanarEnvelope grade base) * tailProd +
                  tailHigh)) := by
            apply mul_le_mul factor_zero tail_graded (coefficientEnvelope_nonneg grade _)
            positivity
          have combined := add_le_add piece_one piece_two
          have final : (2 : ℝ) ^ grade *
              (((2 : ℝ) ^ (grade + 1) * (firstHigh * secondLow + firstLow * secondHigh)) *
                (tailConstant * tailProd) +
                (2 * (firstLow * secondLow)) *
                  (tailConstant * ((1 + tangentPlanarEnvelope grade base) * tailProd +
                    tailHigh))) ≤
              (2 : ℝ) ^ grade * tailConstant * ((2 : ℝ) ^ (grade + 1) + 2) *
                ((1 + tangentPlanarEnvelope grade base) *
                    (firstLow * (secondLow * tailProd)) +
                  (firstHigh * (secondLow * tailProd) +
                    firstLow * (secondHigh * tailProd + secondLow * tailHigh))) := by
            have base_bucket : (0:ℝ) ≤ (1 + tangentPlanarEnvelope grade base) := by linarith
            have pow_g_nonneg : (0:ℝ) ≤ (2 : ℝ) ^ grade :=
              pow_nonneg (by norm_num) grade
            have pow_s_nonneg : (0:ℝ) ≤ (2 : ℝ) ^ (grade + 1) :=
              pow_nonneg (by norm_num) (grade + 1)
            have scale_nonneg : (0:ℝ) ≤ (2 : ℝ) ^ grade * tailConstant :=
              mul_nonneg pow_g_nonneg tailNonneg
            have coeff_high : (2 : ℝ) ^ grade * tailConstant * (2 : ℝ) ^ (grade + 1) ≤
                (2 : ℝ) ^ grade * tailConstant * ((2 : ℝ) ^ (grade + 1) + 2) := by
              nlinarith
            have coeff_low : (2 : ℝ) ^ grade * tailConstant * 2 ≤
                (2 : ℝ) ^ grade * tailConstant * ((2 : ℝ) ^ (grade + 1) + 2) := by
              nlinarith
            have atom_one : (0:ℝ) ≤ firstHigh * (secondLow * tailProd) := by positivity
            have atom_two : (0:ℝ) ≤ firstLow * (secondHigh * tailProd) := by positivity
            have atom_three : (0:ℝ) ≤ (1 + tangentPlanarEnvelope grade base) *
                (firstLow * (secondLow * tailProd)) := by positivity
            have atom_four : (0:ℝ) ≤ firstLow * (secondLow * tailHigh) := by positivity
            nlinarith [mul_le_mul_of_nonneg_right coeff_high atom_one,
              mul_le_mul_of_nonneg_right coeff_high atom_two,
              mul_le_mul_of_nonneg_right coeff_low atom_three,
              mul_le_mul_of_nonneg_right coeff_low atom_four]
          calc (2 : ℝ) ^ grade * (coefficientEnvelope grade
                (tangentDot (directions pairHead.1) (directions pairHead.2)) *
                coefficientEnvelope 0 (evalChartTerm base directions
                  (⟨gOrder, pairTail, []⟩ : ChartTermData)) +
                coefficientEnvelope 0
                  (tangentDot (directions pairHead.1) (directions pairHead.2)) *
                coefficientEnvelope grade (evalChartTerm base directions
                  (⟨gOrder, pairTail, []⟩ : ChartTermData)))
              ≤ (2 : ℝ) ^ grade *
                (((2 : ℝ) ^ (grade + 1) * (firstHigh * secondLow + firstLow * secondHigh)) *
                  (tailConstant * tailProd) +
                  (2 * (firstLow * secondLow)) *
                    (tailConstant * ((1 + tangentPlanarEnvelope grade base) * tailProd +
                      tailHigh))) :=
                mul_le_mul_of_nonneg_left combined (pow_nonneg (by norm_num) grade)
            _ ≤ _ := final
        · have split := tameMul_envelope_zero_le
            (tangentDot (directions pairHead.1) (directions pairHead.2))
            (evalChartTerm base directions (⟨gOrder, pairTail, []⟩ : ChartTermData))
          apply split.trans
          have chain : coefficientEnvelope 0
              (tangentDot (directions pairHead.1) (directions pairHead.2)) *
              coefficientEnvelope 0
                (evalChartTerm base directions (⟨gOrder, pairTail, []⟩ : ChartTermData)) ≤
              (2 * (firstLow * secondLow)) * (tailConstant * tailProd) := by
            apply mul_le_mul factor_zero tail_zero (coefficientEnvelope_nonneg 0 _)
            positivity
          apply chain.trans
          have two_le : (2:ℝ) ≤ (2 : ℝ) ^ grade * ((2 : ℝ) ^ (grade + 1) + 2) := by
            have one_le : (1:ℝ) ≤ (2 : ℝ) ^ grade := one_le_pow₀ (by norm_num)
            have pow_nonneg' : (0:ℝ) ≤ (2 : ℝ) ^ (grade + 1) :=
              pow_nonneg (by norm_num) _
            nlinarith
          nlinarith [mul_nonneg (mul_nonneg firstLow_nonneg secondLow_nonneg) tailProd_nonneg,
            tailNonneg, mul_nonneg tailNonneg
              (mul_nonneg (mul_nonneg firstLow_nonneg secondLow_nonneg) tailProd_nonneg)]
  | cons singleHead singleTail single_step =>
    obtain ⟨tailConstant, tailNonneg, tailBound⟩ := single_step pairs
    refine ⟨(2 : ℝ) ^ grade * tailConstant * ((2 : ℝ) ^ (grade + 1) + 2) * 2, ?_, ?_⟩
    · positivity
    · intro base directions ball
      obtain ⟨tail_graded, tail_zero⟩ := tailBound base directions ball
      have graded_nonneg := tangentPlanarEnvelope_nonneg grade base
      have base_zero_nonneg := tangentPlanarEnvelope_nonneg 0 base
      set headHigh := tangentPlanarEnvelope grade (directions singleHead)
      set headLow := tangentPlanarEnvelope 0 (directions singleHead)
      set tailProd := lowIndexProd directions
        (singleTail ++ pairs.flatMap (fun pair => [pair.1, pair.2]))
      set tailHigh := oneHighIndex grade directions
        (singleTail ++ pairs.flatMap (fun pair => [pair.1, pair.2]))
      have headHigh_nonneg : 0 ≤ headHigh := tangentPlanarEnvelope_nonneg _ _
      have headLow_nonneg : 0 ≤ headLow := tangentPlanarEnvelope_nonneg _ _
      have tailProd_nonneg : 0 ≤ tailProd := lowIndexProd_nonneg _ _
      have tailHigh_nonneg : 0 ≤ tailHigh := oneHighIndex_nonneg _ _ _
      have regroup : evalChartTerm base directions
          (⟨gOrder, pairs, singleHead :: singleTail⟩ : ChartTermData) =
          tangentDot base (directions singleHead) *
            evalChartTerm base directions (⟨gOrder, pairs, singleTail⟩ : ChartTermData) := by
        simp only [evalChartTerm, List.map_cons, List.prod_cons]
        ring
      have factor_graded : coefficientEnvelope grade
          (tangentDot base (directions singleHead)) ≤
          (2 : ℝ) ^ (grade + 1) * (tangentPlanarEnvelope grade base * headLow +
            ballBound * headHigh) := by
        apply (tangentDot_envelope_le grade base (directions singleHead)).trans
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_right ball headHigh_nonneg
      have factor_zero : coefficientEnvelope 0
          (tangentDot base (directions singleHead)) ≤ 2 * (ballBound * headLow) := by
        apply (tangentDot_envelope_zero_le base (directions singleHead)).trans
        have := mul_le_mul_of_nonneg_right ball headLow_nonneg
        nlinarith
      have list_shape : ((singleHead :: singleTail) : List ℕ) ++
          (pairs.flatMap (fun pair => [pair.1, pair.2])) =
          singleHead :: (singleTail ++ pairs.flatMap (fun pair => [pair.1, pair.2])) := rfl
      rw [regroup, list_shape, lowIndexProd_cons, oneHighIndex_cons]
      have ball_le_one : ballBound ≤ 1 := ballLt.le
      constructor
      · have split := tameMul_envelope_le grade
          (tangentDot base (directions singleHead))
          (evalChartTerm base directions (⟨gOrder, pairs, singleTail⟩ : ChartTermData))
        apply split.trans
        have piece_one : coefficientEnvelope grade
            (tangentDot base (directions singleHead)) *
            coefficientEnvelope 0
              (evalChartTerm base directions (⟨gOrder, pairs, singleTail⟩ : ChartTermData)) ≤
            ((2 : ℝ) ^ (grade + 1) * (tangentPlanarEnvelope grade base * headLow +
              ballBound * headHigh)) * (tailConstant * tailProd) := by
          apply mul_le_mul factor_graded tail_zero (coefficientEnvelope_nonneg 0 _)
          positivity
        have piece_two : coefficientEnvelope 0
            (tangentDot base (directions singleHead)) *
            coefficientEnvelope grade
              (evalChartTerm base directions (⟨gOrder, pairs, singleTail⟩ : ChartTermData)) ≤
            (2 * (ballBound * headLow)) *
              (tailConstant * ((1 + tangentPlanarEnvelope grade base) * tailProd +
                tailHigh)) := by
          apply mul_le_mul factor_zero tail_graded (coefficientEnvelope_nonneg grade _)
          positivity
        have combined := add_le_add piece_one piece_two
        have final : (2 : ℝ) ^ grade *
            (((2 : ℝ) ^ (grade + 1) * (tangentPlanarEnvelope grade base * headLow +
              ballBound * headHigh)) * (tailConstant * tailProd) +
              (2 * (ballBound * headLow)) *
                (tailConstant * ((1 + tangentPlanarEnvelope grade base) * tailProd +
                  tailHigh))) ≤
            (2 : ℝ) ^ grade * tailConstant * ((2 : ℝ) ^ (grade + 1) + 2) * 2 *
              ((1 + tangentPlanarEnvelope grade base) * (headLow * tailProd) +
                (headHigh * tailProd + headLow * tailHigh)) := by
          have base_bucket : (0:ℝ) ≤ 1 + tangentPlanarEnvelope grade base := by linarith
          have pow_g_nonneg : (0:ℝ) ≤ (2 : ℝ) ^ grade := pow_nonneg (by norm_num) grade
          have pow_s_nonneg : (0:ℝ) ≤ (2 : ℝ) ^ (grade + 1) :=
            pow_nonneg (by norm_num) (grade + 1)
          have coeff_bg : (2 : ℝ) ^ grade * tailConstant * (2 : ℝ) ^ (grade + 1) ≤
              (2 : ℝ) ^ grade * tailConstant * ((2 : ℝ) ^ (grade + 1) + 2) * 2 := by
            nlinarith [mul_nonneg pow_g_nonneg tailNonneg]
          have coeff_bb : (2 : ℝ) ^ grade * tailConstant * ((2 : ℝ) ^ (grade + 1) * ballBound) ≤
              (2 : ℝ) ^ grade * tailConstant * ((2 : ℝ) ^ (grade + 1) + 2) * 2 := by
            have ball_le_one' : ballBound ≤ 1 := ballLt.le
            nlinarith [mul_nonneg pow_g_nonneg tailNonneg,
              mul_nonneg (mul_nonneg pow_g_nonneg tailNonneg) pow_s_nonneg]
          have coeff_low2 : (2 : ℝ) ^ grade * tailConstant * (2 * ballBound) ≤
              (2 : ℝ) ^ grade * tailConstant * ((2 : ℝ) ^ (grade + 1) + 2) * 2 := by
            have ball_le_one' : ballBound ≤ 1 := ballLt.le
            nlinarith [mul_nonneg pow_g_nonneg tailNonneg]
          have atom_bg : (0:ℝ) ≤ tangentPlanarEnvelope grade base *
              (headLow * tailProd) := by positivity
          have atom_hh : (0:ℝ) ≤ headHigh * tailProd := by positivity
          have atom_first : (0:ℝ) ≤ (1 + tangentPlanarEnvelope grade base) *
              (headLow * tailProd) := by positivity
          have atom_oh : (0:ℝ) ≤ headLow * tailHigh := by positivity
          have bg_le_bucket : tangentPlanarEnvelope grade base * (headLow * tailProd) ≤
              (1 + tangentPlanarEnvelope grade base) * (headLow * tailProd) := by
            nlinarith [mul_nonneg headLow_nonneg tailProd_nonneg]
          nlinarith [mul_le_mul_of_nonneg_right coeff_bg atom_bg,
            mul_le_mul_of_nonneg_right coeff_bb atom_hh,
            mul_le_mul_of_nonneg_right coeff_low2 atom_first,
            mul_le_mul_of_nonneg_right coeff_low2 atom_oh,
            mul_le_mul_of_nonneg_left bg_le_bucket
              (le_trans (by positivity) (le_refl ((2 : ℝ) ^ grade * tailConstant *
                ((2 : ℝ) ^ (grade + 1) + 2) * 2))),
            mul_nonneg (mul_nonneg pow_g_nonneg tailNonneg) atom_bg]
        calc (2 : ℝ) ^ grade * (coefficientEnvelope grade
              (tangentDot base (directions singleHead)) *
              coefficientEnvelope 0 (evalChartTerm base directions
                (⟨gOrder, pairs, singleTail⟩ : ChartTermData)) +
              coefficientEnvelope 0 (tangentDot base (directions singleHead)) *
              coefficientEnvelope grade (evalChartTerm base directions
                (⟨gOrder, pairs, singleTail⟩ : ChartTermData)))
            ≤ (2 : ℝ) ^ grade *
              (((2 : ℝ) ^ (grade + 1) * (tangentPlanarEnvelope grade base * headLow +
                ballBound * headHigh)) * (tailConstant * tailProd) +
                (2 * (ballBound * headLow)) *
                  (tailConstant * ((1 + tangentPlanarEnvelope grade base) * tailProd +
                    tailHigh))) :=
              mul_le_mul_of_nonneg_left combined (pow_nonneg (by norm_num) grade)
          _ ≤ _ := final
      · have split := tameMul_envelope_zero_le
          (tangentDot base (directions singleHead))
          (evalChartTerm base directions (⟨gOrder, pairs, singleTail⟩ : ChartTermData))
        apply split.trans
        have chain : coefficientEnvelope 0 (tangentDot base (directions singleHead)) *
            coefficientEnvelope 0
              (evalChartTerm base directions (⟨gOrder, pairs, singleTail⟩ : ChartTermData)) ≤
            (2 * (ballBound * headLow)) * (tailConstant * tailProd) := by
          apply mul_le_mul factor_zero tail_zero (coefficientEnvelope_nonneg 0 _)
          positivity
        apply chain.trans
        have coefficient_grow : (2:ℝ) * ballBound ≤
            (2 : ℝ) ^ grade * ((2 : ℝ) ^ (grade + 1) + 2) * 2 := by
          have one_le : (1:ℝ) ≤ (2 : ℝ) ^ grade := one_le_pow₀ (by norm_num)
          have pow_nonneg' : (0:ℝ) ≤ (2 : ℝ) ^ (grade + 1) :=
            pow_nonneg (by norm_num) _
          nlinarith
        nlinarith [mul_nonneg headLow_nonneg tailProd_nonneg, tailNonneg,
          mul_nonneg tailNonneg (mul_nonneg headLow_nonneg tailProd_nonneg),
          mul_nonneg ballNonneg headLow_nonneg]

end Grad.NonlinearQuotientBounds
