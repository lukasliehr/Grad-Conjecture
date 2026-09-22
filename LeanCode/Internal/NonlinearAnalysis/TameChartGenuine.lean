import TameChartFamily

noncomputable section

set_option maxHeartbeats 1600000

open Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

/-! Genuineness of the chart derivative family: on the literal Q13 axis
ball, every level's directional difference quotient along the newest
direction converges to the next level in every combined output grade norm.
The affine parts contribute their exact linear coefficients with zero
quotient error; the multiplier part rides on the tower step through the
coefficient-envelope transport. -/

variable {parameters : PhaseParameters}

theorem axisConstant_pos : 0 < axisConstant := by
  rw [axisConstant]
  apply Real.sqrt_pos.mpr
  have pi_large := tame_three_lt_pi
  linarith

/-- The only index of `Fin 1`. -/
theorem tameFinOne_eq (index : Fin 1) : index = 0 :=
  Fin.eq_of_val_eq (Nat.lt_one_iff.mp index.isLt)

/-- The literal Q13 condition places the planar envelope below one half. -/
theorem chartAxis_planar_lt_half {base : ChartState parameters}
    (axis : ChartAxisCondition base) : tangentPlanarEnvelope 0 base.1 < 1 / 2 := by
  have bridge := tangentPlanarEnvelope_le 0 base.1
  rw [pow_zero, one_mul] at bridge
  have bridge_one : tangentPlanarEnvelope 0 base.1 ≤
      axisConstant * tangentNorm 1 base.1 := bridge
  have constant_pos := axisConstant_pos
  have norm_lt : axisConstant * tangentNorm 1 base.1 <
      axisConstant * (2 * axisConstant)⁻¹ :=
    mul_lt_mul_of_pos_left axis constant_pos
  have collapse : axisConstant * (2 * axisConstant)⁻¹ = 1 / 2 := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt constant_pos), one_mul, one_div]
  linarith

/-- The literal Q13 condition forces the strict planar unit ball. -/
theorem chartAxis_planar_small {base : ChartState parameters}
    (axis : ChartAxisCondition base) : tangentPlanarEnvelope 0 base.1 < 1 :=
  lt_trans (chartAxis_planar_lt_half axis) (by norm_num)

/-- The affine tangential part of the chart. -/
def chartTangentPart (parameters : PhaseParameters)
    (family : TangentCoefficient parameters) : ACore parameters 3 :=
  valueMapCore parameters tameTangentInclusion
    (tameScalarMultiplier 1 (tangentComponent family 0)
        (tameCoordinateScalarField parameters 0) +
      tameScalarMultiplier 1 (tangentComponent family 1)
        (tameCoordinateScalarField parameters 1))

theorem chartTangentPart_add (first second : TangentCoefficient parameters) :
    chartTangentPart parameters (first + second) =
      chartTangentPart parameters first + chartTangentPart parameters second := by
  rw [chartTangentPart, chartTangentPart, chartTangentPart,
    tangentComponent_add, tangentComponent_add,
    tameScalarMultiplier_add, tameScalarMultiplier_add, ← map_add]
  congr 1
  abel

theorem chartTangentPart_smul (scalar : ℂ) (family : TangentCoefficient parameters) :
    chartTangentPart parameters (scalar • family) =
      scalar • chartTangentPart parameters family := by
  rw [chartTangentPart, chartTangentPart, tangentComponent_smul, tangentComponent_smul,
    tameScalarMultiplier_smul, tameScalarMultiplier_smul, ← smul_add, map_smul]

/-! ### Exact collapse of the affine quotient parts -/

/-- The full order-one quotient collapse: multiplier difference stays, the
affine direction parts cancel exactly. -/
theorem chartQuotient_collapse_main {Space : Type} [AddCommGroup Space]
    [Module ℂ Space] {t : ℂ} (nonzero : t ≠ 0)
    (movedRoot baseRoot towerPart basePart directionPart
      baseField directionField : Space) :
    (t⁻¹ • ((movedRoot + (basePart + t • directionPart) +
        (baseField + t • directionField)) - (baseRoot + basePart + baseField))) -
      (towerPart + directionPart + directionField) =
      (t⁻¹ • (movedRoot - baseRoot)) - towerPart := by
  have cancel : (movedRoot + (basePart + t • directionPart) +
      (baseField + t • directionField)) - (baseRoot + basePart + baseField) =
      (movedRoot - baseRoot) + (t • directionPart + t • directionField) := by
    abel
  rw [cancel, smul_add, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ nonzero,
    one_smul, one_smul]
  abel

/-- The scalar-slot quotient collapse: an affine curve differentiates to its
slope with zero error. -/
theorem chartQuotient_collapse_affine {Space : Type} [AddCommGroup Space]
    [Module ℂ Space] {t : ℂ} (nonzero : t ≠ 0)
    (seedPart baseScalar directionScalar : Space) :
    (t⁻¹ • ((seedPart + (baseScalar + t • directionScalar)) -
        (seedPart + baseScalar))) - directionScalar = 0 := by
  have cancel : (seedPart + (baseScalar + t • directionScalar)) -
      (seedPart + baseScalar) = t • directionScalar := by
    abel
  rw [cancel, smul_smul, inv_mul_cancel₀ nonzero, one_smul, sub_self]

/-- State-constant summands drop out of the quotient. -/
theorem chartQuotient_collapse_shift {Space : Type} [AddCommGroup Space]
    [Module ℂ Space] (t : ℂ)
    (movedRoot baseRoot towerPart tangentConstant fieldConstant : Space) :
    (t⁻¹ • ((movedRoot + tangentConstant + fieldConstant) -
        (baseRoot + tangentConstant + fieldConstant))) - towerPart =
      (t⁻¹ • (movedRoot - baseRoot)) - towerPart := by
  have cancel : (movedRoot + tangentConstant + fieldConstant) -
      (baseRoot + tangentConstant + fieldConstant) = movedRoot - baseRoot := by
    abel
  rw [cancel]

/-- A constant curve has zero quotient against the zero derivative. -/
theorem chartQuotient_collapse_constant {Space : Type} [AddCommGroup Space]
    [Module ℂ Space] (t : ℂ) (value : Space) :
    (t⁻¹ • (value - value)) - 0 = 0 := by
  rw [sub_self, smul_zero, sub_zero]

/-! ### The tower step through the multiplier -/

/-- The multiplier error of one tower step vanishes in every grade norm. -/
theorem tower_multiplier_tendsto (parameters : PhaseParameters)
    (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain)
    (level : ℕ) (base : ChartState parameters)
    (extended : ℕ → TangentCoefficient parameters)
    (direction : TangentCoefficient parameters)
    (slot : extended level = direction)
    (small : tangentPlanarEnvelope 0 base.1 < 1) (grade : ℕ) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      ((((t : ℂ))⁻¹ • (tameScalarMultiplier 3
            (chartTower level (base.1 + (t : ℂ) • direction) extended)
            (tameSeedField parameters seed inside) -
          tameScalarMultiplier 3 (chartTower level base.1 extended)
            (tameSeedField parameters seed inside))) -
        tameScalarMultiplier 3 (chartTower (level + 1) base.1 extended)
          (tameSeedField parameters seed inside)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have tower_deriv := chartTower_hasEnvDerivAt level base.1 extended small
  rw [slot] at tower_deriv
  have quotient : Tendsto (fun t : ℝ => originalGradeNorm grade
      ((((t : ℂ))⁻¹ • (tameScalarMultiplier 3
            (chartTower level (base.1 + (t : ℂ) • direction) extended)
            (tameSeedField parameters seed inside) -
          tameScalarMultiplier 3
            (chartTower level (base.1 + ((0 : ℝ) : ℂ) • direction) extended)
            (tameSeedField parameters seed inside))) -
        tameScalarMultiplier 3 (chartTower (level + 1) base.1 extended)
          (tameSeedField parameters seed inside)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_multiplier_quotient 3 (tameSeedField parameters seed inside) tower_deriv grade
  have curve_zero : chartTower level (base.1 + ((0 : ℝ) : ℂ) • direction) extended =
      chartTower level base.1 extended := by
    rw [Complex.ofReal_zero, zero_smul, add_zero]
  rw [curve_zero] at quotient
  exact quotient

/-! ### The genuineness of the family -/

/-- Q20 genuineness: on the literal Q13 ball, level `order` of the family
differentiates along the newest direction to level `order + 1`, in every
combined output grade norm. -/
theorem chartDerivativeFamily_genuine (parameters : PhaseParameters)
    (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain) :
    ∀ (order : ℕ) (base : ChartState parameters)
      (directions : Fin (order + 1) → ChartState parameters),
      ChartAxisCondition base →
      IsChartDirectionalDerivative
        (fun state => chartDerivativeFamily parameters seed inside order state
          (fun position => directions position.castSucc))
        base (directions (Fin.last order))
        (chartDerivativeFamily parameters seed inside (order + 1) base directions)
  | 0, base, directions, axis => by
    have small := chartAxis_planar_small axis
    have last_eq : directions (Fin.last 0) = directions 0 :=
      congrArg directions (tameFinOne_eq (Fin.last 0))
    have slot : chartTangentDirections directions 0 = (directions 0).1 := by
      rw [chartTangentDirections_top directions, last_eq]
    rw [last_eq]
    intro grade
    have tower1 : Tendsto (fun t : ℝ => originalGradeNorm grade
        ((((t : ℂ))⁻¹ • (tameScalarMultiplier 3
              (chartTower 0 (base.1 + (t : ℂ) • (directions 0).1)
                (chartTangentDirections directions))
              (tameSeedField parameters seed inside) -
            tameScalarMultiplier 3
              (chartTower 0 base.1 (chartTangentDirections directions))
              (tameSeedField parameters seed inside))) -
          tameScalarMultiplier 3
            (chartTower 1 base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside)))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      tower_multiplier_tendsto parameters seed inside 0 base
        (chartTangentDirections directions) ((directions 0).1) slot small grade
    simp only [chartTower_zero] at tower1
    refine tower1.congr' ?_
    apply eventually_nhdsWithin_of_forall
    intro t membership
    have nonzero : (t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by simpa using membership)
    show originalGradeNorm grade
        ((((t : ℂ))⁻¹ • (tameScalarMultiplier 3
              (tameRootShifted 0 (tangentQuadratic (base.1 + (t : ℂ) • (directions 0).1)))
              (tameSeedField parameters seed inside) -
            tameScalarMultiplier 3 (tameRootShifted 0 (tangentQuadratic base.1))
              (tameSeedField parameters seed inside))) -
          tameScalarMultiplier 3
            (chartTower 1 base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside)) =
      originalGradeNorm grade
        ((((t : ℂ))⁻¹ • ((tameScalarMultiplier 3
              (tameRootShifted 0 (tangentQuadratic (base.1 + (t : ℂ) • (directions 0).1)))
              (tameSeedField parameters seed inside) +
            chartTangentPart parameters (base.1 + (t : ℂ) • (directions 0).1) +
            (base.2.1 + (t : ℂ) • (directions 0).2.1)) -
          (tameScalarMultiplier 3 (tameRootShifted 0 (tangentQuadratic base.1))
              (tameSeedField parameters seed inside) +
            chartTangentPart parameters base.1 + base.2.1))) -
          (tameScalarMultiplier 3
              (chartTower 1 base.1 (chartTangentDirections directions))
              (tameSeedField parameters seed inside) +
            chartTangentPart parameters (directions 0).1 + (directions 0).2.1)) +
      originalGradeNorm grade
        ((((t : ℂ))⁻¹ • ((tameSeedScalar parameters seed inside +
            (base.2.2 + (t : ℂ) • (directions 0).2.2)) -
          (tameSeedScalar parameters seed inside + base.2.2))) - (directions 0).2.2)
    have first_eq : (((t : ℂ))⁻¹ • ((tameScalarMultiplier 3
            (tameRootShifted 0 (tangentQuadratic (base.1 + (t : ℂ) • (directions 0).1)))
            (tameSeedField parameters seed inside) +
          chartTangentPart parameters (base.1 + (t : ℂ) • (directions 0).1) +
          (base.2.1 + (t : ℂ) • (directions 0).2.1)) -
        (tameScalarMultiplier 3 (tameRootShifted 0 (tangentQuadratic base.1))
            (tameSeedField parameters seed inside) +
          chartTangentPart parameters base.1 + base.2.1))) -
        (tameScalarMultiplier 3
            (chartTower 1 base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside) +
          chartTangentPart parameters (directions 0).1 + (directions 0).2.1) =
        (((t : ℂ))⁻¹ • (tameScalarMultiplier 3
            (tameRootShifted 0 (tangentQuadratic (base.1 + (t : ℂ) • (directions 0).1)))
            (tameSeedField parameters seed inside) -
          tameScalarMultiplier 3 (tameRootShifted 0 (tangentQuadratic base.1))
            (tameSeedField parameters seed inside))) -
          tameScalarMultiplier 3
            (chartTower 1 base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside) := by
      rw [chartTangentPart_add, chartTangentPart_smul]
      exact chartQuotient_collapse_main nonzero _ _ _ _ _ _ _
    have second_eq : (((t : ℂ))⁻¹ • ((tameSeedScalar parameters seed inside +
          (base.2.2 + (t : ℂ) • (directions 0).2.2)) -
        (tameSeedScalar parameters seed inside + base.2.2))) - (directions 0).2.2 =
        (0 : ACore parameters 1) :=
      chartQuotient_collapse_affine nonzero _ _ _
    rw [first_eq, second_eq, originalGradeNorm_zero, add_zero]
  | 1, base, directions, axis => by
    have small := chartAxis_planar_small axis
    have slot : chartTangentDirections directions 1 = (directions (Fin.last 1)).1 :=
      chartTangentDirections_top directions
    intro grade
    have tower1 : Tendsto (fun t : ℝ => originalGradeNorm grade
        ((((t : ℂ))⁻¹ • (tameScalarMultiplier 3
              (chartTower 1 (base.1 + (t : ℂ) • (directions (Fin.last 1)).1)
                (chartTangentDirections directions))
              (tameSeedField parameters seed inside) -
            tameScalarMultiplier 3
              (chartTower 1 base.1 (chartTangentDirections directions))
              (tameSeedField parameters seed inside))) -
          tameScalarMultiplier 3
            (chartTower 2 base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside)))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      tower_multiplier_tendsto parameters seed inside 1 base
        (chartTangentDirections directions) ((directions (Fin.last 1)).1) slot small grade
    refine tower1.congr' ?_
    apply eventually_nhdsWithin_of_forall
    intro t _
    show originalGradeNorm grade
        ((((t : ℂ))⁻¹ • (tameScalarMultiplier 3
              (chartTower 1 (base.1 + (t : ℂ) • (directions (Fin.last 1)).1)
                (chartTangentDirections directions))
              (tameSeedField parameters seed inside) -
            tameScalarMultiplier 3
              (chartTower 1 base.1 (chartTangentDirections directions))
              (tameSeedField parameters seed inside))) -
          tameScalarMultiplier 3
            (chartTower 2 base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside)) =
      originalGradeNorm grade
        ((((t : ℂ))⁻¹ • ((tameScalarMultiplier 3
              (chartTower 1 (base.1 + (t : ℂ) • (directions (Fin.last 1)).1)
                (chartTangentDirections (fun position => directions position.castSucc)))
              (tameSeedField parameters seed inside) +
            chartTangentPart parameters (directions ((0 : Fin 1).castSucc)).1 +
            (directions ((0 : Fin 1).castSucc)).2.1) -
          (tameScalarMultiplier 3
              (chartTower 1 base.1
                (chartTangentDirections (fun position => directions position.castSucc)))
              (tameSeedField parameters seed inside) +
            chartTangentPart parameters (directions ((0 : Fin 1).castSucc)).1 +
            (directions ((0 : Fin 1).castSucc)).2.1))) -
          tameScalarMultiplier 3
            (chartTower 2 base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside)) +
      originalGradeNorm grade
        ((((t : ℂ))⁻¹ • ((directions ((0 : Fin 1).castSucc)).2.2 -
            (directions ((0 : Fin 1).castSucc)).2.2)) - 0)
    have tower_moved : chartTower 1 (base.1 + (t : ℂ) • (directions (Fin.last 1)).1)
        (chartTangentDirections (fun position => directions position.castSucc)) =
        chartTower 1 (base.1 + (t : ℂ) • (directions (Fin.last 1)).1)
          (chartTangentDirections directions) :=
      chartTower_congr 1 _ (chartTangentDirections_castSucc directions)
    have tower_base : chartTower 1 base.1
        (chartTangentDirections (fun position => directions position.castSucc)) =
        chartTower 1 base.1 (chartTangentDirections directions) :=
      chartTower_congr 1 _ (chartTangentDirections_castSucc directions)
    rw [tower_moved, tower_base, chartQuotient_collapse_shift ((t : ℂ)),
      chartQuotient_collapse_constant ((t : ℂ)), originalGradeNorm_zero, add_zero]
  | (order + 2), base, directions, axis => by
    have small := chartAxis_planar_small axis
    have slot : chartTangentDirections directions (order + 2) =
        (directions (Fin.last (order + 2))).1 :=
      chartTangentDirections_top directions
    intro grade
    have tower1 : Tendsto (fun t : ℝ => originalGradeNorm grade
        ((((t : ℂ))⁻¹ • (tameScalarMultiplier 3
              (chartTower (order + 2)
                (base.1 + (t : ℂ) • (directions (Fin.last (order + 2))).1)
                (chartTangentDirections directions))
              (tameSeedField parameters seed inside) -
            tameScalarMultiplier 3
              (chartTower (order + 2) base.1 (chartTangentDirections directions))
              (tameSeedField parameters seed inside))) -
          tameScalarMultiplier 3
            (chartTower (order + 3) base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside)))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      tower_multiplier_tendsto parameters seed inside (order + 2) base
        (chartTangentDirections directions) ((directions (Fin.last (order + 2))).1)
        slot small grade
    refine tower1.congr' ?_
    apply eventually_nhdsWithin_of_forall
    intro t _
    show originalGradeNorm grade
        ((((t : ℂ))⁻¹ • (tameScalarMultiplier 3
              (chartTower (order + 2)
                (base.1 + (t : ℂ) • (directions (Fin.last (order + 2))).1)
                (chartTangentDirections directions))
              (tameSeedField parameters seed inside) -
            tameScalarMultiplier 3
              (chartTower (order + 2) base.1 (chartTangentDirections directions))
              (tameSeedField parameters seed inside))) -
          tameScalarMultiplier 3
            (chartTower (order + 3) base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside)) =
      originalGradeNorm grade
        ((((t : ℂ))⁻¹ • (tameScalarMultiplier 3
              (chartTower (order + 2)
                (base.1 + (t : ℂ) • (directions (Fin.last (order + 2))).1)
                (chartTangentDirections (fun position => directions position.castSucc)))
              (tameSeedField parameters seed inside) -
            tameScalarMultiplier 3
              (chartTower (order + 2) base.1
                (chartTangentDirections (fun position => directions position.castSucc)))
              (tameSeedField parameters seed inside))) -
          tameScalarMultiplier 3
            (chartTower (order + 3) base.1 (chartTangentDirections directions))
            (tameSeedField parameters seed inside)) +
      originalGradeNorm grade
        ((((t : ℂ))⁻¹ • ((0 : ACore parameters 1) - 0)) - 0)
    have tower_moved : chartTower (order + 2)
        (base.1 + (t : ℂ) • (directions (Fin.last (order + 2))).1)
        (chartTangentDirections (fun position => directions position.castSucc)) =
        chartTower (order + 2)
          (base.1 + (t : ℂ) • (directions (Fin.last (order + 2))).1)
          (chartTangentDirections directions) :=
      chartTower_congr (order + 2) _ (chartTangentDirections_castSucc directions)
    have tower_base : chartTower (order + 2) base.1
        (chartTangentDirections (fun position => directions position.castSucc)) =
        chartTower (order + 2) base.1 (chartTangentDirections directions) :=
      chartTower_congr (order + 2) _ (chartTangentDirections_castSucc directions)
    rw [tower_moved, tower_base, chartQuotient_collapse_constant ((t : ℂ)),
      originalGradeNorm_zero, add_zero]

end Grad.NonlinearQuotientBounds
