import TameSeedField

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

/-! The exact Q20 interface: the chart state with the literal Q16 product
norms, the literal Q13 axis condition with `C_ax = √(1+π)`, the literal Q18
normalized chart, and the Q20 goal — genuine directional derivative tower
with the exact one-high `X⁴`/`X^q` estimates on the fixed base ball. -/

variable {parameters : PhaseParameters}

/-- The chart state `x = (τ, ṽ, s)`. -/
abbrev ChartState (parameters : PhaseParameters) : Type :=
  TangentCoefficient parameters × ACore parameters 3 × ACore parameters 1

/-- The literal Q16 norm `‖x‖_{X^q} = ‖τ‖_{T^{q+1}} + ‖ṽ‖_{A^q} + ‖s‖_{A^q}`. -/
def chartStateNorm (grade : ℕ) (state : ChartState parameters) : ℝ :=
  tangentNorm (grade + 1) state.1 + originalGradeNorm grade state.2.1 +
    originalGradeNorm grade state.2.2

theorem chartStateNorm_nonneg (grade : ℕ) (state : ChartState parameters) :
    0 ≤ chartStateNorm grade state :=
  add_nonneg (add_nonneg (tangentNorm_nonneg _ _) (originalGradeNorm_nonnegative _ _))
    (originalGradeNorm_nonnegative _ _)

/-- Monotonicity of the tangential norm in the grade. -/
theorem tangentNorm_mono {lower upper : ℕ} (gradeLe : lower ≤ upper)
    (family : TangentCoefficient parameters) :
    tangentNorm lower family ≤ tangentNorm upper family := by
  apply Real.sqrt_le_sqrt
  apply (family.property lower).tsum_le_tsum _ (family.property upper)
  intro cell
  rw [tangentNormTerm, tangentNormTerm]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact pow_le_pow_right₀ (Grad.CellWeights.cellWeight_one_le cell)
    (Nat.mul_le_mul_left 2 gradeLe)

theorem chartStateNorm_mono {lower upper : ℕ} (gradeLe : lower ≤ upper)
    (state : ChartState parameters) :
    chartStateNorm lower state ≤ chartStateNorm upper state := by
  apply add_le_add
  apply add_le_add
  · exact tangentNorm_mono (by omega) state.1
  · exact originalGradeNorm_mono gradeLe state.2.1
  · exact originalGradeNorm_mono gradeLe state.2.2

/-- The literal Q13 axis condition `‖τ‖_{T¹} < (2 C_ax)⁻¹`. -/
def ChartAxisCondition (state : ChartState parameters) : Prop :=
  tangentNorm 1 state.1 < (2 * axisConstant)⁻¹

/-- The chart output pair `(v, w)` with its combined grade norm. -/
abbrev ChartOutput (parameters : PhaseParameters) : Type :=
  ACore parameters 3 × ACore parameters 1

def chartOutputNorm (grade : ℕ) (output : ChartOutput parameters) : ℝ :=
  originalGradeNorm grade output.1 + originalGradeNorm grade output.2

theorem chartOutputNorm_nonneg (grade : ℕ) (output : ChartOutput parameters) :
    0 ≤ chartOutputNorm grade output :=
  add_nonneg (originalGradeNorm_nonnegative _ _) (originalGradeNorm_nonnegative _ _)

/-- The literal Q18 normalized chart
`𝒮_p(τ, ṽ, s) = (a(τ) ι M_p y + e_T (τ·y) + ṽ, w_{M_p} + s)`. -/
def normalizedChart (parameters : PhaseParameters)
    (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain)
    (state : ChartState parameters) : ChartOutput parameters :=
  (tameScalarMultiplier 3 (tameRootShifted 0 (tangentQuadratic state.1))
      (tameSeedField parameters seed inside) +
    valueMapCore parameters tameTangentInclusion
      (tameScalarMultiplier 1 (tangentComponent state.1 0)
          (tameCoordinateScalarField parameters 0) +
        tameScalarMultiplier 1 (tangentComponent state.1 1)
          (tameCoordinateScalarField parameters 1)) +
    state.2.1,
   tameSeedScalar parameters seed inside + state.2.2)

/-- Genuine directional differentiability of a chart-output map along a real
parameter, in every combined output grade norm at once. -/
def IsChartDirectionalDerivative
    (mapping : ChartState parameters → ChartOutput parameters)
    (base direction : ChartState parameters)
    (derivative : ChartOutput parameters) : Prop :=
  ∀ grade : ℕ, Filter.Tendsto (fun t : ℝ => chartOutputNorm grade
      ((((t : ℂ))⁻¹ • (mapping (base + (t : ℂ) • direction) - mapping base)) - derivative))
    (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds 0)

/-- Q20: the literal normalized chart on the literal Q13 axis ball, with a
genuine iterated directional derivative tower and the exact one-high
`X⁴`/`X^q` estimates on every fixed `X⁴` ball, at every grade `q ≥ 3`.
The derivative family is an output; nothing is assumed about it. -/
def NormalizedChartDerivativeGoal : Prop :=
  ∀ (parameters : PhaseParameters) (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain),
    ∃ derivative : (order : ℕ) → ChartState parameters →
        (Fin order → ChartState parameters) → ChartOutput parameters,
      (∀ state, derivative 0 state (fun position => position.elim0) =
        normalizedChart parameters seed inside state) ∧
      (∀ (order : ℕ) (base : ChartState parameters)
        (directions : Fin (order + 1) → ChartState parameters),
        ChartAxisCondition base →
        IsChartDirectionalDerivative
          (fun state => derivative order state
            (fun position => directions position.castSucc))
          base (directions (Fin.last order)) (derivative (order + 1) base directions)) ∧
      ∀ (grade : ℕ), 3 ≤ grade → ∀ (order : ℕ) (bound : ℝ),
        ∃ constant : ℝ, 0 ≤ constant ∧
        ∀ (base : ChartState parameters) (directions : Fin order → ChartState parameters),
          ChartAxisCondition base →
          chartStateNorm 4 base ≤ bound →
          chartOutputNorm grade (derivative order base directions) ≤
            constant * ((1 + chartStateNorm grade base) *
              ∏ position, chartStateNorm 4 (directions position) +
              ∑ position, chartStateNorm grade (directions position) *
                ∏ other ∈ Finset.univ.erase position, chartStateNorm 4 (directions other))

end Grad.NonlinearQuotientBounds
