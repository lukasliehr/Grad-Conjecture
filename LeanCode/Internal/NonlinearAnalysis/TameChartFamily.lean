import TameChartRange

noncomputable section

set_option maxHeartbeats 1600000

open Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct
open Grad.Constraints.Multipliers

/-! The chart derivative family: the literal chart at order zero, the tower
multiplied into the fixed seed field at every positive order, and the affine
direction parts at order one; with its genuineness along the newest
direction on the literal Q13 ball. -/

variable {parameters : PhaseParameters}

/-- Extension of a finite direction tuple to all indices, by zero. -/
def chartTangentDirections {order : ℕ}
    (directions : Fin order → ChartState parameters) :
    ℕ → TangentCoefficient parameters :=
  fun index => if bounded : index < order then (directions ⟨index, bounded⟩).1 else 0

theorem chartTangentDirections_lt {order : ℕ}
    (directions : Fin order → ChartState parameters) (index : ℕ) (bounded : index < order) :
    chartTangentDirections directions index = (directions ⟨index, bounded⟩).1 :=
  dif_pos bounded

theorem chartTangentDirections_fin {order : ℕ}
    (directions : Fin order → ChartState parameters) (index : Fin order) :
    chartTangentDirections directions index.val = (directions index).1 := by
  rw [chartTangentDirections_lt directions index.val index.isLt]

theorem chartTangentDirections_castSucc {order : ℕ}
    (directions : Fin (order + 1) → ChartState parameters) :
    ∀ index < order,
      chartTangentDirections (fun position => directions position.castSucc) index =
        chartTangentDirections directions index := by
  intro index bounded
  rw [chartTangentDirections_lt _ index bounded,
    chartTangentDirections_lt directions index (by omega)]
  rfl

theorem chartTangentDirections_top {order : ℕ}
    (directions : Fin (order + 1) → ChartState parameters) :
    chartTangentDirections directions order = (directions (Fin.last order)).1 := by
  rw [chartTangentDirections_lt directions order (Nat.lt_succ_self order)]
  rfl

/-- The one-high derivative family of the normalized chart. -/
def chartDerivativeFamily (parameters : PhaseParameters)
    (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain) :
    (order : ℕ) → ChartState parameters →
      (Fin order → ChartState parameters) → ChartOutput parameters
  | 0, state, _ => normalizedChart parameters seed inside state
  | 1, state, directions =>
      (tameScalarMultiplier 3 (chartTower 1 state.1 (chartTangentDirections directions))
          (tameSeedField parameters seed inside) +
        valueMapCore parameters tameTangentInclusion
          (tameScalarMultiplier 1 (tangentComponent (directions 0).1 0)
              (tameCoordinateScalarField parameters 0) +
            tameScalarMultiplier 1 (tangentComponent (directions 0).1 1)
              (tameCoordinateScalarField parameters 1)) +
        (directions 0).2.1,
       (directions 0).2.2)
  | order + 2, state, directions =>
      (tameScalarMultiplier 3
          (chartTower (order + 2) state.1 (chartTangentDirections directions))
          (tameSeedField parameters seed inside), 0)

theorem chartDerivativeFamily_zeroth (parameters : PhaseParameters)
    (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain)
    (state : ChartState parameters) :
    chartDerivativeFamily parameters seed inside 0 state (fun position => position.elim0) =
      normalizedChart parameters seed inside state := rfl

/-! ### Coefficient linearity of the multiplier -/

theorem tameScalarMultiplier_sub (dimension : ℕ)
    [Nontrivial (ComplexEuclidean dimension)]
    (first second : TameCoefficient parameters) (field : ACore parameters dimension) :
    tameScalarMultiplier dimension (first - second) field =
      tameScalarMultiplier dimension first field -
        tameScalarMultiplier dimension second field := by
  have add_law := tameScalarMultiplier_add dimension (first - second) second field
  rw [sub_add_cancel] at add_law
  rw [eq_sub_iff_add_eq]
  exact add_law.symm

/-- The multiplier of an envelope-differentiable coefficient curve applied
to a fixed field is differentiable in every original grade norm. -/
theorem tendsto_multiplier_quotient (dimension : ℕ)
    [Nontrivial (ComplexEuclidean dimension)] (fixed : ACore parameters dimension)
    {curve : ℝ → TameCoefficient parameters} {derivative : TameCoefficient parameters}
    (differentiable : HasEnvDerivAt curve derivative) (grade : ℕ) :
    Tendsto (fun t : ℝ => originalGradeNorm grade
      ((((t : ℂ))⁻¹ • (tameScalarMultiplier dimension (curve t) fixed -
          tameScalarMultiplier dimension (curve 0) fixed)) -
        tameScalarMultiplier dimension derivative fixed))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have argument_eq : ∀ t : ℝ,
      (((t : ℂ))⁻¹ • (tameScalarMultiplier dimension (curve t) fixed -
          tameScalarMultiplier dimension (curve 0) fixed)) -
        tameScalarMultiplier dimension derivative fixed =
      tameScalarMultiplier dimension
        ((((t : ℂ))⁻¹ • (curve t - curve 0)) - derivative) fixed := by
    intro t
    rw [tameScalarMultiplier_sub, tameScalarMultiplier_smul, tameScalarMultiplier_sub]
  have majorized : ∀ t : ℝ, originalGradeNorm grade
      ((((t : ℂ))⁻¹ • (tameScalarMultiplier dimension (curve t) fixed -
          tameScalarMultiplier dimension (curve 0) fixed)) -
        tameScalarMultiplier dimension derivative fixed) ≤
      multiplierConstant grade parameters.gamma *
        coefficientEnvelope grade ((((t : ℂ))⁻¹ • (curve t - curve 0)) - derivative) *
        originalGradeNorm grade fixed := by
    intro t
    rw [argument_eq t]
    exact tameScalarMultiplier_bound dimension _ fixed grade
  have limit : Tendsto (fun t : ℝ => multiplierConstant grade parameters.gamma *
      coefficientEnvelope grade ((((t : ℂ))⁻¹ • (curve t - curve 0)) - derivative) *
      originalGradeNorm grade fixed) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have shape := ((differentiable grade).const_mul
      (multiplierConstant grade parameters.gamma)).mul_const
      (originalGradeNorm grade fixed)
    simpa using shape
  exact squeeze_zero' (Eventually.of_forall
    (fun _ => originalGradeNorm_nonnegative _ _)) (Eventually.of_forall majorized) limit

end Grad.NonlinearQuotientBounds
