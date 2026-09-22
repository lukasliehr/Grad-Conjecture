import TameChartSum
import TameChartFamily
import RootUnitInterface

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! Q15 packaged: the derivative tower of `a(τ) = F(τ·τ/2)` along finite
direction tuples, its genuineness along the newest direction on the literal
Q13 ball (from the accepted exact-once tower step), and the exact one-high
envelope estimate in `Fin`-tuple form (from the accepted tower-level range
estimate). -/

variable {parameters : PhaseParameters}

/-- The literal Q13 condition on chart states is the tangential condition. -/
theorem chartAxisCondition_iff (state : ChartState parameters) :
    ChartAxisCondition state ↔ RootAxisCondition state.1 := Iff.rfl

/-- Extension of a finite tangential direction tuple to all indices, by zero. -/
def rootDirections {order : ℕ} (directions : Fin order → TangentCoefficient parameters) :
    ℕ → TangentCoefficient parameters :=
  fun index => if bounded : index < order then directions ⟨index, bounded⟩ else 0

theorem rootDirections_lt {order : ℕ}
    (directions : Fin order → TangentCoefficient parameters) (index : ℕ)
    (bounded : index < order) :
    rootDirections directions index = directions ⟨index, bounded⟩ :=
  dif_pos bounded

theorem rootDirections_fin {order : ℕ}
    (directions : Fin order → TangentCoefficient parameters) (index : Fin order) :
    rootDirections directions index.val = directions index := by
  rw [rootDirections_lt directions index.val index.isLt]

theorem rootDirections_castSucc {order : ℕ}
    (directions : Fin (order + 1) → TangentCoefficient parameters) :
    ∀ index < order,
      rootDirections (fun position => directions position.castSucc) index =
        rootDirections directions index := by
  intro index bounded
  rw [rootDirections_lt _ index bounded, rootDirections_lt directions index (by omega)]
  rfl

theorem rootDirections_top {order : ℕ}
    (directions : Fin (order + 1) → TangentCoefficient parameters) :
    rootDirections directions order = directions (Fin.last order) := by
  rw [rootDirections_lt directions order (Nat.lt_succ_self order)]
  rfl

/-- The Q15 derivative tower of the chart root along a finite direction tuple. -/
def rootDerivativeFamily (order : ℕ) (base : TangentCoefficient parameters)
    (directions : Fin order → TangentCoefficient parameters) : TameCoefficient parameters :=
  chartTower order base (rootDirections directions)

theorem rootDerivativeFamily_zero (base : TangentCoefficient parameters)
    (directions : Fin 0 → TangentCoefficient parameters) :
    rootDerivativeFamily 0 base directions = rootChart base :=
  chartTower_zero base (rootDirections directions)

/-- Genuineness: on the literal Q13 ball, level `order` differentiates along
the newest direction to level `order + 1`, in every graded envelope. -/
theorem rootDerivativeFamily_genuine (order : ℕ) (base : TangentCoefficient parameters)
    (directions : Fin (order + 1) → TangentCoefficient parameters)
    (axis : RootAxisCondition base) :
    HasEnvDerivAt
      (fun t : ℝ => rootDerivativeFamily order (base + (t : ℂ) • directions (Fin.last order))
        (fun position => directions position.castSucc))
      (rootDerivativeFamily (order + 1) base directions) := by
  have small := rootAxis_planar_small axis
  have step := chartTower_hasEnvDerivAt order base (rootDirections directions) small
  rw [rootDirections_top directions] at step
  apply step.congr_curve
  intro t
  exact chartTower_congr order _ (rootDirections_castSucc directions)

/-- The exact Q15 one-high estimate of every tower level on the Q13 ball. -/
theorem rootDerivativeFamily_bound (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : TangentCoefficient parameters)
        (directions : Fin order → TangentCoefficient parameters),
        RootAxisCondition base →
        coefficientEnvelope grade (rootDerivativeFamily order base directions) ≤
          constant * ((1 + tangentPlanarEnvelope grade base) *
              ∏ position, tangentPlanarEnvelope 0 (directions position) +
            ∑ position, tangentPlanarEnvelope grade (directions position) *
              ∏ other ∈ Finset.univ.erase position,
                tangentPlanarEnvelope 0 (directions other)) := by
  obtain ⟨constant, constant_nonneg, bound⟩ :=
    chartTower_range_envelope_le (parameters := parameters) grade order
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨constant, constant_nonneg, ?_⟩
  intro base directions axis
  have raw := bound base (rootDirections directions) (rootAxis_planar_lt_half axis).le
  rw [lowIndexProd_range, oneHighIndex_range] at raw
  have low_eq : (∏ index : Fin order,
      tangentPlanarEnvelope 0 (rootDirections directions index.val)) =
      ∏ position, tangentPlanarEnvelope 0 (directions position) :=
    Finset.prod_congr rfl (fun index _ => by rw [rootDirections_fin])
  have high_eq : (∑ index : Fin order,
      tangentPlanarEnvelope grade (rootDirections directions index.val) *
        ∏ other ∈ Finset.univ.erase index,
          tangentPlanarEnvelope 0 (rootDirections directions other.val)) =
      ∑ position, tangentPlanarEnvelope grade (directions position) *
        ∏ other ∈ Finset.univ.erase position,
          tangentPlanarEnvelope 0 (directions other) := by
    apply Finset.sum_congr rfl
    intro index _
    rw [rootDirections_fin]
    congr 1
    exact Finset.prod_congr rfl (fun other _ => by rw [rootDirections_fin])
  rw [low_eq, high_eq] at raw
  exact raw

/-! ### Identification with the accepted chart -/

/-- The chart's tangential direction extension is the root unit's extension
of the tangential parts. -/
theorem chartTangentDirections_eq_rootDirections {order : ℕ}
    (directions : Fin order → ChartState parameters) :
    chartTangentDirections directions =
      rootDirections (fun position => (directions position).1) := rfl

/-- The accepted chart tower along chart directions is the root derivative
family of the tangential parts. -/
theorem chartTower_eq_rootDerivativeFamily (order : ℕ) (state : ChartState parameters)
    (directions : Fin order → ChartState parameters) :
    chartTower order state.1 (chartTangentDirections directions) =
      rootDerivativeFamily order state.1 (fun position => (directions position).1) := rfl

/-- The root factor of the literal Q18 normalized chart is the root unit's
`rootChart`. -/
theorem normalizedChart_rootChart (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain) (state : ChartState parameters) :
    normalizedChart parameters seed inside state =
      (tameScalarMultiplier 3 (rootChart state.1) (tameSeedField parameters seed inside) +
        valueMapCore parameters tameTangentInclusion
          (tameScalarMultiplier 1 (tangentComponent state.1 0)
              (tameCoordinateScalarField parameters 0) +
            tameScalarMultiplier 1 (tangentComponent state.1 1)
              (tameCoordinateScalarField parameters 1)) +
        state.2.1,
       tameSeedScalar parameters seed inside + state.2.2) := rfl

end Grad.NonlinearQuotientBounds
