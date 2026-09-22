import DIL1Restriction

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open Grad.WeightedJets
open scoped BigOperators Topology

namespace Grad.SpatialDilation

theorem block_consumer : BlockGoal :=
  ⟨geometry_goal, field_goal, test_goal, weak_goal, tuple_goal, plane_continuity_goal, raw_restriction_goal, jet_goal⟩

theorem raw_norm_consumer (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (field : FieldL2 dimension domain) :
    ‖fieldDilation dimension domain measurableDomain scale field‖ = scale.val⁻¹ * ‖field‖ :=
  rawValue_norm dimension domain measurableDomain scale field

theorem stored_norm_consumer (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order (disk radius) exponent) :
    ‖jetDilation dimension order radius scale exponent jet‖ ^ 2 =
      ∑ index : JetIndex order, scale.val ^ (2 * (degree index : ℤ) - 2) * ‖jet.val index‖ ^ 2 :=
  tupleValue_norm_sq dimension order radius scale jet.val

theorem integral_consumer (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order (disk radius) exponent)
    (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : TestFunction (expandedDisk radius scale)) :
    (∫ point in expandedDisk radius scale, test.toFun point • inner ℂ vector
      (Realization.recoveredDerivative dimension order (expandedDisk radius scale) exponent index
        (jetDilation dimension order radius scale exponent jet) point cell)) =
      (-1 : ℂ) ^ degree index * ∫ point in expandedDisk radius scale,
        Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
          inner ℂ vector (base dimension order (expandedDisk radius scale) exponent
            (jetDilation dimension order radius scale exponent jet) point cell) :=
  Realization.recoveredDerivative_integral dimension order (expandedDisk radius scale) exponent index
    (jetDilation dimension order radius scale exponent jet) cell vector test

def graphDilation (dimension order weight : ℕ) (radius : ℝ) (scale : Scale) :
    GraphGrade dimension order weight (disk radius) →L[ℂ] GraphGrade dimension order weight (expandedDisk radius scale) :=
  jetDilation dimension order radius scale (fun _ => weight)

def mixedDilation (dimension grade : ℕ) (radius : ℝ) (scale : Scale) :
    Mixed dimension grade (disk radius) →L[ℂ] Mixed dimension grade (expandedDisk radius scale) :=
  jetDilation dimension grade radius scale (fun index => grade - degree index)

theorem graph_consumer (dimension order weight : ℕ) (radius : ℝ) :
    (∀ scale : Scale, JetLaws dimension order radius scale (fun _ => weight)
      (graphDilation dimension order weight radius scale)) ∧
    ∀ jet : GraphGrade dimension order weight (disk radius),
      Filter.Tendsto (fun scale : Scale => restrictExpanded dimension order radius scale (fun _ => weight)
        (graphDilation dimension order weight radius scale jet)) (𝓝 oneScale) (𝓝 jet) :=
  ⟨fun scale => jetDilation_laws dimension order radius scale (fun _ => weight),
    restricted_jet_tendsto dimension order radius (fun _ => weight)⟩

theorem mixed_consumer (dimension grade : ℕ) (radius : ℝ) :
    (∀ scale : Scale, JetLaws dimension grade radius scale (fun index => grade - degree index)
      (mixedDilation dimension grade radius scale)) ∧
    ∀ jet : Mixed dimension grade (disk radius),
      Filter.Tendsto (fun scale : Scale => restrictExpanded dimension grade radius scale (fun index => grade - degree index)
        (mixedDilation dimension grade radius scale jet)) (𝓝 oneScale) (𝓝 jet) :=
  ⟨fun scale => jetDilation_laws dimension grade radius scale (fun index => grade - degree index),
    restricted_jet_tendsto dimension grade radius (fun index => grade - degree index)⟩

theorem order_zero_base (dimension : ℕ) (radius : ℝ) (scale : Scale) (exponent : JetIndex 0 → ℕ)
    (jet : WJet dimension 0 (disk radius) exponent) :
    base dimension 0 (expandedDisk radius scale) exponent (jetDilation dimension 0 radius scale exponent jet) =
      rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale (base dimension 0 (disk radius) exponent jet) :=
  jetDilation_base dimension 0 radius scale exponent jet

end Grad.SpatialDilation
