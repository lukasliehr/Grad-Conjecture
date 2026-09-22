import ASG22WeakGraphConverse

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def weakRadialRealization (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CollarWeakDerivative lower value derivative) : WeightedRadialH1 dimension lower :=
  (weakPair_in_weightedCompletion dimension lower positive bounded value derivative weak).choose

theorem weakRadialRealization_value (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CollarWeakDerivative lower value derivative) :
    collarH1Coordinate (ComplexEuclidean dimension) lower 0
      (weightedToOrdinary dimension lower positive bounded.le
        (weakRadialRealization dimension lower positive bounded value derivative weak)) = value :=
  (weakPair_in_weightedCompletion dimension lower positive bounded value derivative weak).choose_spec.1

theorem weakRadialRealization_slope (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CollarWeakDerivative lower value derivative) :
    collarH1Coordinate (ComplexEuclidean dimension) lower 1
      (weightedToOrdinary dimension lower positive bounded.le
        (weakRadialRealization dimension lower positive bounded value derivative weak)) = derivative :=
  (weakPair_in_weightedCompletion dimension lower positive bounded value derivative weak).choose_spec.2

def weakRadialEnergy (dimension : ℕ) (lower : ℝ)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower) : ℝ :=
  ∫ radius in lower..1, radius * (‖value radius‖ ^ 2 + ‖derivative radius‖ ^ 2)

theorem weakRadialRealization_norm_sq (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CollarWeakDerivative lower value derivative) :
    ‖weakRadialRealization dimension lower positive bounded value derivative weak‖ ^ 2 =
      weakRadialEnergy dimension lower value derivative := by
  rw [weightedRadialH1_norm_sq,
    weightedRadialCoordinate_eq_sqrt dimension lower positive bounded.le,
    weightedRadialCoordinate_eq_sqrt dimension lower positive bounded.le,
    weakRadialRealization_value, weakRadialRealization_slope,
    radialSqrtMap_norm_sq dimension lower positive bounded.le, radialSqrtMap_norm_sq dimension lower positive bounded.le]
  rw [← intervalIntegral.integral_add
    (radialWeightedEnergy_integrable dimension lower positive bounded.le value)
    (radialWeightedEnergy_integrable dimension lower positive bounded.le derivative)]
  apply intervalIntegral.integral_congr
  intro radius _
  ring

end Grad.AnnularSourceGraph
