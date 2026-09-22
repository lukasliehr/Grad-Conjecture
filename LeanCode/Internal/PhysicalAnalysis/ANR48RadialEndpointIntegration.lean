import ANR47ActualFluxBoundaryEquation

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Integration by parts with both actual endpoint traces of the same
completed radial graph. The test may be nonzero at either endpoint. -/
theorem weightedRadial_endpoint_parts (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : WeightedRadialH1 dimension lower)
    (vector : ComplexEuclidean dimension) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test) :
    collarPairing lower ⟨deriv test, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩ vector
      (collarH1Coordinate (ComplexEuclidean dimension) lower 0 (weightedToOrdinary dimension lower positive bounded.le field)) +
    collarPairing lower ⟨test, smooth.continuous⟩ vector
      (collarH1Coordinate (ComplexEuclidean dimension) lower 1 (weightedToOrdinary dimension lower positive bounded.le field)) =
      test 1 • inner ℂ vector (weightedRadialTrace dimension lower positive bounded 1 field) -
        test lower • inner ℂ vector (weightedRadialTrace dimension lower positive bounded 0 field) := by
  let valueMap := (collarH1Coordinate (ComplexEuclidean dimension) lower 0).comp
    (weightedToOrdinary dimension lower positive bounded.le)
  let slopeMap := (collarH1Coordinate (ComplexEuclidean dimension) lower 1).comp
    (weightedToOrdinary dimension lower positive bounded.le)
  let testMap : C(ℝ, ℝ) := ⟨test, smooth.continuous⟩
  let derivativeMap : C(ℝ, ℝ) := ⟨deriv test, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩
  have leftContinuous : Continuous (fun field : WeightedRadialH1 dimension lower =>
      collarPairing lower derivativeMap vector (valueMap field) + collarPairing lower testMap vector (slopeMap field)) :=
    ((collarPairing lower derivativeMap vector).continuous.comp valueMap.continuous).add
      ((collarPairing lower testMap vector).continuous.comp slopeMap.continuous)
  have rightContinuous : Continuous (fun field : WeightedRadialH1 dimension lower =>
      test 1 • inner ℂ vector (weightedRadialTrace dimension lower positive bounded 1 field) -
        test lower • inner ℂ vector (weightedRadialTrace dimension lower positive bounded 0 field)) :=
    (((innerSL ℂ vector).continuous.comp (weightedRadialTrace dimension lower positive bounded 1).continuous).const_smul (test 1)).sub
      (((innerSL ℂ vector).continuous.comp (weightedRadialTrace dimension lower positive bounded 0).continuous).const_smul (test lower))
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (isClosed_eq leftContinuous rightContinuous) _ field
  intro core
  change collarPairing lower derivativeMap vector
      (collarH1Coordinate (ComplexEuclidean dimension) lower 0 (weightedToOrdinary dimension lower positive bounded.le (weightedRadialCoreInto dimension lower core))) +
    collarPairing lower testMap vector
      (collarH1Coordinate (ComplexEuclidean dimension) lower 1 (weightedToOrdinary dimension lower positive bounded.le (weightedRadialCoreInto dimension lower core))) = _
  rw [weightedToOrdinary_core, collarH1Coordinate_core_zero, collarH1Coordinate_core_one,
    weightedRadialTrace_core, weightedRadialTrace_core]
  apply (congrArg₂ (fun first second : ℂ => first + second)
    (collarPairing_core lower bounded.le derivativeMap vector core.val.val.1)
    (collarPairing_core lower bounded.le testMap vector core.val.val.2)).trans
  have index : (1 : Fin 2) ≠ 0 := by decide
  simp only [radialEndpointRadius, if_neg index]
  let pairing := (innerSL ℂ vector).restrictScalars ℝ
  have pairedDerivative (radius : ℝ) :
      HasDerivAt (fun point => inner ℂ vector (core.val.val.1 point)) (inner ℂ vector (core.val.val.2 radius)) radius :=
    pairing.hasFDerivAt.comp_hasDerivAt radius (core.val.property radius)
  have identity := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := lower) (b := 1) (fun radius _ => (smooth.differentiable (by simp) radius).hasDerivAt)
    (fun radius _ => pairedDerivative radius)
    (derivativeMap.continuous.intervalIntegrable lower 1)
    ((pairing.continuous.comp core.val.val.2.continuous).intervalIntegrable lower 1)
  change (∫ radius in lower..1, deriv test radius • inner ℂ vector (core.val.val.1 radius)) +
    (∫ radius in lower..1, test radius • inner ℂ vector (core.val.val.2 radius)) = _
  rw [identity]
  abel

end Grad.CircularHighRegularity
