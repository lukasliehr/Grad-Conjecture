import AAV7GenericMomentEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.GaugeCoefficients.Physical.WeightedTrace

section Converse
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularDataGraph_weak
    (data : annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength)
    (mode : HighAnnularMode) :
    CollarWeakDerivative lower
      (radialOrdinary 1 lower positive
        (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength data.val.1 data.val.2.1 mode))
      (annularNormalizedQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le data.val.1 data.val.2 mode) := by
  have weak := weightedRadial_weak 1 lower positive bounded.le
    (annularDataRadialFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data mode)
  rw [annularDataRadialFluxGraph_ordinary_value, annularDataRadialFluxGraph_ordinary_slope] at weak
  exact weak

theorem annularDataGraph_outer
    (data : annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength)
    (outer : annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1 data =
      -data.val.2.2.2.2) (mode : HighAnnularMode) :
    weightedRadialTrace 1 lower positive bounded 1
      (annularDataRadialFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data mode) =
      -((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • data.val.2.2.2.2 mode) := by
  have point := congrArg (fun trace : AnnularBoundary => trace mode) outer
  change annularFluxTrace lower positive bounded 1
    (annularDataFluxGraph parameters lower length positive lengthPositive widthHalf widthLength data) mode =
    -(data.val.2.2.2.2 mode) at point
  rw [annularFluxTrace_apply] at point
  change (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ •
    weightedRadialSection 1 lower positive bounded
      (annularDataRadialFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data mode)
      ⟨radialEndpointRadius lower 1, radialEndpointRadius_mem lower bounded.le 1⟩ = _ at point
  rw [weightedRadialSection_endpoint] at point
  have scaled := congrArg (fun value : ComplexEuclidean 1 =>
    Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) • value) point
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 (Grad.AnnularFluxTrace.annularFrequency_pos mode)).ne', one_smul, smul_neg] at scaled
  exact scaled

/-- Every element of the independently defined full weak flux graph with
the actual boundary rows is the previously constructed variational inverse.
No variational identity or source differentiability is an assumption. -/
theorem annularDataGraph_unique
    (data : annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength)
    (innerValue : AnnularBoundary)
    (innerLaw : annularEnergyTrace lower length positive bounded lengthPositive 0 data.val.1 = innerValue)
    (outerLaw : annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1 data =
      -data.val.2.2.2.2) :
    data.val.1 = annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength data.val.2 innerValue := by
  apply annularVariationalSolution_unique parameters lower length positive bounded lengthPositive widthHalf widthLength
    data.val.2 innerValue data.val.1 innerLaw
  apply annularSingleTests_imply_variational parameters lower length positive bounded lengthPositive widthHalf widthLength
  intro mode test innerZero
  let weak := annularDataGraph_weak parameters lower length positive bounded lengthPositive widthHalf widthLength data mode
  let graph := annularCandidateMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength
    data.val.1 data.val.2 mode weak
  apply annularMomentGraph_single_test parameters lower length positive bounded lengthPositive widthHalf widthLength
    data.val.1 data.val.2 mode graph
  · exact compactWeakRadialGraph_value lower positive bounded _ _ _
  · exact compactWeakRadialGraph_slope lower positive bounded _ _ _
  · exact (annularCandidateMomentGraph_outer parameters lower length positive bounded lengthPositive widthHalf widthLength
      data.val.1 data.val.2 mode weak
      (annularDataRadialFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data mode)
      (annularDataRadialFluxGraph_ordinary_value parameters lower length positive bounded lengthPositive widthHalf widthLength data mode)).trans
      (annularDataGraph_outer parameters lower length positive bounded lengthPositive widthHalf widthLength data outerLaw mode)
  · exact innerZero

end Converse
end Grad.AnnularConverse
