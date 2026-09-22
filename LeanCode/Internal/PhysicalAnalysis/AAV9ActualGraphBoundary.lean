import AAV8ActualWeakGraphUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.GaugeCoefficients.Physical.WeightedTrace

section Boundary
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularSolvedData_radial_outer (data : AnnularForcing lower × AnnularBoundary)
    (mode : HighAnnularMode) :
    weightedRadialTrace 1 lower positive bounded 1
      (annularDataRadialFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularSolvedDataGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data) mode) =
      -((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • data.1.2.2.2 mode) := by
  let solved := annularSolvedDataGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data
  have weak := annularDataGraph_weak parameters lower length positive bounded lengthPositive widthHalf widthLength solved mode
  have endpoint := annularCandidateMomentGraph_outer parameters lower length positive bounded lengthPositive widthHalf widthLength
    solved.val.1 solved.val.2 mode weak
    (annularDataRadialFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength solved mode)
    (annularDataRadialFluxGraph_ordinary_value parameters lower length positive bounded lengthPositive widthHalf widthLength solved mode)
  have boundary := annularQMomentGraph_outer parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode
  unfold annularQMomentGraph at boundary
  rw [map_add, map_smul] at boundary
  exact endpoint.symm.trans boundary

/-- The genuine conormal trace of the constructed inverse is precisely its
prescribed normalized outer datum. This is derived, not stored separately. -/
theorem annularSolvedData_outer (data : AnnularForcing lower × AnnularBoundary) :
    annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1
      (annularSolvedDataGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data) =
      -data.1.2.2.2 := by
  apply lp.ext
  funext mode
  change annularFluxTrace lower positive bounded 1
    (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data) mode =
    -(data.1.2.2.2 mode)
  rw [annularFluxTrace_apply]
  change (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ •
    weightedRadialSection 1 lower positive bounded
      (annularDataRadialFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularSolvedDataGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data) mode)
      ⟨radialEndpointRadius lower 1, radialEndpointRadius_mem lower bounded.le 1⟩ = _
  rw [weightedRadialSection_endpoint, annularSolvedData_radial_outer]
  change (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ •
    -(Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) • data.1.2.2.2 mode) = _
  rw [smul_neg, smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.2 (Grad.AnnularFluxTrace.annularFrequency_pos mode)).ne', one_smul]

end Boundary
end Grad.AnnularConverse
