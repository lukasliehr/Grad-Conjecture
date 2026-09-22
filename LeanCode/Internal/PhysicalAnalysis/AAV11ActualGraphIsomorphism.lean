import AAV10ClosedBoundaryGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.GaugeCoefficients.Physical.WeightedTrace

section Isomorphism
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularBoundaryGraph_right (data : AnnularForcing lower × AnnularBoundary) :
    annularBoundaryGraphForward parameters lower length positive bounded lengthPositive widthHalf widthLength
      (annularBoundaryGraphInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data) = data := by
  apply Prod.ext
  · rfl
  · exact annularVariationalSolution_inner parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2

theorem annularBoundaryGraph_left
    (data : annularBoundaryFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength) :
    annularBoundaryGraphInverse parameters lower length positive bounded lengthPositive widthHalf widthLength
      (annularBoundaryGraphForward parameters lower length positive bounded lengthPositive widthHalf widthLength data) = data := by
  have outer : annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1 data.val =
      -data.val.val.2.2.2.2 := by
    have member := data.property
    change annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1 data.val +
      data.val.val.2.2.2.2 = 0 at member
    exact eq_neg_of_add_eq_zero_left member
  have same := annularDataGraph_unique parameters lower length positive bounded lengthPositive widthHalf widthLength data.val
    (annularEnergyTrace lower length positive bounded lengthPositive 0 data.val.val.1) rfl outer
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact same.symm
  · rfl

/-- The exact original energy/forcing weak graph, with its genuine conormal
boundary, is continuously linearly isomorphic to independently prescribed
data. This is the converse component of the four-source graph theorem. -/
def annularBoundaryGraphEquivalence :
    annularBoundaryFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength ≃L[ℂ]
      (AnnularForcing lower × AnnularBoundary) where
  toLinearEquiv :=
    { toLinearMap := (annularBoundaryGraphForward parameters lower length positive bounded lengthPositive widthHalf widthLength).toLinearMap
      invFun := annularBoundaryGraphInverse parameters lower length positive bounded lengthPositive widthHalf widthLength
      left_inv := annularBoundaryGraph_left parameters lower length positive bounded lengthPositive widthHalf widthLength
      right_inv := annularBoundaryGraph_right parameters lower length positive bounded lengthPositive widthHalf widthLength }
  continuous_toFun := (annularBoundaryGraphForward parameters lower length positive bounded lengthPositive widthHalf widthLength).continuous
  continuous_invFun := (annularBoundaryGraphInverse parameters lower length positive bounded lengthPositive widthHalf widthLength).continuous

end Isomorphism
end Grad.AnnularConverse
