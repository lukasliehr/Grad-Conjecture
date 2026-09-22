import AAX4OriginalFirstResidual
import AAV12ExactWeakGraphConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFourSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.AnnularGrades Grad.AnnularConverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Natural
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

local notation "FG" => annularFourGraph parameters lower length positive lengthPositive widthHalf widthLength

def annularFourBeta : FG →L[ℂ] AnnularBoundary :=
  -((annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1).comp
    (annularFourIntoWeak parameters lower length positive lengthPositive widthHalf widthLength))

def annularFourNaturalAmbient : FG →L[ℂ] AnnularFluxAmbient lower length positive :=
  ((annularFourW lower length positive).comp (FG).subtypeL).prod
    (((annularFourF parameters lower length positive lengthPositive widthHalf widthLength).comp (FG).subtypeL).prod
      (((annularAngularDecode lower).comp ((annularFourG lower length positive).comp (FG).subtypeL)).prod
        (((annularFourF2 lower length positive).comp (FG).subtypeL).prod
          (annularFourBeta parameters lower length positive bounded lengthPositive widthHalf widthLength))))

/-- The boundary datum is the actual trace of p on the entire graph.
The genuine weak derivative relation does not depend on that datum. -/
def annularFourNaturalData : FG →L[ℂ]
    annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength :=
  (annularFourNaturalAmbient parameters lower length positive bounded lengthPositive widthHalf widthLength).codRestrict
    (annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength) (by
      intro data
      exact data.property)

theorem annularFourNaturalData_flux (data : FG) :
    annularDataFluxGraph parameters lower length positive lengthPositive widthHalf widthLength
      (annularFourNaturalData parameters lower length positive bounded lengthPositive widthHalf widthLength data) =
    annularDataFluxGraph parameters lower length positive lengthPositive widthHalf widthLength
      (annularFourIntoWeak parameters lower length positive lengthPositive widthHalf widthLength data) := by
  apply Subtype.ext
  rfl

theorem annularFourNaturalData_outer (data : FG) :
    annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1
      (annularFourNaturalData parameters lower length positive bounded lengthPositive widthHalf widthLength data) =
      -((annularFourNaturalData parameters lower length positive bounded lengthPositive widthHalf widthLength data).val.2.2.2.2) := by
  have traceEquality := congrArg (annularFluxTrace lower positive bounded 1)
    (annularFourNaturalData_flux parameters lower length positive bounded lengthPositive widthHalf widthLength data)
  exact traceEquality.trans (neg_neg
    (annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1
      (annularFourIntoWeak parameters lower length positive lengthPositive widthHalf widthLength data))).symm


/-- Any member of the independently defined four-source residual graph
is the same saved inverse for its actual forcing and actual boundary rows. -/
theorem annularFourGraph_energy_unique (data : FG) :
    annularFourW lower length positive data.val =
      annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularFourNaturalData parameters lower length positive bounded lengthPositive widthHalf widthLength data).val.2
        (annularEnergyTrace lower length positive bounded lengthPositive 0 (annularFourW lower length positive data.val)) :=
  annularDataGraph_unique parameters lower length positive bounded lengthPositive widthHalf widthLength
    (annularFourNaturalData parameters lower length positive bounded lengthPositive widthHalf widthLength data) _ rfl
    (annularFourNaturalData_outer parameters lower length positive bounded lengthPositive widthHalf widthLength data)

end Natural
end Grad.AnnularFourSource
