import AAX2OriginalSumAmbient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFourSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Graph
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularFourQ : AnnularFourAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  (annularQFromAngularP lower).comp (annularFourP lower length positive)

/-- f=xi_r+2xi/r+Dp in the original sqrt(r)ePhi coordinates. -/
def annularFourF : AnnularFourAmbient lower length positive →L[ℂ] AnnularBulk lower :=
  ((annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength +
    annularEnergyRadial lower length positive).comp (annularFourW lower length positive)) -
      annularFourQ lower length positive

/-- The fourth source retains its stronger angular norm in the domain;
only the genuine inclusion to the lower bulk is used by the weak equation. -/
def annularFourZeroBetaForcing : AnnularFourAmbient lower length positive →L[ℂ] AnnularForcing lower :=
  (annularFourF parameters lower length positive lengthPositive widthHalf widthLength).prod
    (((annularAngularDecode lower).comp (annularFourG lower length positive)).prod
      ((annularFourF2 lower length positive).prod (0 : AnnularFourAmbient lower length positive →L[ℂ] AnnularBoundary)))

def annularFourWeakData : AnnularFourAmbient lower length positive →L[ℂ] AnnularFluxAmbient lower length positive :=
  (annularFourW lower length positive).prod
    (annularFourZeroBetaForcing parameters lower length positive lengthPositive widthHalf widthLength)

/-- The independently defined literal conormal distribution graph.
Its G coordinate is constrained by the weak equation, not freely chosen. -/
def annularFourGraph : Submodule ℂ (AnnularFourAmbient lower length positive) :=
  (annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength).comap
    (annularFourWeakData parameters lower length positive lengthPositive widthHalf widthLength).toLinearMap

theorem annularFourGraph_closed : IsClosed (annularFourGraph parameters lower length positive lengthPositive widthHalf widthLength :
    Set (AnnularFourAmbient lower length positive)) :=
  (annularFluxDataGraph_closed parameters lower length positive lengthPositive widthHalf widthLength).preimage
    (annularFourWeakData parameters lower length positive lengthPositive widthHalf widthLength).continuous

instance annularFourGraph_complete : CompleteSpace
    (annularFourGraph parameters lower length positive lengthPositive widthHalf widthLength) :=
  (annularFourGraph_closed parameters lower length positive lengthPositive widthHalf widthLength).completeSpace_coe

def annularFourIntoWeak : annularFourGraph parameters lower length positive lengthPositive widthHalf widthLength →L[ℂ]
    annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength :=
  ((annularFourWeakData parameters lower length positive lengthPositive widthHalf widthLength).comp
    (annularFourGraph parameters lower length positive lengthPositive widthHalf widthLength).subtypeL).codRestrict
      (annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength) (fun data => data.property)

theorem annularFour_recoveredQ (data : AnnularFourAmbient lower length positive) :
    annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength
      (annularFourW lower length positive data)
      (annularFourF parameters lower length positive lengthPositive widthHalf widthLength data) =
      annularFourQ lower length positive data := by
  change (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength
    (annularFourW lower length positive data)) +
    annularEnergyRadial lower length positive (annularFourW lower length positive data) -
    ((annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength
      (annularFourW lower length positive data)) +
      annularEnergyRadial lower length positive (annularFourW lower length positive data) -
      annularFourQ lower length positive data) = annularFourQ lower length positive data
  abel

theorem annularFour_recoveredAngularP (data : AnnularFourAmbient lower length positive) :
    annularRecoveredAngularP parameters lower length positive lengthPositive widthHalf widthLength
      (annularFourW lower length positive data)
      (annularFourF parameters lower length positive lengthPositive widthHalf widthLength data) =
      annularFourP lower length positive data := by
  unfold annularRecoveredAngularP
  rw [annularFour_recoveredQ]
  exact annularQFromAngularP_left lower _

end Graph
end Grad.AnnularFourSource
