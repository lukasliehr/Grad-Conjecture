import AEE5ActualLowReferenceDataOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- An actual radial graph element placed in one original low coordinate. -/
def lowSingleRadialGraph (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (index : LowAnnularIndex) : WeightedRadialH1 1 lower →L[ℝ] lowEnergyGraph lower length positive :=
  (lowModeCoordinates lower length positive bounded index).codRestrict
    ((lowEnergyGraph lower length positive).restrictScalars ℝ)
    (lowModeCoordinates_mem lower length positive bounded index)

theorem lowSingleRadialGraph_value (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (index other : LowAnnularIndex) (radial : WeightedRadialH1 1 lower) :
    lowEnergyValue lower positive other (lowSingleRadialGraph lower length positive bounded index radial).val =
      if other = index then collarH1Coordinate (ComplexEuclidean 1) lower 0
        (weightedToOrdinary 1 lower positive bounded.le radial) else 0 := by
  change collarScalar 1 lower (lowStorageInverse lower positive)
    ((lp.single 2 index (lowModeEncodedValue lower positive bounded radial) : LowEnergyBulk lower) other) = _
  split_ifs with same
  · subst other
    simp only [lp.single_apply, Pi.single_eq_same]
    exact lowStorage_decode_encode lower positive _
  · simp only [lp.single_apply, Pi.single_eq_of_ne same, map_zero]

theorem lowSingleRadialGraph_derivative (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (index other : LowAnnularIndex) (radial : WeightedRadialH1 1 lower) :
    lowEnergyDerivative lower length positive other (lowSingleRadialGraph lower length positive bounded index radial).val =
      if other = index then collarH1Coordinate (ComplexEuclidean 1) lower 1
        (weightedToOrdinary 1 lower positive bounded.le radial) else 0 := by
  change collarScalar 1 lower (lowMuCurve lower length positive other.2.val.2)
    (collarScalar 1 lower (lowStorageInverse lower positive)
      ((lp.single 2 index (lowModeEncodedSlope lower length positive bounded index radial) : LowEnergyBulk lower) other)) = _
  split_ifs with same
  · subst other
    simp only [lp.single_apply, Pi.single_eq_same]
    change collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)
      (collarScalar 1 lower (lowStorageInverse lower positive)
        (collarScalar 1 lower (lowStorageWeight lower positive)
          (collarScalar 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
            (collarH1Coordinate (ComplexEuclidean 1) lower 1 (weightedToOrdinary 1 lower positive bounded.le radial))))) = _
    rw [lowStorage_decode_encode, lowMu_decode_encode]
  · simp only [lp.single_apply, Pi.single_eq_of_ne same, map_zero]

theorem lowSingleRadialGraph_section (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (index other : LowAnnularIndex) (radial : WeightedRadialH1 1 lower) :
    lowEnergySection lower length positive bounded (lowSingleRadialGraph lower length positive bounded index radial) other =
      if other = index then weightedRadialSection 1 lower positive bounded radial else 0 := by
  apply radialSectionL2_injective lower positive bounded
  rw [lowEnergySection_bulk, lowSingleRadialGraph_value]
  split_ifs with same
  · exact (weightedRadialSection_bulk 1 lower positive bounded radial).symm
  · exact (map_zero (radialSectionL2 1 lower positive bounded.le)).symm

theorem lowSingleRadialGraph_incoming (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (index other : LowAnnularIndex) (radial : WeightedRadialH1 1 lower) :
    lowIncomingTrace lower length positive bounded (lowSingleRadialGraph lower length positive bounded index radial) other =
      if other = index then
        (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower index.2.val.2))⁻¹) •
          weightedRadialTrace 1 lower positive bounded 0 radial else 0 := by
  rw [lowIncomingTrace_apply]
  unfold lowEnergyEndpoint
  rw [lowSingleRadialGraph_section]
  split_ifs with same
  · subst other
    rw [weightedRadialSection_endpoint]
  · change _ • (0 : ComplexEuclidean 1) = 0
    exact smul_zero _

end Grad.AnnularLowCompletion
