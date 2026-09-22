import AID11ActualCompactTestConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity Grad.AnnularSourceGraph
open Grad.AnnularConverse

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

theorem physicalTestPacket_vector_moment (mode : HighAnnularMode) (core : complexSmoothRadialCore 1)
    (field : DivisionRow 3 lower) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength
      (bEnergyNormalize lower L positive (annularEnergyCoreInto lower L positive (Finsupp.single mode core)))) field =
      vectorCollarPairing lower core.val.2 (annularRadialMoment lower positive (highPhysicalOutput lower 0 field mode)) +
      vectorCollarPairing lower core.val.1 (physicalFluxMomentRHS parameters lower L positive field mode) := by
  rw [physicalTestPacket_single, weightedCurve_vector_moment lower positive,
    weightedCurve_vector_scalar lower positive,
    weightedCurve_vector_skew lower positive _ (imaginarySymbol_star _)]
  have angular : inner ℂ ((Complex.I * (mode.val.1 : ℂ)) •
      collarScalar 1 lower (highReciprocalRadius lower positive) (weightedCurveComplex 1 lower core.val.1))
      (highPhysicalOutput lower 2 field mode) =
    -vectorCollarPairing lower core.val.1 ((Complex.I * (mode.val.1 : ℂ)) •
      collarScalar 1 lower (highReciprocalRadius lower positive)
        (annularRadialMoment lower positive (highPhysicalOutput lower 2 field mode))) := by
    have starAngular : starRingEnd ℂ (Complex.I * (mode.val.1 : ℂ)) = -(Complex.I * (mode.val.1 : ℂ)) := by simp
    rw [inner_smul_left, starAngular, weightedCurve_vector_scalar lower positive, map_smul]
    change -(Complex.I * (mode.val.1 : ℂ)) * _ = -((Complex.I * (mode.val.1 : ℂ)) * _)
    ring
  rw [angular]
  simp only [physicalFluxMomentRHS, map_sub]
  ring

/-- Actual genuine radial graph of r times the recovered flux, supplied by compact physical testing. -/
def physicalFluxMomentGraph (bounded : lower < 1) (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field)
    (mode : HighAnnularMode) : WeightedRadialH1 1 lower :=
  compactWeakRadialGraph lower positive bounded
    (annularRadialMoment lower positive (highPhysicalOutput lower 0 field mode))
    (physicalFluxMomentRHS parameters lower L positive field mode)
    (physicalFluxMoment_compactWeak parameters lower L positive lengthPositive widthHalf widthLength field equation mode)

theorem physicalFluxMomentGraph_value (bounded : lower < 1) (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field)
    (mode : HighAnnularMode) :
    collarH1Coordinate (ComplexEuclidean 1) lower 0
      (weightedToOrdinary 1 lower positive bounded.le
        (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength bounded field equation mode)) =
      annularRadialMoment lower positive (highPhysicalOutput lower 0 field mode) :=
  compactWeakRadialGraph_value lower positive bounded _ _ _

theorem physicalFluxMomentGraph_slope (bounded : lower < 1) (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field)
    (mode : HighAnnularMode) :
    collarH1Coordinate (ComplexEuclidean 1) lower 1
      (weightedToOrdinary 1 lower positive bounded.le
        (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength bounded field equation mode)) =
      physicalFluxMomentRHS parameters lower L positive field mode :=
  compactWeakRadialGraph_slope lower positive bounded _ _ _

/-- Green identity for the actual physical packet, retaining both genuine endpoint traces. -/
theorem physicalFlux_packet_green (bounded : lower < 1) (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field)
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength
      (bEnergyNormalize lower L positive (annularEnergyCoreInto lower L positive (Finsupp.single mode core)))) field =
      inner ℂ (core.val.1 1) (weightedRadialTrace 1 lower positive bounded 1
        (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength bounded field equation mode)) -
      inner ℂ (core.val.1 lower) (weightedRadialTrace 1 lower positive bounded 0
        (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength bounded field equation mode)) := by
  rw [physicalTestPacket_vector_moment]
  have parts := weightedRadial_vector_parts 1 lower positive bounded
    (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength bounded field equation mode) core
  rw [physicalFluxMomentGraph_value, physicalFluxMomentGraph_slope] at parts
  exact parts

end Grad.AnnularCurrentGreen
