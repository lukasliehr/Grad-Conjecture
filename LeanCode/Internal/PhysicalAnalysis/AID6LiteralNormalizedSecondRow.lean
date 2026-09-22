import AID5ActualCompactFluxEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity Grad.AnnularSourceGraph

theorem highReciprocalRadius_eq_inverse (lower : ℝ) (positive : 0 < lower) :
    highReciprocalRadius lower positive = annularInverseRadiusCurve lower positive := by
  ext radius
  exact (one_div (max lower radius)).symm

/-- Literal BF14 before omega normalization, with the original s−1/r, cell, and rV signs. -/
theorem physicalFluxOrdinarySlope_literal (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (field : DivisionRow 3 lower) (mode : HighAnnularMode) :
    physicalFluxOrdinarySlope parameters lower L positive field mode =
      collarScalar 1 lower (annularTiltCurve parameters lower positive mode.val.2)
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode)) -
      collarScalar 1 lower (highReciprocalRadius lower positive)
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode)) -
      (Complex.I * (((mode.val.2 : ℝ) / L) : ℝ)) •
        radialOrdinary 1 lower positive (highPhysicalOutput lower 1 field mode) -
      (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
        (radialOrdinary 1 lower positive (highPhysicalOutput lower 2 field mode)) := by
  rw [physicalFluxOrdinarySlope, physicalFluxMomentRHS, annularRadialMoment_inverseSlope]
  simp only [map_sub, map_smul, annularRadialMoment_divide_scalar, annularRadialMoment_divide]
  rw [highReciprocalRadius_eq_inverse]
  abel

/-- The compact physical equation yields the literal normalized second weak row. -/
theorem physicalFlux_second_weak (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field)
    (mode : HighAnnularMode) :
    CollarWeakDerivative lower (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode))
      (collarScalar 1 lower (annularTiltCurve parameters lower positive mode.val.2)
          (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode)) -
        collarScalar 1 lower (highReciprocalRadius lower positive)
          (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode)) -
        (Complex.I * (((mode.val.2 : ℝ) / L) : ℝ)) •
          radialOrdinary 1 lower positive (highPhysicalOutput lower 1 field mode) -
        (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
          (radialOrdinary 1 lower positive (highPhysicalOutput lower 2 field mode))) := by
  have weak := physicalFluxOrdinary_weak parameters lower L positive lengthPositive widthHalf widthLength bounded field equation mode
  rw [physicalFluxOrdinarySlope_literal] at weak
  exact weak

end Grad.AnnularCurrentGreen
