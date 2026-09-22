import AID3ActualSinglePhysicalTests

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity

/-- The original physical test packet at one Fourier mode, for an arbitrary completed flux output. -/
theorem physicalTestPacket_single (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) (field : DivisionRow 3 lower) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength
      (bEnergyNormalize lower L positive (annularEnergyCoreInto lower L positive (Finsupp.single mode core)))) field =
      inner ℂ (weightedCurveComplex 1 lower core.val.2)
        (highPhysicalOutput lower 0 field mode) +
      inner ℂ (collarScalar 1 lower (annularTiltCurve parameters lower positive mode.val.2)
        (weightedCurveComplex 1 lower core.val.1)) (highPhysicalOutput lower 0 field mode) +
      inner ℂ ((Complex.I * (((mode.val.2 : ℝ) / L) : ℝ)) • weightedCurveComplex 1 lower core.val.1)
        (highPhysicalOutput lower 1 field mode) +
      inner ℂ ((Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
        (weightedCurveComplex 1 lower core.val.1)) (highPhysicalOutput lower 2 field mode) := by
  rw [physicalTestPacket_normalized_pairing, inner_add_left, annularEnergyDerivative_single,
    actualTiltPhase_single, actualCell_single, actualAngularRadius_single,
    annularBulk_single_inner, annularBulk_single_inner, annularBulk_single_inner, annularBulk_single_inner]

/-- The completed moment on the right of the genuine second radial equation. -/
def physicalFluxMomentRHS (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (field : DivisionRow 3 lower) (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  collarScalar 1 lower (annularTiltCurve parameters lower positive mode.val.2)
      (annularRadialMoment lower positive (highPhysicalOutput lower 0 field mode)) -
    (Complex.I * (((mode.val.2 : ℝ) / L) : ℝ)) • annularRadialMoment lower positive (highPhysicalOutput lower 1 field mode) -
    (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
      (annularRadialMoment lower positive (highPhysicalOutput lower 2 field mode))

/-- Exact scalar compact-test formula in the original radial measure, before integration by parts. -/
theorem physicalTestPacket_scalar_moment (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (mode : HighAnnularMode) (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (vector : ComplexEuclidean 1) (field : DivisionRow 3 lower) :
    inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength
      (bEnergyNormalize lower L positive (annularScalarTest lower L positive mode profile smooth vector))) field =
      collarPairing lower ⟨deriv profile, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩ vector
        (annularRadialMoment lower positive (highPhysicalOutput lower 0 field mode)) +
      collarPairing lower ⟨profile, smooth.continuous⟩ vector (physicalFluxMomentRHS parameters lower L positive field mode) := by
  rw [annularScalarTest, physicalTestPacket_single, smoothScalarRadialCore_slope_curve,
    smoothScalarRadialCore_value_curve, weightedCurve_test_moment lower positive, weightedCurve_leftScalar_pairing lower positive,
    weightedCurve_skew_pairing lower positive _ (imaginarySymbol_star _)]
  have angular : inner ℂ ((Complex.I * (mode.val.1 : ℂ)) •
      collarScalar 1 lower (highReciprocalRadius lower positive)
        (weightedCurveComplex 1 lower (collarTestCurve ⟨profile, smooth.continuous⟩ vector)))
      (highPhysicalOutput lower 2 field mode) =
    -collarPairing lower ⟨profile, smooth.continuous⟩ vector
      ((Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
        (annularRadialMoment lower positive (highPhysicalOutput lower 2 field mode))) := by
    have starAngular : starRingEnd ℂ (Complex.I * (mode.val.1 : ℂ)) = -(Complex.I * (mode.val.1 : ℂ)) := by simp
    rw [inner_smul_left, starAngular, weightedCurve_leftScalar_pairing lower positive,
      collarPairing_complex_smul]
    ring
  rw [angular]
  simp only [physicalFluxMomentRHS, map_sub]
  ring

end Grad.AnnularCurrentGreen
