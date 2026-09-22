import AIQ2ActualPhysicalCandidateUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularPhysicalSolution
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentGreen Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularReconstruction Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra

theorem collarScalar_radius_inverseRadius (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower annularRadiusCurve
      (collarScalar 1 lower (annularInverseRadiusCurve lower positive) field) = field := by
  rw [collarScalar_comm, collarScalar_inverseRadius_radius]

theorem physicalFluxOrdinarySlope_radius (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (field : DivisionRow 3 lower) (mode : HighAnnularMode) :
    radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode) +
      collarScalar 1 lower annularRadiusCurve (physicalFluxOrdinarySlope parameters lower L positive field mode) =
      physicalFluxMomentRHS parameters lower L positive field mode := by
  rw [physicalFluxOrdinarySlope, annularRadialMoment_inverseSlope, map_add, map_neg,
    collarScalar_radius_inverseRadius, collarScalar_radius_inverseRadius]
  abel

/-- The literal ordinary weak second row recovers compact physical testing, with the original rdr weight. -/
theorem compactPhysicalPacketEquation_of_ordinaryWeak (parameters : PhaseParameters) (lower L : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (field : DivisionRow 3 lower)
    (weak : ∀ mode : HighAnnularMode,
      CollarWeakDerivative lower (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode))
        (physicalFluxOrdinarySlope parameters lower L positive field mode)) :
    CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field := by
  intro mode profile smooth compact supported vector
  have moment := collarWeakDerivative_radius lower _ _ (weak mode)
  rw [physicalFluxOrdinarySlope_radius] at moment
  have compactMoment := (compactWeak_iff_collarWeak 1 lower positive bounded _ _).mpr moment
  have law := compactMoment profile smooth compact supported vector
  rw [physicalTestPacket_scalar_moment]
  change collarPairing lower ⟨profile, smooth.continuous⟩ vector (physicalFluxMomentRHS parameters lower L positive field mode) =
    -collarPairing lower ⟨deriv profile, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩ vector
      (annularRadialMoment lower positive (highPhysicalOutput lower 0 field mode)) at law
  linear_combination law

/-- Exact ordinary distributional row equivalence, without an assumed missing regularity statement. -/
theorem compactPhysicalPacketEquation_iff_ordinaryWeak (parameters : PhaseParameters) (lower L : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (field : DivisionRow 3 lower) :
    CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field ↔
    ∀ mode : HighAnnularMode,
      CollarWeakDerivative lower (radialOrdinary 1 lower positive (highPhysicalOutput lower 0 field mode))
        (physicalFluxOrdinarySlope parameters lower L positive field mode) := by
  constructor
  · intro equation mode
    exact physicalFluxOrdinary_weak parameters lower L positive lengthPositive widthHalf widthLength bounded field equation mode
  · exact compactPhysicalPacketEquation_of_ordinaryWeak parameters lower L positive bounded lengthPositive widthHalf widthLength field

end Grad.AnnularPhysicalSolution
