import AAV5FullVariationalConverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarScalar_radius_inverse (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower annularRadiusCurve
      (collarScalar 1 lower (annularInverseRadiusCurve lower positive) field) = field :=
  (collarScalar_comm lower _ _ field).trans (collarScalar_inverseRadius_radius lower positive field)

theorem collarScalar_radius_inverseSlope (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower annularRadiusCurve
      (collarScalar 1 lower (annularInverseRadiusSlope lower positive) field) =
      -collarScalar 1 lower (annularInverseRadiusCurve lower positive) field :=
  (collarScalar_comm lower _ _ field).trans (collarScalar_inverseSlope_radius lower positive field)

section Converse
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularNormalizedQSlope_moment (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode) :
    radialOrdinary 1 lower positive
      (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode) +
    collarScalar 1 lower annularRadiusCurve
      (annularNormalizedQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode) =
      annularFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode := by
  unfold annularNormalizedQSlope
  rw [map_add, collarScalar_radius_inverseSlope, collarScalar_radius_inverse,
    annularRadialMoment_divide]
  abel

/-- The literal weak Q graph implies the actual uncorrected conormal
graph, without differentiating the L2 forcing. -/
theorem annularFluxGraph_uncorrected_weak (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode)
    (weak : CollarWeakDerivative lower
      (radialOrdinary 1 lower positive
        (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode))
      (annularNormalizedQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode)) :
    CompactWeakDerivative 1 lower
      (annularUncorrectedFluxMoment parameters lower length positive lengthPositive widthHalf widthLength field source mode)
      (annularUncorrectedFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength field source mode) := by
  have product := collarWeakDerivative_radius lower _ _ weak
  rw [annularNormalizedQSlope_moment parameters lower length positive bounded lengthPositive widthHalf widthLength] at product
  have whole := collarWeak_isCompact 1 lower _ _ product
  have valueWeak := collarWeak_isCompact 1 lower _ _
    (annularModeRadialH1_weak lower length positive bounded.le mode field)
  intro profile smooth compact supported vector
  have wholeLaw := whole profile smooth compact supported vector
  have valueLaw := valueWeak profile smooth compact supported vector
  change collarPairing lower _ vector
    (annularFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode) =
      -collarPairing lower _ vector
        (annularRadialMoment lower positive
          (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode)) at wholeLaw
  rw [annularRecoveredQ_moment parameters lower length positive lengthPositive widthHalf widthLength bounded.le] at wholeLaw
  simp only [annularFluxMomentRHS, map_add, map_smul] at wholeLaw
  change collarPairing lower _ vector
      (annularUncorrectedFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength field source mode) +
      (2 : ℂ) * collarPairing lower _ vector (annularOrdinaryCoordinate lower length positive bounded.le mode 1 field) =
    -(collarPairing lower _ vector
      (annularUncorrectedFluxMoment parameters lower length positive lengthPositive widthHalf widthLength field source mode) +
      (2 : ℂ) * collarPairing lower _ vector (annularOrdinaryCoordinate lower length positive bounded.le mode 0 field)) at wholeLaw
  change collarPairing lower _ vector (annularOrdinaryCoordinate lower length positive bounded.le mode 1 field) =
    -collarPairing lower _ vector (annularOrdinaryCoordinate lower length positive bounded.le mode 0 field) at valueLaw
  change collarPairing lower _ vector
      (annularUncorrectedFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength field source mode) = _
  linear_combination wholeLaw - 2 * valueLaw

end Converse
end Grad.AnnularConverse
