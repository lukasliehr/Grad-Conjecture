import AAR7NormalizedCoordinateLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem inversePhaseSlope_cancellation (parameters : PhaseParameters) (lower : ℝ) (cell : ℤ)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (annularInversePhaseSlope parameters cell) field =
      -(collarScalar 1 lower (annularInversePhase parameters cell)
        (collarScalar 1 lower (annularPhaseCurve parameters cell) field)) := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (annularInversePhaseSlope parameters cell) field,
    collarScalar_ae 1 lower (annularInversePhase parameters cell)
      (collarScalar 1 lower (annularPhaseCurve parameters cell) field),
    collarScalar_ae 1 lower (annularPhaseCurve parameters cell) field,
    Lp.coeFn_neg (collarScalar 1 lower (annularInversePhase parameters cell)
      (collarScalar 1 lower (annularPhaseCurve parameters cell) field))]
    with radius slope exponential phase negative
  rw [slope, negative, Pi.neg_apply, exponential, phase]
  change (-annularPhaseSlope parameters cell radius * annularInversePhase parameters cell radius) • field radius =
    -(annularInversePhase parameters cell radius • (annularPhaseSlope parameters cell radius • field radius))
  rw [neg_mul, neg_smul, mul_smul]
  exact congrArg Neg.neg (smul_comm (annularPhaseSlope parameters cell radius)
    (annularInversePhase parameters cell radius) (field radius))

theorem annularPhysicalSlope_eq_decode (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    annularPhysicalSlope parameters lower length positive bounded mode field =
      annularDecodeMode parameters lower positive mode
        (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode) := by
  change collarScalar 1 lower (annularInversePhaseSlope parameters mode.val.2)
      (annularOrdinaryCoordinate lower length positive bounded mode 0 field) +
    collarScalar 1 lower (annularInversePhase parameters mode.val.2)
      (annularOrdinaryCoordinate lower length positive bounded mode 1 field) =
    collarScalar 1 lower (annularInversePhase parameters mode.val.2)
      (radialOrdinary 1 lower positive
        (annularEnergyDerivative lower length positive field mode -
          annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field mode))
  rw [map_sub, annularEnergyDerivative_ordinary lower length positive bounded mode field,
    annularEnergyPhase_mode, radialOrdinary_collarScalar,
    annularEnergyValue_ordinary lower length positive bounded mode field, map_sub,
    inversePhaseSlope_cancellation]
  abel

theorem annularDecode_radial (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (mode : HighAnnularMode)
    (field : annularEnergySpace lower length positive) :
    annularDecodeMode parameters lower positive mode (annularEnergyRadial lower length positive field mode) =
      collarScalar 1 lower (annularRadialCurve lower positive)
        (annularPhysicalValue parameters lower length positive bounded mode field) := by
  change collarScalar 1 lower (annularInversePhase parameters mode.val.2)
      (radialOrdinary 1 lower positive (annularEnergyRadial lower length positive field mode)) =
    collarScalar 1 lower (annularRadialCurve lower positive)
      (collarScalar 1 lower (annularInversePhase parameters mode.val.2)
        (annularOrdinaryCoordinate lower length positive bounded mode 0 field))
  rw [annularEnergyRadial_mode, radialOrdinary_collarScalar,
    annularEnergyValue_ordinary lower length positive bounded mode field]
  exact collarScalar_comm lower _ _ _

section Physical
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularPhysicalP (field : annularEnergySpace lower length positive)
    (source : AnnularBulk lower) (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  annularDecodeMode parameters lower positive mode
    (annularRecoveredP parameters lower length positive lengthPositive widthHalf widthLength field source mode)

def annularPhysicalQ (field : annularEnergySpace lower length positive)
    (source : AnnularBulk lower) (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  annularDecodeMode parameters lower positive mode
    (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source mode)

theorem annularPhysicalP_D (field : annularEnergySpace lower length positive)
    (source : AnnularBulk lower) (mode : HighAnnularMode) :
    annularDSymbol mode • annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source mode =
      -annularPhysicalQ parameters lower length positive lengthPositive widthHalf widthLength field source mode := by
  have law := congrArg (annularDecodeMode parameters lower positive mode)
    (annularPMap_D lower
      (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source) mode)
  rw [map_smul, map_neg] at law
  exact law

/-- The original first row xi_r+2xi/r+D p=f in ordinary radial L2, with
xi_r already proved to be the genuine weak derivative. -/
theorem annularPhysical_first_row (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive)
    (source : AnnularBulk lower) (mode : HighAnnularMode) :
    annularPhysicalSlope parameters lower length positive bounded mode field +
      collarScalar 1 lower (annularRadialCurve lower positive)
        (annularPhysicalValue parameters lower length positive bounded mode field) +
      annularDSymbol mode •
        annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source mode =
      annularDecodeMode parameters lower positive mode (source mode) := by
  have law := congrArg (annularDecodeMode parameters lower positive mode)
    (annularRecovered_first_row parameters lower length positive lengthPositive widthHalf widthLength field source mode)
  rw [map_add, map_add, map_smul,
    ← annularPhysicalSlope_eq_decode parameters lower length positive bounded lengthPositive widthHalf widthLength mode field,
    annularDecode_radial parameters lower length positive bounded mode field] at law
  exact law

end Physical
end Grad.AnnularReconstruction
