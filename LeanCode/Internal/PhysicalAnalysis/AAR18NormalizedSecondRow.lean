import AAR17ActualFluxWeakGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarScalar_inverseSlope_radius (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (annularInverseRadiusSlope lower positive)
      (collarScalar 1 lower annularRadiusCurve field) =
      -collarScalar 1 lower (annularInverseRadiusCurve lower positive) field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (annularInverseRadiusSlope lower positive)
    (collarScalar 1 lower annularRadiusCurve field), collarScalar_ae 1 lower annularRadiusCurve field,
    collarScalar_ae 1 lower (annularInverseRadiusCurve lower positive) field,
    Lp.coeFn_neg (collarScalar 1 lower (annularInverseRadiusCurve lower positive) field),
    ae_restrict_mem measurableSet_Icc] with radius outer inner inverse negative inside
  rw [outer, inner, negative, Pi.neg_apply, inverse, smul_smul, ← neg_smul]
  change (-((1 / max lower radius) * (1 / max lower radius)) * radius) • field radius =
    -(1 / max lower radius) • field radius
  rw [max_eq_right inside.1]
  congr 1
  field_simp

theorem collarScalar_radial_twice (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (annularRadialCurve lower positive) field =
      (2 : ℝ) • collarScalar 1 lower (annularInverseRadiusCurve lower positive) field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (annularRadialCurve lower positive) field,
    collarScalar_ae 1 lower (annularInverseRadiusCurve lower positive) field,
    Lp.coeFn_smul (2 : ℝ) (collarScalar 1 lower (annularInverseRadiusCurve lower positive) field)]
    with radius radial inverse scaled
  rw [radial, scaled, Pi.smul_apply, inverse, smul_smul]
  change (2 / max lower radius) • field radius = (2 * (1 / max lower radius)) • field radius
  congr 1
  ring

theorem annularRadialMoment_inverseSlope (lower : ℝ) (positive : 0 < lower) (field : RadialL2 1 lower) :
    collarScalar 1 lower (annularInverseRadiusSlope lower positive)
      (annularRadialMoment lower positive field) =
      -collarScalar 1 lower (annularInverseRadiusCurve lower positive) (radialOrdinary 1 lower positive field) :=
  collarScalar_inverseSlope_radius lower positive _

theorem annularRadialMoment_divide_scalar (lower : ℝ) (positive : 0 < lower)
    (coefficient : C(ℝ, ℝ)) (field : RadialL2 1 lower) :
    collarScalar 1 lower (annularInverseRadiusCurve lower positive)
      (collarScalar 1 lower coefficient (annularRadialMoment lower positive field)) =
      collarScalar 1 lower coefficient (radialOrdinary 1 lower positive field) := by
  rw [collarScalar_comm lower (annularInverseRadiusCurve lower positive), annularRadialMoment_divide]

theorem annularFlux_algebra {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (inverse phase potential radial : E →L[ℝ] E) (u v f g h : E)
    (commutes : inverse (phase u) = phase (inverse u))
    (radialF : radial f = (2 : ℝ) • inverse f) :
    -inverse (v - phase u + (2 : ℝ) • inverse u - f) +
      (phase (v - phase u) - phase f + potential u - radial f - g - h + inverse ((2 : ℝ) • v)) =
      phase (v - phase u + (2 : ℝ) • inverse u - f) +
      inverse (v - phase u + (2 : ℝ) • inverse u - f) + potential u -
      (4 : ℝ) • inverse (inverse u) - g - h := by
  rw [radialF]
  simp only [map_add, map_sub, map_smul]
  rw [commutes]
  module

section SecondRow
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularPhysicalDerivative_ordinary (bounded : lower ≤ 1)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    radialOrdinary 1 lower positive
      (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode) =
    annularOrdinaryCoordinate lower length positive bounded mode 1 field -
      collarScalar 1 lower (annularPhaseCurve parameters mode.val.2)
        (annularOrdinaryCoordinate lower length positive bounded mode 0 field) := by
  change radialOrdinary 1 lower positive
    (annularEnergyDerivative lower length positive field mode -
      annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field mode) = _
  rw [map_sub, annularEnergyDerivative_ordinary lower length positive bounded mode field,
    annularEnergyPhase_mode, radialOrdinary_collarScalar,
    annularEnergyValue_ordinary lower length positive bounded mode field]

theorem annularRecoveredQ_ordinary (bounded : lower ≤ 1)
    (field : annularEnergySpace lower length positive) (source : AnnularBulk lower) (mode : HighAnnularMode) :
    radialOrdinary 1 lower positive
      (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source mode) =
    annularOrdinaryCoordinate lower length positive bounded mode 1 field -
      collarScalar 1 lower (annularPhaseCurve parameters mode.val.2)
        (annularOrdinaryCoordinate lower length positive bounded mode 0 field) +
      (2 : ℝ) • collarScalar 1 lower (annularInverseRadiusCurve lower positive)
        (annularOrdinaryCoordinate lower length positive bounded mode 0 field) -
      radialOrdinary 1 lower positive (source mode) := by
  let ordinary := radialOrdinary 1 lower positive
  let radial := annularRadialCurve lower positive
  let u := annularOrdinaryCoordinate lower length positive bounded mode 0 field
  have radialPair := (congrArg ordinary (annularEnergyRadial_mode lower length positive mode field)).trans
    ((radialOrdinary_collarScalar lower positive radial (annularEnergyValue lower length positive field mode)).trans
      ((congrArg (collarScalar 1 lower radial)
        (annularEnergyValue_ordinary lower length positive bounded mode field)).trans
        (collarScalar_radial_twice lower positive u)))
  have derivativePair := annularPhysicalDerivative_ordinary parameters lower length positive lengthPositive widthHalf widthLength bounded field mode
  have sumPair := congrArg₂ (fun first second : CollarL2 (ComplexEuclidean 1) lower => first + second)
    derivativePair radialPair
  have differencePair := congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower => value - ordinary (source mode)) sumPair
  change ordinary
    (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode +
      annularEnergyRadial lower length positive field mode - source mode) = _
  exact ((ordinary.map_sub _ _).trans
    (congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower => value - ordinary (source mode))
      (ordinary.map_add _ _))).trans differencePair

theorem annularNormalizedQSlope_formula (bounded : lower ≤ 1)
    (field : annularEnergySpace lower length positive) (source : AnnularForcing lower) (mode : HighAnnularMode) :
    let q := radialOrdinary 1 lower positive
      (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode)
    let u := annularOrdinaryCoordinate lower length positive bounded mode 0 field
    annularNormalizedQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded field source mode =
      collarScalar 1 lower (annularPhaseCurve parameters mode.val.2) q +
      collarScalar 1 lower (annularInverseRadiusCurve lower positive) q +
      collarScalar 1 lower (annularPotentialCurve lower length positive mode) u -
      (4 : ℝ) • collarScalar 1 lower (annularInverseRadiusCurve lower positive)
        (collarScalar 1 lower (annularInverseRadiusCurve lower positive) u) -
      annularDSymbol mode • radialOrdinary 1 lower positive (source.2.1 mode) -
      annularCellSymbol length mode • radialOrdinary 1 lower positive (source.2.2.1 mode) := by
  dsimp only
  unfold annularNormalizedQSlope annularFluxMomentRHS annularUncorrectedFluxMomentRHS annularUncorrectedFluxMoment
  simp only [map_add, map_sub, map_smul]
  rw [annularRadialMoment_inverseSlope]
  simp only [annularRadialMoment_divide_scalar, annularRadialMoment_divide]
  rw [annularEnergyValue_ordinary lower length positive bounded mode field,
    annularPhysicalDerivative_ordinary parameters lower length positive lengthPositive widthHalf widthLength bounded field mode,
    annularRecoveredQ_ordinary parameters lower length positive lengthPositive widthHalf widthLength bounded field source.1 mode]
  exact annularFlux_algebra
    ((collarScalar 1 lower (annularInverseRadiusCurve lower positive)).restrictScalars ℝ)
    ((collarScalar 1 lower (annularPhaseCurve parameters mode.val.2)).restrictScalars ℝ)
    ((collarScalar 1 lower (annularPotentialCurve lower length positive mode)).restrictScalars ℝ)
    ((collarScalar 1 lower (annularRadialCurve lower positive)).restrictScalars ℝ)
    (annularOrdinaryCoordinate lower length positive bounded mode 0 field)
    (annularOrdinaryCoordinate lower length positive bounded mode 1 field)
    (radialOrdinary 1 lower positive (source.1 mode))
    (annularDSymbol mode • radialOrdinary 1 lower positive (source.2.1 mode))
    (annularCellSymbol length mode • radialOrdinary 1 lower positive (source.2.2.1 mode))
    (collarScalar_comm lower (annularInverseRadiusCurve lower positive)
      (annularPhaseCurve parameters mode.val.2)
      (annularOrdinaryCoordinate lower length positive bounded mode 0 field))
    (collarScalar_radial_twice lower positive (radialOrdinary 1 lower positive (source.1 mode)))

end SecondRow
end Grad.AnnularReconstruction
