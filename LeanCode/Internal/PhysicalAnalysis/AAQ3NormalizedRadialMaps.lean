import AAQ2NormalizedCoefficientBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularScalarFamily (lower : ℝ) (coefficient : HighAnnularMode → C(ℝ, ℝ))
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ constant) :
    AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  complexLpTwoMap (fun mode => scalarRadialMap lower (coefficient mode) constant (bounded mode))
    constant nonnegative (fun mode => scalarRadialMap_bound lower (coefficient mode) constant (bounded mode))

theorem annularScalarFamily_bound (lower : ℝ) (coefficient : HighAnnularMode → C(ℝ, ℝ))
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ constant)
    (field : AnnularBulk lower) :
    ‖annularScalarFamily lower coefficient constant nonnegative bounded field‖ ≤ constant * ‖field‖ :=
  complexLpTwoMap_bound _ _ _ _ field

theorem scalarRadialMap_eq_collarScalar (lower : ℝ) (coefficient : C(ℝ, ℝ))
    (constant : ℝ) (bounded : ∀ radius, radius ∈ Icc lower 1 → |coefficient radius| ≤ constant)
    (field : RadialL2 1 lower) :
    scalarRadialMap lower coefficient constant bounded field = collarScalar 1 lower coefficient field := by
  apply Lp.ext
  filter_upwards [scalarRadialMap_ae lower coefficient constant bounded field,
    collarScalar_ae 1 lower coefficient field] with radius first second
  exact first.trans second.symm

theorem collarScalar_frequency (lower : ℝ) (mode : HighAnnularMode) (coefficient : C(ℝ, ℝ))
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (annularFrequencyCurve mode coefficient) field =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ : ℝ) •
        collarScalar 1 lower coefficient field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (annularFrequencyCurve mode coefficient) field,
    collarScalar_ae 1 lower coefficient field,
    Lp.coeFn_smul ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ : ℝ)
      (collarScalar 1 lower coefficient field)] with radius scaled plain literal
  rw [scaled, literal, Pi.smul_apply, plain, smul_smul]
  rfl

theorem annularScalarFamily_ordinary (lower : ℝ) (positive : 0 < lower)
    (coefficient : HighAnnularMode → C(ℝ, ℝ)) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ constant)
    (field : AnnularBulk lower) (mode : HighAnnularMode) :
    radialOrdinary 1 lower positive (annularScalarFamily lower coefficient constant nonnegative bounded field mode) =
      collarScalar 1 lower (coefficient mode) (radialOrdinary 1 lower positive (field mode)) := by
  change radialOrdinary 1 lower positive (scalarRadialMap lower (coefficient mode) constant (bounded mode) (field mode)) = _
  rw [scalarRadialMap_eq_collarScalar, radialOrdinary_collarScalar]

def annularSymbolFamily (lower : ℝ) (symbol : HighAnnularMode → ℂ) (constant : ℝ)
    (nonnegative : 0 ≤ constant) (bounded : ∀ mode, ‖symbol mode‖ ≤ constant) :
    AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  complexLpTwoMap (fun mode => symbol mode • ContinuousLinearMap.id ℂ (RadialL2 1 lower))
    constant nonnegative (fun mode field => by
      change ‖symbol mode • field‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (bounded mode) (norm_nonneg field))

theorem annularSymbolFamily_bound (lower : ℝ) (symbol : HighAnnularMode → ℂ) (constant : ℝ)
    (nonnegative : 0 ≤ constant) (bounded : ∀ mode, ‖symbol mode‖ ≤ constant) (field : AnnularBulk lower) :
    ‖annularSymbolFamily lower symbol constant nonnegative bounded field‖ ≤ constant * ‖field‖ :=
  complexLpTwoMap_bound _ _ _ _ field

def annularNormalizedPotentialMap (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (annularScalarFamily lower
    (fun mode => annularFrequencyCurve mode (annularPotentialWeight lower length positive mode.val.1 mode.val.2))
    (annularFluxPotentialConstant lower length) (annularFluxPotentialConstant_nonnegative lower length)
    (annularNormalizedPotential_bound lower length positive)).comp (annularEnergyMass lower length positive)

theorem annularNormalizedPotentialMap_bound (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    ‖annularNormalizedPotentialMap lower length positive field‖ ≤ annularFluxPotentialConstant lower length * ‖field‖ :=
  (annularScalarFamily_bound lower
    (fun mode => annularFrequencyCurve mode (annularPotentialWeight lower length positive mode.val.1 mode.val.2))
    (annularFluxPotentialConstant lower length) (annularFluxPotentialConstant_nonnegative lower length)
    (annularNormalizedPotential_bound lower length positive) (annularEnergyMass lower length positive field)).trans
    (mul_le_mul_of_nonneg_left (annularEnergyMass_bound lower length positive field)
      (annularFluxPotentialConstant_nonnegative lower length))

theorem annularNormalizedPotentialMap_ordinary (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    radialOrdinary 1 lower positive (annularNormalizedPotentialMap lower length positive field mode) =
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ : ℝ) •
        collarScalar 1 lower (annularPotentialCurve lower length positive mode)
          (annularOrdinaryCoordinate lower length positive bounded mode 0 field) := by
  change radialOrdinary 1 lower positive (annularScalarFamily lower
    (fun mode => annularFrequencyCurve mode (annularPotentialWeight lower length positive mode.val.1 mode.val.2))
    (annularFluxPotentialConstant lower length) (annularFluxPotentialConstant_nonnegative lower length)
    (annularNormalizedPotential_bound lower length positive)
    (annularEnergyMass lower length positive field) mode) = _
  rw [annularScalarFamily_ordinary, collarScalar_frequency, annularEnergyMass_mode,
    radialOrdinary_collarScalar, collarScalar_mul_apply, annularEnergyValue_ordinary]
  rfl

theorem collarScalar_inverseSquare (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (annularInverseSquareCurve lower positive) field =
      (4 : ℝ) • collarScalar 1 lower (annularInverseRadiusCurve lower positive)
        (collarScalar 1 lower (annularInverseRadiusCurve lower positive) field) := by
  rw [collarScalar_mul_apply]
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (annularInverseSquareCurve lower positive) field,
    collarScalar_ae 1 lower (annularInverseRadiusCurve lower positive * annularInverseRadiusCurve lower positive) field,
    Lp.coeFn_smul (4 : ℝ) (collarScalar 1 lower
      (annularInverseRadiusCurve lower positive * annularInverseRadiusCurve lower positive) field)]
    with radius scaled plain literal
  rw [scaled, literal, Pi.smul_apply, plain, smul_smul]
  rfl

end Grad.AnnularFluxTrace
