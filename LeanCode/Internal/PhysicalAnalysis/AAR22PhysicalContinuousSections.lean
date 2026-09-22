import AAR20ActualMomentGraph
import AAR17ActualFluxWeakGraph
import ASG34SectionBulkIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

def radialSectionScalar (lower : ℝ) (coefficient : C(ℝ, ℝ))
    (sectionValue : RadialContinuousSection 1 lower) : RadialContinuousSection 1 lower :=
  ⟨fun radius => coefficient radius.val • sectionValue radius,
    (coefficient.continuous.comp continuous_subtype_val).smul sectionValue.continuous⟩

theorem radialSectionL2_scalar (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (coefficient : C(ℝ, ℝ)) (sectionValue : RadialContinuousSection 1 lower) :
    radialSectionL2 1 lower positive bounded (radialSectionScalar lower coefficient sectionValue) =
      collarScalar 1 lower coefficient (radialSectionL2 1 lower positive bounded sectionValue) := by
  apply Lp.ext
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (collarContinuous_memLp (ComplexEuclidean 1) lower
      (radialSectionExtension 1 lower bounded (radialSectionScalar lower coefficient sectionValue))).coeFn_toLp,
    (collarContinuous_memLp (ComplexEuclidean 1) lower
      (radialSectionExtension 1 lower bounded sectionValue)).coeFn_toLp,
    collarScalar_ae 1 lower coefficient (radialSectionL2 1 lower positive bounded sectionValue)]
    with radius inside product base multiplied
  change radialSectionL2 1 lower positive bounded (radialSectionScalar lower coefficient sectionValue) radius = _ at product
  change radialSectionL2 1 lower positive bounded sectionValue radius = _ at base
  rw [product, multiplied, base]
  change coefficient (radialClamp lower bounded radius).val • sectionValue (radialClamp lower bounded radius) =
    coefficient radius • sectionValue (radialClamp lower bounded radius)
  rw [radialClamp_eq lower bounded radius inside]

theorem radialSectionL2_complex_smul (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (scalar : ℂ) (sectionValue : RadialContinuousSection 1 lower) :
    radialSectionL2 1 lower positive bounded (scalar • sectionValue) =
      scalar • radialSectionL2 1 lower positive bounded sectionValue := by
  apply Lp.ext
  filter_upwards [
    (collarContinuous_memLp (ComplexEuclidean 1) lower
      (radialSectionExtension 1 lower bounded (scalar • sectionValue))).coeFn_toLp,
    (collarContinuous_memLp (ComplexEuclidean 1) lower
      (radialSectionExtension 1 lower bounded sectionValue)).coeFn_toLp,
    Lp.coeFn_smul scalar (radialSectionL2 1 lower positive bounded sectionValue)]
    with radius scaled base literal
  change radialSectionL2 1 lower positive bounded (scalar • sectionValue) radius = _ at scaled
  change radialSectionL2 1 lower positive bounded sectionValue radius = _ at base
  rw [scaled, literal, Pi.smul_apply, base]
  rfl

section Physical
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularPhysicalQSection (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) : RadialContinuousSection 1 lower :=
  radialSectionScalar lower (annularInversePhase parameters mode.val.2)
    (radialSectionScalar lower (annularInverseRadiusCurve lower positive)
      (weightedRadialSection 1 lower positive bounded
        (annularQMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)))

def annularPhysicalPSection (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) : RadialContinuousSection 1 lower :=
  (-(annularDSymbol mode)⁻¹) •
    annularPhysicalQSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode

/-- This actual continuous representative is the recovered physical q in
ordinary L2; hence its endpoint is a genuine trace of that weak solution. -/
theorem annularPhysicalQSection_bulk (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) :
    radialSectionL2 1 lower positive bounded.le
      (annularPhysicalQSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode) =
      annularPhysicalQ parameters lower length positive lengthPositive widthHalf widthLength
        (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)
        source.1 mode := by
  unfold annularPhysicalQSection
  rw [radialSectionL2_scalar, radialSectionL2_scalar, weightedRadialSection_bulk,
    annularQMomentGraph_value, annularRadialMoment_divide]
  rfl

theorem annularPhysicalPSection_bulk (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) :
    radialSectionL2 1 lower positive bounded.le
      (annularPhysicalPSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode) =
      annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength
        (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)
        source.1 mode := by
  unfold annularPhysicalPSection
  rw [radialSectionL2_complex_smul, annularPhysicalQSection_bulk,
    annularPhysicalP_eq_Q]

end Physical
end Grad.AnnularReconstruction
