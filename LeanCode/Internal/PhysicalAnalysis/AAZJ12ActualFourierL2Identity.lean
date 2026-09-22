import AAZJ11ExactDoubleFourierCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularRadialJets Grad.AnnularRegularity

section ActualIdentity
variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))
    (grades : ∀ order grade, HasAnnularRawGrade lower grade (jet order))
include grades

theorem annularPhysicalJet_point_coefficients_summable (radial angular cell : ℕ)
    (radius : Icc lower (1 : ℝ)) :
    Summable (fun mode => ‖annularMixedSymbol angular cell mode •
      annularPhysicalJetSection parameters lower positive bounded jet weak radial mode radius‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun mode => ?_)
    (annularPhysicalJetSection_weighted_summable parameters lower positive bounded jet weak radial (angular + cell)
      (grades radial (angular + cell + 2)) (grades (radial + 1) (angular + cell + 2)))
  rw [norm_smul]
  exact mul_le_mul (annularMixedSymbol_norm_le angular cell mode)
    (ContinuousMap.norm_coe_le_norm _ radius) (norm_nonneg _) (pow_nonneg (zero_le_one.trans (annularRawFrequency_one_le mode)) _)

theorem annularMixedFourierSection_characterSeries (radial angular cell : ℕ)
    (radius : Icc lower (1 : ℝ)) (angles : ℝ × ℝ) :
    annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell angles radius =
      annularCharacterSeries (fun mode => annularMixedSymbol angular cell mode •
        annularPhysicalJetSection parameters lower positive bounded jet weak radial mode radius) angles := by
  rw [annularMixedFourierSection_apply parameters lower positive bounded jet weak grades]
  apply tsum_congr
  intro mode
  simp only [annularFourierCoefficient, mul_smul]

/-- Every mixed reconstructed derivative has its literal double Fourier
coefficient, including at both closed radial endpoints. -/
theorem annularMixedFourierSection_coefficient (radial angular cell : ℕ)
    (radius : Icc lower (1 : ℝ)) (query : HighAnnularMode) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell (polar, axial) radius)
      query.val.1) query.val.2 =
      annularMixedSymbol angular cell query •
        annularPhysicalJetSection parameters lower positive bounded jet weak radial query radius := by
  simp_rw [annularMixedFourierSection_characterSeries parameters lower positive bounded jet weak grades]
  exact annularCharacterSeries_coefficient _
    (annularPhysicalJet_point_coefficients_summable parameters lower positive bounded jet weak grades radial angular cell radius) query

/-- The coefficient is defined by the two actual integrals of the reconstructed
field, as a continuous radial section. -/
def annularReconstructedCoefficientSection (radial : ℕ) (query : HighAnnularMode) :
    RadialContinuousSection 1 lower where
  toFun radius := angularCoefficient (fun axial => angularCoefficient
    (fun polar => annularMixedFourierSection parameters lower positive bounded jet weak radial 0 0 (polar, axial) radius)
    query.val.1) query.val.2
  continuous_toFun := by
    have same : (fun radius : Icc lower (1 : ℝ) => angularCoefficient (fun axial => angularCoefficient
        (fun polar => annularMixedFourierSection parameters lower positive bounded jet weak radial 0 0 (polar, axial) radius)
        query.val.1) query.val.2) =
        (annularPhysicalJetSection parameters lower positive bounded jet weak radial query) := by
      funext radius
      simpa only [annularMixedSymbol, pow_zero, one_mul, one_smul] using
        annularMixedFourierSection_coefficient parameters lower positive bounded jet weak grades radial 0 0 radius query
    rw [same]
    exact (annularPhysicalJetSection parameters lower positive bounded jet weak radial query).continuous

theorem annularReconstructedCoefficientSection_eq (radial : ℕ) (query : HighAnnularMode) :
    annularReconstructedCoefficientSection parameters lower positive bounded jet weak grades radial query =
      annularPhysicalJetSection parameters lower positive bounded jet weak radial query := by
  apply ContinuousMap.ext
  intro radius
  exact (by simpa only [annularReconstructedCoefficientSection, ContinuousMap.coe_mk,
      annularMixedSymbol, pow_zero, one_mul, one_smul] using
    annularMixedFourierSection_coefficient parameters lower positive bounded jet weak grades radial 0 0 radius query)

/-- Exact L² fidelity: the actual Fourier integrals of the smooth field recover
precisely the original phase-decoded physical jet, not an independent field. -/
theorem annularReconstructedCoefficientSection_bulk (radial : ℕ) (query : HighAnnularMode) :
    radialSectionL2 1 lower positive bounded.le
      (annularReconstructedCoefficientSection parameters lower positive bounded jet weak grades radial query) =
      annularDecodeMode parameters lower positive query (jet radial query) := by
  rw [annularReconstructedCoefficientSection_eq]
  exact annularPhysicalJetSection_bulk parameters lower positive bounded jet weak radial query

end ActualIdentity
end Grad.AnnularJointRegularity
