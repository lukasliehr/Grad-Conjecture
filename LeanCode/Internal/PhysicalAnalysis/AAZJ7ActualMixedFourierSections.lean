import AAZJ6ExactFourierDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace









open Grad.AnnularRadialJets Grad.AnnularRegularity






section FourierSections
variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))

def annularMixedFourierSection (radial angular cell : ℕ) (angles : ℝ × ℝ) : RadialContinuousSection 1 lower :=
  ∑' mode : HighAnnularMode, annularFourierCoefficient angular cell mode angles •
    annularPhysicalJetSection parameters lower positive bounded jet weak radial mode

variable (grades : ∀ order grade, HasAnnularRawGrade lower grade (jet order))

include grades

theorem annularFourierSection_terms_summable (radial angular cell : ℕ) (angles : ℝ × ℝ) :
    Summable (fun mode : HighAnnularMode => annularFourierCoefficient angular cell mode angles •
      annularPhysicalJetSection parameters lower positive bounded jet weak radial mode) := by
  apply Summable.of_norm_bounded
    (annularPhysicalJetSection_weighted_summable parameters lower positive bounded jet weak radial (angular + cell)
      (grades radial (angular + cell + 2)) (grades (radial + 1) (angular + cell + 2)))
  intro mode
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (annularFourierCoefficient_norm_le angular cell mode angles) (norm_nonneg _)

theorem annularMixedFourierSection_apply (radial angular cell : ℕ) (angles : ℝ × ℝ)
    (radius : Icc lower (1 : ℝ)) :
    annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell angles radius =
      ∑' mode : HighAnnularMode, annularFourierCoefficient angular cell mode angles •
        annularPhysicalJetSection parameters lower positive bounded jet weak radial mode radius := by
  exact (ContinuousMap.tsum_apply
    (annularFourierSection_terms_summable parameters lower positive bounded jet weak grades radial angular cell angles) radius).symm

/-- Joint continuity of every mixed derivative's radial section in both
Fourier variables, in the uniform norm on the full closed radial interval. -/
theorem annularMixedFourierSection_continuous (radial angular cell : ℕ) :
    Continuous (annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell) := by
  apply continuous_tsum
    (fun mode => (annularFourierCoefficient_continuous angular cell mode).smul continuous_const)
    (annularPhysicalJetSection_weighted_summable parameters lower positive bounded jet weak radial (angular + cell)
      (grades radial (angular + cell + 2)) (grades (radial + 1) (angular + cell + 2)))
  intro mode angles
  change ‖annularFourierCoefficient angular cell mode angles •
    annularPhysicalJetSection parameters lower positive bounded jet weak radial mode‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (annularFourierCoefficient_norm_le angular cell mode angles) (norm_nonneg _)

/-- All mixed Fourier sections retain the actual closed-interval radial
primitive law, hence the radial derivative costs the next actual physical jet. -/
theorem annularMixedFourierSection_radial (radial angular cell : ℕ) (angles : ℝ × ℝ) :
    AnnularSectionDerivative lower positive bounded.le
      (annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell angles)
      (annularMixedFourierSection parameters lower positive bounded jet weak (radial + 1) angular cell angles) :=
  annularSectionDerivative_tsum lower positive bounded.le _ _
    (annularFourierSection_terms_summable parameters lower positive bounded jet weak grades radial angular cell angles)
    (annularFourierSection_terms_summable parameters lower positive bounded jet weak grades (radial + 1) angular cell angles)
    (fun mode => annularSectionDerivative_smul lower positive bounded.le _ _
      (annularPhysicalJetSection_integral parameters lower positive bounded jet weak radial mode)
      (annularFourierCoefficient angular cell mode angles))

theorem annularMixedFourierSection_radialDerivative (radial angular cell : ℕ) (angles : ℝ × ℝ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (radialSectionExtension 1 lower bounded.le
        (annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell angles))
      (annularMixedFourierSection parameters lower positive bounded jet weak (radial + 1) angular cell angles ⟨radius, inside⟩)
      (Icc lower 1) radius :=
  annularSectionDerivative_hasDerivWithinAt lower positive bounded.le _ _
    (annularMixedFourierSection_radial parameters lower positive bounded jet weak grades radial angular cell angles) radius inside

end FourierSections
end Grad.AnnularJointRegularity
