import AAZJ7ActualMixedFourierSections

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







section MixedDerivatives
variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))
    (grades : ∀ order grade, HasAnnularRawGrade lower grade (jet order))

include grades

/-- Genuine angular differentiation in the uniform closed-radial norm. -/
theorem annularMixedFourierSection_angular (radial angular cell : ℕ) (polar axial : ℝ) :
    HasDerivAt (fun angle => annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell (angle, axial))
      (annularMixedFourierSection parameters lower positive bounded jet weak radial (angular + 1) cell (polar, axial)) polar := by
  have majorant := annularPhysicalJetSection_weighted_summable parameters lower positive bounded jet weak radial (angular + 1 + cell)
    (grades radial (angular + 1 + cell + 2)) (grades (radial + 1) (angular + 1 + cell + 2))
  have each (mode : HighAnnularMode) (angle : ℝ) :=
    (annularFourierCoefficient_angular angular cell mode angle axial).smul_const
      (annularPhysicalJetSection parameters lower positive bounded jet weak radial mode)
  have bound (mode : HighAnnularMode) (angle : ℝ) :
      ‖annularFourierCoefficient (angular + 1) cell mode (angle, axial) •
          annularPhysicalJetSection parameters lower positive bounded jet weak radial mode‖ ≤
        (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ (angular + 1 + cell) *
          ‖annularPhysicalJetSection parameters lower positive bounded jet weak radial mode‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (annularFourierCoefficient_norm_le (angular + 1) cell mode (angle, axial)) (norm_nonneg _)
  exact hasDerivAt_tsum majorant each bound
    (annularFourierSection_terms_summable parameters lower positive bounded jet weak grades radial angular cell (0, axial)) polar

/-- Genuine cell-angle differentiation, with the original cell frequency. -/
theorem annularMixedFourierSection_cell (radial angular cell : ℕ) (polar axial : ℝ) :
    HasDerivAt (fun angle => annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell (polar, angle))
      (annularMixedFourierSection parameters lower positive bounded jet weak radial angular (cell + 1) (polar, axial)) axial := by
  have majorant := annularPhysicalJetSection_weighted_summable parameters lower positive bounded jet weak radial (angular + (cell + 1))
    (grades radial (angular + (cell + 1) + 2)) (grades (radial + 1) (angular + (cell + 1) + 2))
  have each (mode : HighAnnularMode) (angle : ℝ) :=
    (annularFourierCoefficient_cell angular cell mode polar angle).smul_const
      (annularPhysicalJetSection parameters lower positive bounded jet weak radial mode)
  have bound (mode : HighAnnularMode) (angle : ℝ) :
      ‖annularFourierCoefficient angular (cell + 1) mode (polar, angle) •
          annularPhysicalJetSection parameters lower positive bounded jet weak radial mode‖ ≤
        (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ (angular + (cell + 1)) *
          ‖annularPhysicalJetSection parameters lower positive bounded jet weak radial mode‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (annularFourierCoefficient_norm_le angular (cell + 1) mode (polar, angle)) (norm_nonneg _)
  exact hasDerivAt_tsum majorant each bound
    (annularFourierSection_terms_summable parameters lower positive bounded jet weak grades radial angular cell (polar, 0)) axial

/-- All mixed derivative values are jointly continuous through both radial
endpoints; this is continuity on the actual closed product domain. -/
theorem annularMixedFourierValue_continuous (radial angular cell : ℕ) :
    Continuous (fun point : (Icc lower (1 : ℝ)) × (ℝ × ℝ) =>
      annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell point.2 point.1) := by
  exact continuous_eval.comp
    (((annularMixedFourierSection_continuous parameters lower positive bounded jet weak grades radial angular cell).comp
      continuous_snd).prodMk continuous_fst)

theorem annularMixedFourierValue_angular (radial angular cell : ℕ)
    (radius : Icc lower (1 : ℝ)) (polar axial : ℝ) :
    HasDerivAt (fun angle => annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell (angle, axial) radius)
      (annularMixedFourierSection parameters lower positive bounded jet weak radial (angular + 1) cell (polar, axial) radius) polar :=
  (ContinuousMap.evalCLM ℝ radius : RadialContinuousSection 1 lower →L[ℝ] ComplexEuclidean 1).hasFDerivAt.comp_hasDerivAt polar
    (annularMixedFourierSection_angular parameters lower positive bounded jet weak grades radial angular cell polar axial)

theorem annularMixedFourierValue_cell (radial angular cell : ℕ)
    (radius : Icc lower (1 : ℝ)) (polar axial : ℝ) :
    HasDerivAt (fun angle => annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell (polar, angle) radius)
      (annularMixedFourierSection parameters lower positive bounded jet weak radial angular (cell + 1) (polar, axial) radius) axial :=
  (ContinuousMap.evalCLM ℝ radius : RadialContinuousSection 1 lower →L[ℝ] ComplexEuclidean 1).hasFDerivAt.comp_hasDerivAt axial
    (annularMixedFourierSection_cell parameters lower positive bounded jet weak grades radial angular cell polar axial)

end MixedDerivatives
end Grad.AnnularJointRegularity
