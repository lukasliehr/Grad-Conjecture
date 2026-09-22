import AAZJ12ActualFourierL2Identity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularRadialJets Grad.AnnularRegularity

section OriginalTorus
variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))

def annularMixedTorusSection (radial angular cell : ℕ) (angles : CellCircle × CellCircle) :
    RadialContinuousSection 1 lower :=
  ∑' mode : HighAnnularMode,
    (cellCharacter mode.val.1 angles.1 * cellCharacter mode.val.2 angles.2 * annularMixedSymbol angular cell mode) •
      annularPhysicalJetSection parameters lower positive bounded jet weak radial mode

/-- The actual two-torus reconstruction pulls back to precisely the checked
physical Fourier series, at the original period in both angular variables. -/
theorem annularMixedTorusSection_coe (radial angular cell : ℕ) (polar axial : ℝ) :
    annularMixedTorusSection parameters lower positive bounded jet weak radial angular cell
      ((polar : CellCircle), (axial : CellCircle)) =
      annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell (polar, axial) := by
  unfold annularMixedTorusSection annularMixedFourierSection
  apply tsum_congr
  intro mode
  simp only [cellCharacter_coe, annularFourierCoefficient]

variable (grades : ∀ order grade, HasAnnularRawGrade lower grade (jet order))
include grades

theorem annularMixedTorusSection_continuous (radial angular cell : ℕ) :
    Continuous (annularMixedTorusSection parameters lower positive bounded jet weak radial angular cell) := by
  have each (mode : HighAnnularMode) : Continuous (fun angles : CellCircle × CellCircle =>
      (cellCharacter mode.val.1 angles.1 * cellCharacter mode.val.2 angles.2 * annularMixedSymbol angular cell mode) •
        annularPhysicalJetSection parameters lower positive bounded jet weak radial mode) := by
    exact ((((cellCharacter mode.val.1).continuous.comp continuous_fst).mul
      ((cellCharacter mode.val.2).continuous.comp continuous_snd)).mul continuous_const).smul continuous_const
  unfold annularMixedTorusSection
  apply continuous_tsum each
    (annularPhysicalJetSection_weighted_summable parameters lower positive bounded jet weak radial (angular + cell)
      (grades radial (angular + cell + 2)) (grades (radial + 1) (angular + cell + 2)))
  intro mode angles
  change ‖(cellCharacter mode.val.1 angles.1 * cellCharacter mode.val.2 angles.2 * annularMixedSymbol angular cell mode) •
    annularPhysicalJetSection parameters lower positive bounded jet weak radial mode‖ ≤ _
  simp only [norm_smul, norm_mul, cellCharacter_apply_norm, one_mul]
  exact mul_le_mul_of_nonneg_right (annularMixedSymbol_norm_le angular cell mode) (norm_nonneg _)

/-- Every mixed derivative is a continuous function on the actual closed
collar times the original two circles, including both radial endpoints. -/
theorem annularMixedTorusValue_continuous (radial angular cell : ℕ) :
    Continuous (fun point : (Icc lower (1 : ℝ)) × (CellCircle × CellCircle) =>
      annularMixedTorusSection parameters lower positive bounded jet weak radial angular cell point.2 point.1) := by
  exact continuous_eval.comp
    (((annularMixedTorusSection_continuous parameters lower positive bounded jet weak grades radial angular cell).comp
      continuous_snd).prodMk continuous_fst)

end OriginalTorus
end Grad.AnnularJointRegularity
