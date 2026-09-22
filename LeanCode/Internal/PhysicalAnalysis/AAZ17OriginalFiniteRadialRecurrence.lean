import AAZ16ComponentRadialRecurrence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRadialJets
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace








/-- A valid AG34 constant, depending only on k, a and L. -/
def annularRadialRecurrenceConstant (lower length : ℝ) (order : ℕ) : ℝ :=
  2 + 3 * annularLeibnizConstant lower 1 order + annularLeibnizConstant lower 2 order +
    1 / (3 * length ^ 2) + 1 / (3 * length)

theorem annularRadialRecurrenceConstant_positive (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (order : ℕ) : 0 < annularRadialRecurrenceConstant lower length order := by
  have first := annularLeibnizConstant_nonnegative lower positive 1 order
  have second := annularLeibnizConstant_nonnegative lower positive 2 order
  unfold annularRadialRecurrenceConstant
  positivity

theorem annularRadialCoefficient_absorb (first second cell source size f g h p xi : ℝ)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) (cellNonnegative : 0 ≤ cell)
    (sourceNonnegative : 0 ≤ source) (sizeNonnegative : 0 ≤ size)
    (fNonnegative : 0 ≤ f) (gNonnegative : 0 ≤ g) (hNonnegative : 0 ≤ h)
    (pBound : p ≤ (first + second + cell) * size + g + source * h)
    (xiBound : xi ≤ (2 * first + 1) * size + f) :
    p + xi ≤ (2 + 3 * first + second + cell + source) * (size + f + g + h) := by
  have excessSize : 0 ≤ (1 + source) * size := mul_nonneg (by positivity) sizeNonnegative
  have excessF : 0 ≤ (1 + 3 * first + second + cell + source) * f := mul_nonneg (by positivity) fNonnegative
  have excessG : 0 ≤ (1 + 3 * first + second + cell + source) * g := mul_nonneg (by positivity) gNonnegative
  have excessH : 0 ≤ (2 + 3 * first + second + cell) * h := mul_nonneg (by positivity) hNonnegative
  nlinarith

/-- AG34 in the original physical state Hilbert norm, at unchanged analytic
width. Every source derivative costs one inserted grade, every lower state
order costs two, and no derivative of the physical phase is omitted. -/
theorem annularPhysicalStateJet_recurrence (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (initial : AnnularRawState lower) (source : ℕ → AnnularRawSource lower)
    (jetGrades : ∀ index grade, HasAnnularRawStateGrade lower grade
      (annularPhysicalStateJet lower positive length initial source index))
    (sourceGrades : ∀ index grade, HasAnnularRawSourceGrade lower grade (source index))
    (order grade : ℕ) :
    let jet := annularPhysicalStateJet lower positive length initial source
    annularRawStateSize lower grade (jet (order + 1)) (jetGrades (order + 1) grade) ≤
      annularRadialRecurrenceConstant lower length order *
        (annularJetPrefixSize lower (grade + 2) order jet jetGrades +
         ‖annularRawWeighted lower (grade + 1) (source order).1 (sourceGrades order (grade + 1)).1‖ +
         ‖annularRawWeighted lower (grade + 1) (source order).2.1 (sourceGrades order (grade + 1)).2.1‖ +
         ‖annularRawWeighted lower (grade + 1) (source order).2.2 (sourceGrades order (grade + 1)).2.2‖) := by
  let jet := annularPhysicalStateJet lower positive length initial source
  have pBound := annularPhysicalJet_p_bound lower length positive lengthPositive initial source jetGrades sourceGrades order grade
  have xiBound := annularPhysicalJet_xi_bound lower length positive initial source jetGrades sourceGrades order grade
  have pairBound := annularRawStateSize_sum_bound lower grade (jet (order + 1)) (jetGrades (order + 1) grade)
  apply pairBound.trans
  exact annularRadialCoefficient_absorb _ _ _ _ _ _ _ _ _ _
    (annularLeibnizConstant_nonnegative lower positive 1 order)
    (annularLeibnizConstant_nonnegative lower positive 2 order) (by positivity) (by positivity)
    (annularJetPrefixSize_nonnegative lower (grade + 2) order jet jetGrades)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) pBound xiBound

end Grad.AnnularRadialJets
