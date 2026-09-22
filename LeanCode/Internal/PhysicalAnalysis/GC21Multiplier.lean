import GC21HighProjection

noncomputable section

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.BoundaryTrace

/-- Bulk multiplication followed by the actual trace. No fractional boundary
multiplier is postulated. -/
def apMultiplierTrace {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (gradePositive : 1 ≤ grade)
    (coefficient : Coefficient L sigma gamma ell grade input output) :
    apGrade L sigma gamma ell input grade →L[ℂ] APBoundaryGrade L sigma gamma ell output grade :=
  (apBoundaryTrace L sigma gamma ell grade gradePositive).comp (apMultiplier admissible coefficient)

theorem apMultiplierTrace_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (gradePositive : 1 ≤ grade)
    (coefficient : Coefficient L sigma gamma ell grade input output)
    (field : apGrade L sigma gamma ell input grade) :
    ‖apMultiplierTrace admissible gradePositive coefficient field‖ ≤
      (Real.sqrt (traceCellConstant grade) * apMultiplierConstant L sigma gamma grade) * ‖coefficient‖ * ‖field‖ := by
  change ‖apBoundaryTrace L sigma gamma ell grade gradePositive (apMultiplier admissible coefficient field)‖ ≤ _
  calc
    _ ≤ Real.sqrt (traceCellConstant grade) * ‖apMultiplier admissible coefficient field‖ :=
      apBoundaryTrace_bound L sigma gamma ell grade gradePositive (apMultiplier admissible coefficient field)
    _ ≤ _ := by
      simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
        (apMultiplier_bound admissible coefficient field) (Real.sqrt_nonneg (traceCellConstant grade)))

theorem apHighMultiplierTrace_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (gradePositive : 1 ≤ grade)
    (coefficient : Coefficient L sigma gamma ell grade input output)
    (field : apGrade L sigma gamma ell input grade) :
    ‖apHighProjection L sigma gamma ell grade (apMultiplierTrace admissible gradePositive coefficient field)‖ ≤
      (Real.sqrt (traceCellConstant grade) * apMultiplierConstant L sigma gamma grade) * ‖coefficient‖ * ‖field‖ :=
  (apHighProjection_bound L sigma gamma ell grade _).trans
    (apMultiplierTrace_bound admissible gradePositive coefficient field)

theorem apMultiplierTrace_single_coefficient {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (gradePositive : 1 ≤ grade) (inputCell shift : ℤ)
    (coefficient : SmoothOperatorJet input output) (field : ClosedJet input) (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade
      (apMultiplierTrace admissible gradePositive (singleJetCoefficient L sigma gamma ell grade shift coefficient)
        (apFiniteInto L sigma gamma ell (Finsupp.single inputCell field))) mode =
      apCoreBoundaryCoefficient (Finsupp.single (inputCell + shift) (apProductJet coefficient field)) mode := by
  change apBoundaryCoefficient L sigma gamma ell grade
    (apBoundaryTrace L sigma gamma ell grade gradePositive
      (apMultiplier admissible (singleJetCoefficient L sigma gamma ell grade shift coefficient)
        (apFiniteInto L sigma gamma ell (Finsupp.single inputCell field)))) mode = _
  rw [apMultiplier_single, apBoundaryTrace_coefficient]

end Grad.GaugeCoefficients.Physical.WeightedTrace
