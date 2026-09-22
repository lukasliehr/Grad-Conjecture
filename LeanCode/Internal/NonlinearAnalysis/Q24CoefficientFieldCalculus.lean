import Q24CoefficientFieldBilinear
import Q23SeedChartFamilies

noncomputable section

set_option maxHeartbeats 400000
open scoped ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.NonlinearQuotientBounds

/-- Parameter smoothness of the actual operator-valued coefficient action.
The function-level proof keeps the real/complex operator instances explicit. -/
theorem completedCoefficientField_smooth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (parameters : PhaseParameters) (grade : ℕ)
    (mapping : E → AGrade parameters 3 grade) (domain : Set E)
    (smooth : ContDiffOn ℝ ∞ mapping domain) :
    ContDiffOn ℝ ∞ (fun point => completedCoefficientField parameters 3 grade (mapping point)) domain := by
  apply q23RealSmooth_linearFunction_comp
    (fun field : AGrade parameters 3 grade => completedCoefficientField parameters 3 grade field)
  · intro first second
    exact (completedCoefficientField parameters 3 grade).map_add first second
  · intro scalar field
    apply ContinuousLinearMap.ext
    intro coefficient
    exact congrArg
      (fun operator : Grad.Q8FixedGrade.Carrier parameters grade →L[ℂ] AGrade parameters 3 grade => operator coefficient)
      (((completedCoefficientField parameters 3 grade).restrictScalars ℝ).map_smul scalar field)
  · exact (completedCoefficientField parameters 3 grade).continuous
  · exact smooth

end Grad.Q24Realization
