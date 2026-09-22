import AJE45FiniteSourceGraphOrbitSmoothness
import AJB29ActualLpComplementaryEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.AnnularOrbitGenerators Grad.AnnularKernelOrbit Grad.AnnularVariational

section Extraction
variable {H ι V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    (projection : H →L[ℝ] lp (fun _ : ι => V) 2) (orbit : ℝ → H) (smooth : ContDiff ℝ ∞ orbit)
    (frequency : ι → ℤ) (field : lp (fun _ : ι => V) 2)
    (character : ∀ time index, projection (orbit time) index = cellExponential (frequency index) time • field index)

include smooth character in
theorem realSourceGenerator_coordinates (order : ℕ) (index : ι) :
    projection (iteratedDeriv order orbit 0) index = (Complex.I * (frequency index : ℂ)) ^ order • field index := by
  let coefficient := (lp.evalCLM ℝ (fun _ : ι => V) 2 index).comp projection
  have extracted := coefficient_iteratedDeriv coefficient orbit smooth order 0
  have same : (fun time => coefficient (orbit time)) = fun time => cellExponential (frequency index) time • field index :=
    funext (fun time => character time index)
  rw [same,characterVector_iteratedDeriv] at extracted
  change projection (iteratedDeriv order orbit 0) index = _ at extracted
  simpa only [cellExponential,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_smul] using extracted
end Extraction

/-- The original total Fourier frequency controls each genuine pure-axis generator. -/
theorem sourceAxisFrequency_bound (axis : Bool) (mode : ℤ × ℤ) :
    |(sourceAxisFrequency axis mode : ℝ)| ≤ annularFrequency mode.1 mode.2 := by
  cases axis <;> simp only [sourceAxisFrequency,Bool.false_eq_true,if_false,if_true]
  · unfold annularFrequency
    linarith [abs_nonneg (mode.2 : ℝ)]
  · unfold annularFrequency
    linarith [abs_nonneg (mode.1 : ℝ)]

end Grad.AnnularStrongOrbit
