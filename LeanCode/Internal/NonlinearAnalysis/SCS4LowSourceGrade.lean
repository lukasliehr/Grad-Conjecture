import SCS3DividedSourceRows

noncomputable section

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.CompatibleCompletion Grad.ConstrainedGrades Grad.AxisCore
open Grad.SourceCollarBulk Grad.SourceCollarDivision

theorem dividedPlanar_lower {low high power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + 3 ≤ low) (grades : low ≤ high)
    (source : ZAmbient parameters high) :
    dividedPlanar lower positive bounded parameters paid (zLowering parameters grades source) =
      dividedPlanar lower positive bounded parameters (paid.trans grades) source := by
  have factor := DFunLike.congr_fun
    (completedDivisionRow_inclusion (dimension := 2) (power := power) (radial := 0)
      lower positive bounded parameters paid grades) (originalSourcePlanar parameters high source)
  simpa only [dividedPlanar, ContinuousLinearMap.comp_apply, originalSourcePlanar_lower] using factor

theorem dividedFourth_lower {low high power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (paid : power + 3 ≤ low) (grades : low ≤ high)
    (source : ZAmbient parameters high) :
    dividedFourth lower positive bounded parameters L paid (zLowering parameters grades source) =
      dividedFourth lower positive bounded parameters L (paid.trans grades) source := by
  have factor := DFunLike.congr_fun
    (completedDivisionRow_inclusion (dimension := 1) (power := power) (radial := 0)
      lower positive bounded parameters paid grades) (source 3)
  simp only [dividedFourth, zLowering_apply]
  exact congrArg (fun row : DivisionRow 1 lower => (L : ℂ)⁻¹ • row) factor

theorem dividedSourceRows_lower {low high power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (paid : power + 3 ≤ low) (grades : low ≤ high)
    (source : ZAmbient parameters high) (component : Fin 3) :
    dividedSourceRows lower positive bounded parameters L paid (zLowering parameters grades source) component =
      dividedSourceRows lower positive bounded parameters L (paid.trans grades) source component := by
  unfold dividedSourceRows
  rw [dividedPlanar_lower, dividedFourth_lower]

/-- The one-high coefficient branch consumes only the original source
grade three. Its field is exactly the same one as in the high input branch. -/
theorem dividedSourceRows_low_bound {grade : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (large : 3 ≤ grade)
    (source : ZAmbient parameters grade) (component : Fin 3) :
    ‖dividedSourceRows (power := 0) lower positive bounded parameters L large source component‖ ≤
      sourceDivisionConstant 0 L * ‖zLowering parameters large source‖ := by
  rw [← dividedSourceRows_lower lower positive bounded parameters L (by omega : 0 + 3 ≤ 3) large source component]
  exact dividedSourceRows_bound lower positive bounded parameters L (by omega) _ component

end Grad.SourceCollarFullSource
