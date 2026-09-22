import NonlinearRadialCorrection
import RotationAverageDifferential

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily Grad.Constraints

theorem mean_diskEuler_zero {potential : Plane → ℝ → ℂ} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry potential) (Metric.ball 0 radius ×ˢ univ))
    (meanZero : ∀ point ∈ Metric.ball (0 : Plane) radius, ∀ time,
      complexAngularAverage potential point time = 0)
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    complexAngularAverage (diskEuler potential) point time = 0 := by
  have eventualZero : rotationAverage (fun argument => potential argument time) =ᶠ[𝓝 point]
      fun _ => (0 : ℂ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds pointIn] with argument argumentIn
    exact meanZero argument argumentIn time
  have equality := rotationAverage_euler (cellSection_smooth smooth time) pointIn
  rw [eventualZero.fderiv_eq] at equality
  simpa [diskEuler, complexAngularAverage_eq_rotationAverage] using equality.symm

theorem complex_second_row_eq (cellLength epsilon : ℝ)
    {mapping : Plane → ℝ → ComplexVec} {potential : Plane → ℝ → ℂ} {radius : ℝ}
    (mappingSmooth : ContDiffOn ℝ ∞ (Function.uncurry mapping) (Metric.ball 0 radius ×ˢ univ))
    (potentialSmooth : ContDiffOn ℝ ∞ (Function.uncurry potential) (Metric.ball 0 radius ×ˢ univ))
    (meanZero : ∀ point ∈ Metric.ball (0 : Plane) radius, ∀ time,
      complexAngularAverage potential point time = 0)
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    complexRawRows cellLength epsilon mapping potential point time 1 =
      diskEuler potential point time - complexDot (diskEuler mapping point time) (diskAngular mapping point time) +
        meanEulerAngularProduct mapping point time := by
  have averageSub : complexAngularAverage (fun argument cellTime => diskEuler potential argument cellTime -
        complexDot (diskEuler mapping argument cellTime) (diskAngular mapping argument cellTime)) point time =
      complexAngularAverage (diskEuler potential) point time - meanEulerAngularProduct mapping point time := by
    exact rotationAverage_sub
      (cellSection_smooth (diskEuler_joint_smooth potentialSmooth) time).continuousOn
      (cellSection_smooth
        (field := fun argument cellTime => complexDot (diskEuler mapping argument cellTime)
          (diskAngular mapping argument cellTime))
        (eulerAngularProduct_joint_smooth mappingSmooth) time).continuousOn pointIn
  change _ - complexAngularAverage _ point time = _
  rw [averageSub, mean_diskEuler_zero potentialSmooth meanZero point pointIn time]
  ring

theorem complex_fourth_row_eq (cellLength epsilon : ℝ)
    (mapping : Plane → ℝ → ComplexVec) (potential : Plane → ℝ → ℂ) (point : Plane) (time : ℝ) :
    (‖point‖ ^ 2) • quotientFields cellLength epsilon mapping potential point time 2 =
      complexRawRows cellLength epsilon mapping potential point time 3 := by
  change (‖point‖ ^ 2) • complexRemoveAngularAverage (fun argument cellTime =>
    complexDeterminant (fderiv ℝ (fun y => mapping y cellTime) argument (diskBasis 0))
      (fderiv ℝ (fun y => mapping y cellTime) argument (diskBasis 1))
      (complexAffineStateDerivative cellLength epsilon mapping argument cellTime)) point time =
    complexRemoveAngularAverage (fun argument cellTime =>
      complexDeterminant (diskEuler mapping argument cellTime) (diskAngular mapping argument cellTime)
        (complexAffineStateDerivative cellLength epsilon mapping argument cellTime)) point time
  simp only [complexRemoveAngularAverage]
  simp_rw [determinant_diskEuler_diskAngular]
  rw [complexAngularAverage_eq_rotationAverage, complexAngularAverage_eq_rotationAverage,
    rotationAverage_radial_pullout]
  exact smul_sub _ _ _

/-- O13--O17 on the original constrained potential domain, using the actual
integral-defined radial correction. No extra projection changes the residual. -/
theorem literalRows : LiteralRowsGoal := by
  intro cellLength epsilon radius mapping potential radiusLarge mappingSmooth potentialSmooth meanZero point pointBound time
  have pointIn : point ∈ Metric.ball (0 : Plane) radius := by
    simpa [Metric.mem_ball, dist_zero_right] using pointBound.trans_lt radiusLarge
  have secondRow := complex_second_row_eq cellLength epsilon mappingSmooth potentialSmooth
    meanZero point pointIn time
  have correction := nonlinearRadialQuotient_identity mappingSmooth point pointIn time
  have plus : star (complexDiskCoordinate point) * quotientFields cellLength epsilon mapping potential point time 0 =
      complexRawRows cellLength epsilon mapping potential point time 1 +
        Complex.I * complexRawRows cellLength epsilon mapping potential point time 0 := by
    rw [secondRow, correction]
    exact literal_plus_pointwise mapping potential point time (nonlinearRadialQuotient mapping point time)
  have minus : complexDiskCoordinate point * quotientFields cellLength epsilon mapping potential point time 1 =
      complexRawRows cellLength epsilon mapping potential point time 1 -
        Complex.I * complexRawRows cellLength epsilon mapping potential point time 0 := by
    rw [secondRow, correction]
    exact literal_minus_pointwise mapping potential point time (nonlinearRadialQuotient mapping point time)
  funext row
  fin_cases row
  · change (_ - _) / (2 * Complex.I) = complexRawRows cellLength epsilon mapping potential point time 0
    rw [plus, minus]
    field_simp
    ring
  · change (_ + _) / 2 = complexRawRows cellLength epsilon mapping potential point time 1
    rw [plus, minus]
    ring
  · rfl
  · exact complex_fourth_row_eq cellLength epsilon mapping potential point time

end Grad.NonlinearQuotient
