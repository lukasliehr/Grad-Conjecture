import AKAC17CorrectedPhysicalRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource

local instance angularPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

theorem periodicLift_continuous {E : Type*} [TopologicalSpace E] (field : ℝ → E)
    (continuousField : Continuous field) (periodic : Function.Periodic field (2 * Real.pi)) :
    Continuous periodic.lift := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact continuousField

theorem periodicScalar_eq_zero (field : ℝ → ℂ) (continuousField : Continuous field)
    (periodic : Function.Periodic field (2 * Real.pi))
    (zero : ∀ mode, angularCoefficient field mode = 0) (angle : ℝ) : field angle = 0 := by
  let circle : C(CellCircle,ℂ) := ⟨periodic.lift,periodicLift_continuous field continuousField periodic⟩
  have coefficients (mode : ℤ) : fourierCoeff circle mode = 0 := by
    rw [← angularCoefficient_circle]
    exact zero mode
  have summable : Summable (fourierCoeff circle) := by
    have equal : fourierCoeff circle = fun _ => (0 : ℂ) := funext coefficients
    rw [equal]
    exact summable_zero
  have series := has_pointwise_sum_fourier_series_of_summable summable (angle : CellCircle)
  simp only [coefficients,zero_smul] at series
  exact series.unique hasSum_zero

theorem periodicFourier_ext {dimension : ℕ} (first second : ℝ → ComplexEuclidean dimension)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second)
    (firstPeriodic : Function.Periodic first (2 * Real.pi))
    (secondPeriodic : Function.Periodic second (2 * Real.pi))
    (same : ∀ mode, angularCoefficient first mode = angularCoefficient second mode) : first = second := by
  funext angle
  apply PiLp.ext
  intro component
  apply sub_eq_zero.mp
  apply periodicScalar_eq_zero (fun angle => first angle component - second angle component)
    (((PiLp.continuous_apply (p := 2) _ component).comp firstContinuous).sub
      ((PiLp.continuous_apply (p := 2) _ component).comp secondContinuous))
    (fun angle => by
      change first (angle + 2 * Real.pi) component - second (angle + 2 * Real.pi) component = _
      rw [firstPeriodic angle,secondPeriodic angle]) _ angle
  intro mode
  have firstScalar : Continuous (fun angle => first angle component) := (PiLp.continuous_apply (p := 2) _ component).comp firstContinuous
  have secondScalar : Continuous (fun angle => second angle component) := (PiLp.continuous_apply (p := 2) _ component).comp secondContinuous
  rw [angularCoefficient_sub_general _ _ firstScalar secondScalar,
    ← angularCoefficient_component first firstContinuous component,
    ← angularCoefficient_component second secondContinuous component,same mode,sub_self]

/-- Equality of every actual double Fourier coefficient determines the full
continuous periodic vector field, with both angular variables retained. -/
theorem doubleFourier_ext {dimension : ℕ} (first second : ℝ × ℝ → ComplexEuclidean dimension)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second)
    (firstAngular : ∀ axial, Function.Periodic (fun polar => first (polar,axial)) (2 * Real.pi))
    (secondAngular : ∀ axial, Function.Periodic (fun polar => second (polar,axial)) (2 * Real.pi))
    (firstCell : ∀ polar, Function.Periodic (fun axial => first (polar,axial)) (2 * Real.pi))
    (secondCell : ∀ polar, Function.Periodic (fun axial => second (polar,axial)) (2 * Real.pi))
    (same : ∀ mode : ℤ × ℤ,
      angularCoefficient (fun axial => angularCoefficient (fun polar => first (polar,axial)) mode.1) mode.2 =
        angularCoefficient (fun axial => angularCoefficient (fun polar => second (polar,axial)) mode.1) mode.2) :
    first = second := by
  have inner (angular : ℤ) :
      (fun axial => angularCoefficient (fun polar => first (polar,axial)) angular) =
        (fun axial => angularCoefficient (fun polar => second (polar,axial)) angular) := by
    apply periodicFourier_ext _ _
      (angularCoefficient_continuous_parameter (fun point => first (point.2,point.1)) (firstContinuous.comp continuous_swap) angular)
      (angularCoefficient_continuous_parameter (fun point => second (point.2,point.1)) (secondContinuous.comp continuous_swap) angular)
    · intro axial
      exact congrArg (fun field : ℝ → ComplexEuclidean dimension => angularCoefficient field angular)
        (funext (fun polar => firstCell polar axial))
    · intro axial
      exact congrArg (fun field : ℝ → ComplexEuclidean dimension => angularCoefficient field angular)
        (funext (fun polar => secondCell polar axial))
    · exact fun cell => same (angular,cell)
  funext point
  have final := periodicFourier_ext (fun polar => first (polar,point.2)) (fun polar => second (polar,point.2))
    (firstContinuous.comp (continuous_id.prodMk continuous_const))
    (secondContinuous.comp (continuous_id.prodMk continuous_const)) (firstAngular point.2) (secondAngular point.2)
    (fun angular => congrFun (inner angular) point.2)
  exact congrFun final point.1

end Grad.ActualSmoothPhysicalField
