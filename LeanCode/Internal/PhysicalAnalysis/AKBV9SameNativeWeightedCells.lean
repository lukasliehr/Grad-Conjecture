import AKBV8NativeWeightedAnnularField
import AKAW7SameWeightedCartesianCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.BoundaryTrace Grad.SourceCollarFullSource Grad.PhaseAlgebra

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

theorem weightedFullField_doubleCoefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => weightedFullField curves bounded (radius,angles)) mode =
      curves.curve 0 radius mode := by
  exact (doubleCoefficient_swap _ (weightedFullField_continuous_angles curves bounded radius inside) mode.1 mode.2).trans
    (weightedFullField_coefficient curves bounded radius inside mode)

/-- The analytic weight is restored on each actual axial cell, after the full native Fourier reconstruction. -/
theorem weightedFullField_cell (radius : ℝ) (inside : radius ∈ Icc lower 1) (cell : ℤ) (polar : ℝ) :
    angularCoefficient (fun axial => weightedFullField curves bounded (radius,polar,axial)) cell =
      (Real.exp (radialPhase parameters radius cell) : ℂ) •
        angularCoefficient (fun axial => curves.fullField bounded (radius,polar,axial)) cell := by
  have fullContinuous := weightedFullField_continuous_angles curves bounded radius inside
  have physicalContinuous := curves.fullField_continuous_angles bounded radius inside
  have firstContinuous := Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter _ fullContinuous cell
  have secondContinuous := Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter _ physicalContinuous cell
  apply congrFun (periodicFourier_ext _ _ firstContinuous
    (secondContinuous.const_smul (Real.exp (radialPhase parameters radius cell) : ℂ)) ?_ ?_ ?_) polar
  · intro angle
    exact congrArg (fun field : ℝ → ComplexEuclidean dimension => angularCoefficient field cell)
      (funext (fun axial => weightedFullField_angular_periodic curves bounded radius axial angle))
  · intro angle
    simp only [Pi.smul_apply]
    apply congrArg ((Real.exp (radialPhase parameters radius cell) : ℂ) • ·)
    exact congrArg (fun field : ℝ → ComplexEuclidean dimension => angularCoefficient field cell)
      (funext (fun axial => curves.fullField_angular_periodic bounded radius axial angle))
  · intro angular
    rw [angularCoefficient_smul_continuous _ _ angular]
    change doubleCoefficient (fun angles => weightedFullField curves bounded (radius,angles)) (angular,cell) =
      (Real.exp (radialPhase parameters radius cell) : ℂ) •
        doubleCoefficient (fun angles => curves.fullField bounded (radius,angles)) (angular,cell)
    rw [weightedFullField_doubleCoefficient curves bounded radius inside,
      curves.fullField_doubleCoefficient bounded radius inside,
      curves.physicalCurve_coefficient bounded 0 radius inside,Real.exp_neg,Complex.ofReal_inv]
    exact (smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') _).symm

end Grad.CartesianCoreRecovery
