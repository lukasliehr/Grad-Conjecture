import AKAF6SamePhysicalSliceKernelAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularSmoothCore
open Grad.ActualSmoothPhysicalField Grad.PhaseAlgebra Grad.SourceCollarFullSource

/-- Equality of the actual physical Fourier coefficients determines these
same smooth representatives everywhere on the closed collar. -/
theorem samePhysical_fullField_eq {dimension : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row other : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row)
    (target : SmoothLowPhysicalRow parameters lower positive other) (bounded : lower < 1)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive row radius mode =
        lowRhoPhysicalCoefficient parameters lower positive other radius mode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    curves.fullField bounded (radius,angles) = target.fullField bounded (radius,angles) := by
  apply congrFun (curves.fullField_eq_of_doubleCoefficient bounded radius inside _
    (target.fullField_continuous_angles bounded radius inside)
    (target.fullField_angular_periodic bounded radius)
    (target.fullField_cell_periodic bounded radius) _) angles
  intro mode
  rw [target.fullField_doubleCoefficient bounded radius inside mode]
  symm
  apply collarCurve_eq_of_ae lower bounded
    (fun location => curves.physicalCurve 0 location mode)
    (fun location => target.physicalCurve 0 location mode)
    ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).continuous.comp_continuousOn
      (curves.physicalCurve_smooth bounded 0).continuousOn)
    ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).continuous.comp_continuousOn
      (target.physicalCurve_smooth bounded 0).continuousOn) _ inside
  filter_upwards [curves.physicalCurve_actual bounded 0,target.physicalCurve_actual bounded 0,same]
    with location first second law
  rw [first mode,second mode,law mode]

/-- Exact scalar multiplication of the SAME full physical field. -/
theorem samePhysical_fullField_smul {dimension : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)
    (scalar : ℂ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.smul scalar).fullField bounded (radius,angles) = scalar • curves.fullField bounded (radius,angles) := by
  apply congrFun ((curves.smul scalar).fullField_eq_of_doubleCoefficient bounded radius inside
    (fun query => scalar • curves.fullField bounded (radius,query))
    ((curves.fullField_continuous_angles bounded radius inside).const_smul scalar)
    (fun axial polar => congrArg (scalar • ·) (curves.fullField_angular_periodic bounded radius axial polar))
    (fun polar axial => congrArg (scalar • ·) (curves.fullField_cell_periodic bounded radius polar axial)) _) angles
  intro mode
  have mapped := doubleCoefficient_valueMap (scalar • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension))
    (fun query => curves.fullField bounded (radius,query))
    (curves.fullField_continuous_angles bounded radius inside) mode
  change doubleCoefficient (fun query => scalar • curves.fullField bounded (radius,query)) mode =
    scalar • doubleCoefficient (fun query => curves.fullField bounded (radius,query)) mode at mapped
  rw [mapped,curves.fullField_doubleCoefficient bounded radius inside mode,
    (curves.smul scalar).physicalCurve_coefficient bounded 0 radius inside mode,
    curves.physicalCurve_coefficient bounded 0 radius inside mode]
  change scalar • (_ • curves.curve 0 radius mode) = _ • (scalar • curves.curve 0 radius mode)
  exact smul_comm _ _ _

end Grad.ActualPolarEquations
