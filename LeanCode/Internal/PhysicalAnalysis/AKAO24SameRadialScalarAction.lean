import AKAO23SameMeanFreeKernelAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularPhysicalReconstruction Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable {input output : ℕ} (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {row : DivisionRow input lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (scalar : ℝ → ℂ) (continuousScalar : ContinuousOn scalar (Icc lower 1))
    (kernel : (r : RadialPoint) → RadialKernel parameters r input output)
    (regular : RegularKernelFamily kernel) (smooth : SmoothConjugatedFamily parameters lower positive bounded.le kernel)
    (scaledRegular : RegularKernelFamily (fun r => fullKernelSmul (scalar r.val) (kernel r)))
    (scaledSmooth : SmoothConjugatedFamily parameters lower positive bounded.le (fun r => fullKernelSmul (scalar r.val) (kernel r)))

include continuousScalar

theorem physicalCurve_action_radial_smul (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    (curves.action parameters lower positive bounded (fun r => fullKernelSmul (scalar r.val) (kernel r)) scaledRegular scaledSmooth).physicalCurve 0 radius mode =
      scalar radius • (curves.action parameters lower positive bounded kernel regular smooth).physicalCurve 0 radius mode := by
  let first := curves.action parameters lower positive bounded (fun r => fullKernelSmul (scalar r.val) (kernel r)) scaledRegular scaledSmooth
  let second := curves.action parameters lower positive bounded kernel regular smooth
  apply collarCurve_eq_of_ae lower bounded
    (fun location => first.physicalCurve 0 location mode)
    (fun location => scalar location • second.physicalCurve 0 location mode)
    ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean output) 2 mode).continuous.comp_continuousOn
      (first.physicalCurve_smooth bounded 0).continuousOn)
    (continuousScalar.smul ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean output) 2 mode).continuous.comp_continuousOn
      (second.physicalCurve_smooth bounded 0).continuousOn)) _ inside
  filter_upwards [first.physicalCurve_actual bounded 0,second.physicalCurve_actual bounded 0,
    originalPhysicalSlice_action parameters lower positive bounded.le
      (fun r => fullKernelSmul (scalar r.val) (kernel r)) scaledRegular row,
    originalPhysicalSlice_action parameters lower positive bounded.le kernel regular row,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (regularRadialBulkAction parameters 0 lower positive bounded.le (fun r => fullKernelSmul (scalar r.val) (kernel r)) scaledRegular row),
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (regularRadialBulkAction parameters 0 lower positive bounded.le kernel regular row),
    ae_restrict_mem measurableSet_Icc]
      with location firstActual secondActual firstAction secondAction firstCoefficient secondCoefficient member
  simp only [pow_zero,one_smul] at firstActual secondActual
  rw [firstActual mode,secondActual mode]
  change lowRhoPhysicalCoefficient parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded.le (fun r => fullKernelSmul (scalar r.val) (kernel r)) scaledRegular row) location mode =
    scalar location • lowRhoPhysicalCoefficient parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded.le kernel regular row) location mode
  rw [← firstCoefficient mode,firstAction]
  simp only [fullNegativeKernelAction_smul,negativeTraceCoefficient_smul]
  rw [← secondAction,secondCoefficient mode,collarRadius_literal lower positive bounded.le location member]

theorem fullField_action_radial_smul (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.action parameters lower positive bounded (fun r => fullKernelSmul (scalar r.val) (kernel r)) scaledRegular scaledSmooth).fullField bounded (radius,angles) =
      scalar radius • (curves.action parameters lower positive bounded kernel regular smooth).fullField bounded (radius,angles) := by
  let first := curves.action parameters lower positive bounded (fun r => fullKernelSmul (scalar r.val) (kernel r)) scaledRegular scaledSmooth
  let second := curves.action parameters lower positive bounded kernel regular smooth
  apply congrFun (first.fullField_eq_of_doubleCoefficient bounded radius inside
    (fun query => scalar radius • second.fullField bounded (radius,query))
    ((second.fullField_continuous_angles bounded radius inside).const_smul (scalar radius))
    (fun axial polar => congrArg (scalar radius • ·) (second.fullField_angular_periodic bounded radius axial polar))
    (fun polar axial => congrArg (scalar radius • ·) (second.fullField_cell_periodic bounded radius polar axial)) _) angles
  intro mode
  have mapped := doubleCoefficient_valueMap (scalar radius • ContinuousLinearMap.id ℂ (ComplexEuclidean output))
    (fun query => second.fullField bounded (radius,query))
    (second.fullField_continuous_angles bounded radius inside) mode
  change doubleCoefficient (fun query => scalar radius • second.fullField bounded (radius,query)) mode =
    scalar radius • doubleCoefficient (fun query => second.fullField bounded (radius,query)) mode at mapped
  rw [mapped,second.fullField_doubleCoefficient bounded radius inside mode]
  exact (physicalCurve_action_radial_smul parameters lower positive bounded curves scalar continuousScalar kernel regular smooth
    scaledRegular scaledSmooth radius inside mode).symm

end Grad.ActualPolarFlux
