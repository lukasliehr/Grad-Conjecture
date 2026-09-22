import AKAO4LiteralPolarMatrixProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularPhysicalReconstruction Grad.AnnularPhysicalSolution Grad.AnnularCurrentEnergy

 theorem fullField_eq_of_row_eq {dimension : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {first second : DivisionRow dimension lower}
    (a : SmoothLowPhysicalRow parameters lower positive first) (b : SmoothLowPhysicalRow parameters lower positive second)
    (bounded : lower < 1) (same : first=second) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    a.fullField bounded (radius,angles)=b.fullField bounded (radius,angles) :=
  samePhysical_fullField_eq a b bounded
    (Eventually.of_forall (fun radius mode => congrArg
      (fun row => lowRhoPhysicalCoefficient parameters lower positive row radius mode) same)) radius inside angles

variable {input output : ℕ} (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {row : DivisionRow input lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

 theorem fullField_action_sub
    (first second : (radius : RadialPoint) → RadialKernel parameters radius input output)
    (firstRegular : RegularKernelFamily first) (secondRegular : RegularKernelFamily second)
    (firstSmooth : SmoothConjugatedFamily parameters lower positive bounded.le first)
    (secondSmooth : SmoothConjugatedFamily parameters lower positive bounded.le second)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.action parameters lower positive bounded (fun r => fullKernelSub (first r) (second r))
      (firstRegular.sub secondRegular) (firstSmooth.sub secondSmooth)).fullField bounded (radius,angles) =
    (curves.action parameters lower positive bounded first firstRegular firstSmooth).fullField bounded (radius,angles) -
      (curves.action parameters lower positive bounded second secondRegular secondSmooth).fullField bounded (radius,angles) := by
  let a := curves.action parameters lower positive bounded first firstRegular firstSmooth
  let b := curves.action parameters lower positive bounded second secondRegular secondSmooth
  have same := fullField_eq_of_row_eq
    (curves.action parameters lower positive bounded (fun r => fullKernelSub (first r) (second r))
      (firstRegular.sub secondRegular) (firstSmooth.sub secondSmooth)) (a.sub b) bounded
    (congrArg (fun action : DivisionRow input lower →L[ℂ] DivisionRow output lower => action row)
      (regularRadialBulkAction_sub parameters 0 lower positive bounded.le first firstRegular second secondRegular)) radius inside angles
  rw [a.fullField_sub bounded b radius inside angles] at same
  exact same

 theorem fullField_action_add
    (first second : (radius : RadialPoint) → RadialKernel parameters radius input output)
    (firstRegular : RegularKernelFamily first) (secondRegular : RegularKernelFamily second)
    (firstSmooth : SmoothConjugatedFamily parameters lower positive bounded.le first)
    (secondSmooth : SmoothConjugatedFamily parameters lower positive bounded.le second)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.action parameters lower positive bounded (fun r => fullKernelAdd (first r) (second r))
      (firstRegular.add secondRegular) (firstSmooth.add secondSmooth)).fullField bounded (radius,angles) =
    (curves.action parameters lower positive bounded first firstRegular firstSmooth).fullField bounded (radius,angles) +
      (curves.action parameters lower positive bounded second secondRegular secondSmooth).fullField bounded (radius,angles) := by
  let a := curves.action parameters lower positive bounded first firstRegular firstSmooth
  let b := curves.action parameters lower positive bounded second secondRegular secondSmooth
  have same := fullField_eq_of_row_eq
    (curves.action parameters lower positive bounded (fun r => fullKernelAdd (first r) (second r))
      (firstRegular.add secondRegular) (firstSmooth.add secondSmooth)) (a.add b) bounded
    (congrArg (fun action : DivisionRow input lower →L[ℂ] DivisionRow output lower => action row)
      (regularRadialBulkAction_add parameters 0 lower positive bounded.le first second firstRegular secondRegular)) radius inside angles
  rw [a.fullField_add bounded b radius inside angles] at same
  exact same

 theorem fullField_action_comp {middle : ℕ}
    (outer : (radius : RadialPoint) → RadialKernel parameters radius middle output)
    (inner : (radius : RadialPoint) → RadialKernel parameters radius input middle)
    (outerRegular : RegularKernelFamily outer) (innerRegular : RegularKernelFamily inner)
    (outerSmooth : SmoothConjugatedFamily parameters lower positive bounded.le outer)
    (innerSmooth : SmoothConjugatedFamily parameters lower positive bounded.le inner)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.action parameters lower positive bounded (fun r => fullKernelComposition (outer r) (inner r))
      (outerRegular.comp innerRegular) (outerSmooth.comp innerSmooth)).fullField bounded (radius,angles) =
    ((curves.action parameters lower positive bounded inner innerRegular innerSmooth).action
      parameters lower positive bounded outer outerRegular outerSmooth).fullField bounded (radius,angles) := by
  exact fullField_eq_of_row_eq _ _ bounded
    (congrArg (fun action : DivisionRow input lower →L[ℂ] DivisionRow output lower => action row)
      (regularRadialBulkAction_comp parameters 0 lower positive bounded.le outer inner outerRegular innerRegular)) radius inside angles

 theorem fullField_action_congr
    (first second : (radius : RadialPoint) → RadialKernel parameters radius input output)
    (firstRegular : RegularKernelFamily first) (secondRegular : RegularKernelFamily second)
    (firstSmooth : SmoothConjugatedFamily parameters lower positive bounded.le first)
    (secondSmooth : SmoothConjugatedFamily parameters lower positive bounded.le second)
    (same : ∀ radius,first radius=second radius)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.action parameters lower positive bounded first firstRegular firstSmooth).fullField bounded (radius,angles) =
      (curves.action parameters lower positive bounded second secondRegular secondSmooth).fullField bounded (radius,angles) :=
  fullField_eq_of_row_eq _ _ bounded
    (congrArg (fun action : DivisionRow input lower →L[ℂ] DivisionRow output lower => action row)
      (regularRadialBulkAction_congr parameters 0 lower positive bounded.le first firstRegular second secondRegular same)) radius inside angles

 theorem fullField_action_projection (component : Fin input)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.action parameters lower positive bounded
      (fun r => coordinateProjectionKernel (radialKernelParameters parameters r) input component)
      (constantMatrixRadialKernel_regular parameters _ _ _)
      (smoothConjugatedFamily_fixed parameters lower positive bounded
        (fun p => coordinateProjectionKernel p input component) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _))).fullField bounded (radius,angles) =
      (curves.bulkUnit (0 : Fin 1) component).fullField bounded (radius,angles) := by
  apply samePhysical_fullField_eq _ _ bounded _ radius inside angles
  filter_upwards [originalPhysicalSlice_action parameters lower positive bounded.le
      (fun r => coordinateProjectionKernel (radialKernelParameters parameters r) input component)
      (constantMatrixRadialKernel_regular parameters _ _ _) row,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le row,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (regularRadialBulkAction parameters 0 lower positive bounded.le
        (fun r => coordinateProjectionKernel (radialKernelParameters parameters r) input component)
        (constantMatrixRadialKernel_regular parameters _ _ _) row),
    lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) component row]
      with location action inputSame outputSame projected
  intro mode
  rw [projected mode,← outputSame mode,action]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  have value := coordinateProjectionKernel_action_coefficient
    (radialKernelParameters parameters (collarRadius lower positive bounded.le location)) 0 0 component
    (originalPhysicalSlice parameters lower positive bounded.le row location) mode
  rw [inputSame mode] at value
  simpa [matrixUnit_apply,operatorBasis] using value

end Grad.ActualPolarFlux
