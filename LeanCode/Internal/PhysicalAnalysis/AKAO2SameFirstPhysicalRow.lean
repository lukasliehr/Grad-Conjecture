import AKAO1SameActualThirdFluxDerivative

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
open Grad.AnnularPhysicalReconstruction Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularLowEnergy Grad.PhaseAlgebra Grad.AnnularGeneralSourceRegularity Grad.AnnularCurrentEnergy

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)

def actualRetainedForceAction : DivisionRow 3 lower →L[ℂ] DivisionRow 1 lower :=
  regularRadialBulkAction parameters 0 lower positive bounded.le
    (fun radius => radialRetainedForceKernel parameters length compact state.val.val radius)
    (radialRetainedForceKernel_regular parameters length compact state.val)

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.retainedForce
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive
      (actualRetainedForceAction parameters length compact lower positive bounded state row) :=
  curves.action parameters lower positive bounded _
    (radialRetainedForceKernel_regular parameters length compact state.val)
    (actualRetainedForce_conjugated_smooth parameters length compact state lower positive bounded)

/-- The original j row before P is exactly (Ra_c)_1-r1*a_c, on every Fourier cell. -/
theorem sameFirstPhysicalRow_physicalCoefficients (row : DivisionRow 7 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive
        (lowPhysicalRowAction parameters length compact lower positive bounded.le state 0 row) radius mode 0 =
      lowRhoPhysicalCoefficient parameters lower positive
        (fullRotatedCovariantAction parameters length compact lower positive bounded.le state.val row) radius mode 0 -
      lowRhoPhysicalCoefficient parameters lower positive
        (actualRetainedForceAction parameters length compact lower positive bounded state
          (fullCovariantAction parameters length compact lower positive bounded.le state.val row)) radius mode 0 := by
  let covariant := fullCovariantAction parameters length compact lower positive bounded.le state.val row
  let rotated := fullRotatedCovariantAction parameters length compact lower positive bounded.le state.val row
  let force := actualRetainedForceAction parameters length compact lower positive bounded state covariant
  let output := lowPhysicalRowAction parameters length compact lower positive bounded.le state 0 row
  filter_upwards [originalPhysicalSlice_action parameters lower positive bounded.le
      (lowPhysicalRowKernel parameters length compact state 0) (lowPhysicalRowKernel_regular parameters length compact state 0) row,
    originalPhysicalSlice_action parameters lower positive bounded.le
      (fun radius => radialNormalizedCovariantKernel parameters length compact state.val.val radius state.val.property)
      (radialNormalizedCovariantKernel_regular parameters length compact state.val) row,
    originalPhysicalSlice_action parameters lower positive bounded.le
      (fun radius => radialNormalizedRotatedCovariantKernel parameters length compact state.val.val radius state.val.property)
      (radialNormalizedRotatedCovariantKernel_regular parameters length compact state.val) row,
    originalPhysicalSlice_action parameters lower positive bounded.le
      (fun radius => radialRetainedForceKernel parameters length compact state.val.val radius)
      (radialRetainedForceKernel_regular parameters length compact state.val) covariant,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le output,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le rotated,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le force]
      with radius outputSame covariantSame rotatedSame forceSame outputCoefficient rotatedCoefficient forceCoefficient
  intro mode
  change originalPhysicalSlice parameters lower positive bounded.le covariant radius = _ at covariantSame
  change originalPhysicalSlice parameters lower positive bounded.le rotated radius = _ at rotatedSame
  change originalPhysicalSlice parameters lower positive bounded.le force radius = _ at forceSame
  have literal := outputSame
  change originalPhysicalSlice parameters lower positive bounded.le output radius =
    fullNegativeKernelAction _ 0 0 (radialNormalizedUnprojectedFirstRowKernel parameters length compact state _) _ at literal
  simp only [radialNormalizedUnprojectedFirstRowKernel,fullNegativeKernelAction_sub,fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply] at literal
  rw [← rotatedSame,← covariantSame,← forceSame] at literal
  have value := congrArg (fun trace => negativeTraceCoefficient
    (radialKernelParameters parameters (collarRadius lower positive bounded.le radius)) 0 0 trace mode 0) literal
  simp only [negativeTraceCoefficient_sub,PiLp.sub_apply,coordinateProjectionKernel_action_coefficient] at value
  rw [outputCoefficient mode,rotatedCoefficient mode,forceCoefficient mode] at value
  exact value

/-- Pointwise same-field j=(Ra_c)_1-r1*a_c. The radial scalar equation applies its prescribed outer P. -/
theorem sameFirstPhysicalRow_pointwise {row : DivisionRow 7 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.lowPhysicalCurves parameters length compact lower positive bounded state 0).fullField bounded (radius,angles) =
      ((curves.rotatedCovariant parameters length compact lower positive bounded state.val).bulkUnit (0 : Fin 1) 0).fullField bounded (radius,angles) -
      ((curves.covariant parameters length compact lower positive bounded state.val).retainedForce parameters length compact lower positive bounded state).fullField bounded (radius,angles) := by
  let covariant := curves.covariant parameters length compact lower positive bounded state.val
  let rotated := curves.rotatedCovariant parameters length compact lower positive bounded state.val
  let force := covariant.retainedForce parameters length compact lower positive bounded state
  let target := (rotated.bulkUnit (0 : Fin 1) 0).sub force
  have equality := samePhysical_fullField_eq
    (curves.lowPhysicalCurves parameters length compact lower positive bounded state 0) target bounded (by
      filter_upwards [sameFirstPhysicalRow_physicalCoefficients parameters length compact lower positive bounded state row,
        Grad.AnnularSmoothCore.lowRhoPhysicalCoefficient_sub_ae parameters lower positive
          (bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3) (fullRotatedCovariantAction parameters length compact lower positive bounded.le state.val row))
          (actualRetainedForceAction parameters length compact lower positive bounded state
            (fullCovariantAction parameters length compact lower positive bounded.le state.val row)),
        lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) (0 : Fin 3)
          (fullRotatedCovariantAction parameters length compact lower positive bounded.le state.val row)]
          with location same subtract projected
      intro mode
      rw [subtract mode,projected mode]
      apply PiLp.ext
      intro component
      fin_cases component
      simpa [matrixUnit_apply,operatorBasis] using same mode) radius inside angles
  rw [(rotated.bulkUnit (0 : Fin 1) 0).fullField_sub bounded force radius inside angles] at equality
  exact equality

end Grad.ActualPolarFlux
