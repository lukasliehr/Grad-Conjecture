import AKAF5SameSevenGenuineAngularLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.AnnularPhysicalReconstruction Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.ActualSmoothPhysicalField Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.PhaseAlgebra
open Grad.AnnularKernelContinuity

/-- The original low-rho slice intertwines the SAME completed full kernel
with its exact negative trace action, including all angular and axial modes. -/
theorem originalPhysicalSlice_action {input output : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius input output)
    (regular : RegularKernelFamily kernel) (row : DivisionRow input lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      originalPhysicalSlice parameters lower positive bounded
        (regularRadialBulkAction parameters 0 lower positive bounded kernel regular row) radius =
      fullNegativeKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded radius)) 0 0
        (kernel (collarRadius lower positive bounded radius))
        (originalPhysicalSlice parameters lower positive bounded row radius) := by
  filter_upwards [originalPhysicalSlice_coefficient parameters lower positive bounded row,
    originalPhysicalSlice_coefficient parameters lower positive bounded
      (regularRadialBulkAction parameters 0 lower positive bounded kernel regular row),
    lowRegularAction_physical parameters lower positive bounded kernel regular row]
      with radius inputSame outputSame actual
  apply NegativeTrace.ext_coefficient
  intro mode
  rw [outputSame mode]
  have full := fullNegativeKernelAction_coefficient_hasSum
    (radialKernelParameters parameters (collarRadius lower positive bounded radius)) 0 0
    (kernel (collarRadius lower positive bounded radius))
    (originalPhysicalSlice parameters lower positive bounded row radius) mode
  simp only [inputSame] at full
  exact (actual mode).unique full

end Grad.ActualPolarEquations
