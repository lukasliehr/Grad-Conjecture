import AKAO31SameCorrectedPAngularDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularPhysicalReconstruction Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularLowEnergy Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularCurrentEnergy

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)

/-- The SAME corrected radial flux is the true mean-free angular primitive
of the SAME original x, including the zero angular mode. -/
theorem sharedCorrectedP_primitiveCoefficients :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive
        (actualCorrectedPAction parameters length compact lower positive bounded state
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)) radius mode =
      angularInverseMultiplier mode • lowRhoPhysicalCoefficient parameters lower positive
        (bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 7)
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)) radius mode := by
  let seven := fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution
  filter_upwards [sharedCorrectedP_trace parameters length compact lower positive bounded state lengthPositive data solution,
    sharedFull_inputFidelity parameters length lower positive bounded.le lengthPositive data solution,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (actualCorrectedPAction parameters length compact lower positive bounded state seven),
    lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) (0 : Fin 7) seven]
      with radius same inputSame outputSame projected
  intro mode
  have primitive := physicalBulkFlux_coefficient parameters lower positive
    (collarRadius lower positive bounded.le radius) (collectRadial lower seven radius) mode
  rw [← same, outputSame mode] at primitive
  have input := inputSame mode 0
  rw [physicalBulkSevenTrace_coefficient] at input
  rw [input] at primitive
  rw [projected mode]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simpa [matrixUnit_apply,operatorBasis] using primitive

end Grad.ActualPolarFlux
