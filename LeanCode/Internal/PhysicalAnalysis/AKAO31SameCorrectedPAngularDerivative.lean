import AKAO30SameCorrectedPAction

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
open Grad.AnnularLowEnergy Grad.PhaseAlgebra Grad.BoundaryLift Grad.AnnularCurrentEnergy

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)

theorem originalCorrectedP_bulkTrace (r : RadialPoint) (field : CellL2 7)
    (compatible : BulkSevenCompatibility field) :
    fullNegativeKernelAction _ 0 0 (originalCorrectedPKernel parameters length compact state r)
      (bulkNegativeLift parameters r 7 ((lowStorageWeight lower positive r.val : ℂ)⁻¹ • field)) =
    physicalBulkFlux parameters lower positive r field := by
  let input := (lowStorageWeight lower positive r.val : ℂ)⁻¹ • field
  have law : BulkSevenCompatibility input := compatible.smul _ _
  have flux := physicalBulkFlux_laws parameters lower positive r field compatible
  have same := originalCorrectedPKernel_trace parameters length compact state r 0 0
    (bulkSevenTrace parameters r input)
  rw [bulkSevenTrace_flatten] at same
  rw [same]
  have exactFlux := radialNormalizedCovariantKernel_correctedFlux_eq parameters length compact state.val.val r state.val.property 0 0
    (bulkSevenTrace parameters r input) (physicalBulkFlux parameters lower positive r field) flux.1 flux.2
    (bulkSevenTrace_derivative parameters r input 3 1 law.scalarDerivative)
  simpa only [bulkSevenTrace_flatten] using exactFlux

variable (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)

/-- The actual corrected flux of the SAME full solution is exactly the mean-free angular primitive of x. -/
theorem sharedCorrectedP_trace :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      originalPhysicalSlice parameters lower positive bounded.le
        (actualCorrectedPAction parameters length compact lower positive bounded state
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)) radius =
      physicalBulkFlux parameters lower positive (collarRadius lower positive bounded.le radius)
        (collectRadial lower (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution) radius) := by
  let seven := fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution
  filter_upwards [fullStrongSevenInput_compatible_ae parameters length lower lengthPositive positive bounded.le data solution,
    originalPhysicalSlice_action parameters lower positive bounded.le
      (originalCorrectedPKernel parameters length compact state) (originalCorrectedPKernel_regular parameters length compact state) seven]
      with radius compatible same
  have law := originalCorrectedP_bulkTrace parameters length compact lower positive state
    (collarRadius lower positive bounded.le radius) (collectRadial lower seven radius) compatible
  rw [map_smul] at law
  exact same.trans law

/-- Coefficient form of Rp=x, with no angular mode removed beyond the original outer P. -/
theorem sharedCorrectedP_angularCoefficients :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive
        (bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 7)
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)) radius mode =
      (Complex.I * (mode.1 : ℂ)) • lowRhoPhysicalCoefficient parameters lower positive
        (actualCorrectedPAction parameters length compact lower positive bounded state
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)) radius mode := by
  let seven := fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution
  filter_upwards [sharedCorrectedP_trace parameters length compact lower positive bounded state lengthPositive data solution,
    fullStrongSevenInput_compatible_ae parameters length lower lengthPositive positive bounded.le data solution,
    sharedFull_inputFidelity parameters length lower positive bounded.le lengthPositive data solution,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (actualCorrectedPAction parameters length compact lower positive bounded state seven),
    lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) (0 : Fin 7) seven]
      with radius same compatible inputSame outputSame projected
  intro mode
  have derivative := (physicalBulkFlux_laws parameters lower positive
    (collarRadius lower positive bounded.le radius) (collectRadial lower seven radius) compatible).2 mode
  rw [← same,outputSame mode] at derivative
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  have value := congrArg (fun v : ComplexEuclidean 1 => v 0) derivative
  rw [inputSame mode 0] at value
  rw [projected mode]
  simpa [matrixUnit_apply,operatorBasis] using value

/-- Genuine classical Rp=x for the same reconstructed corrected radial flux. -/
theorem sharedCorrectedP_classical_angular
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle => (curves.correctedP parameters length compact lower positive bounded state).fullField bounded (radius,angle,axial))
      ((curves.bulkUnit (0 : Fin 1) (0 : Fin 7)).fullField bounded (radius,polar,axial)) polar :=
  samePhysical_angularDerivative _ _ bounded
    (sharedCorrectedP_angularCoefficients parameters length compact lower positive bounded state lengthPositive data solution)
    radius inside polar axial

end Grad.ActualPolarFlux
