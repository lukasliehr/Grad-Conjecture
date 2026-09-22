import AJG10OriginalFullSliceEquations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy

/-- The original mean-free flux p is the unique angular primitive of the
actual shared input x; this includes both high and low sectors. -/
def physicalBulkFlux (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : RadialPoint) (field : CellL2 7) : NegativeTrace (radialKernelParameters parameters radius) 0 0 1 :=
  fullNegativeKernelAction (radialKernelParameters parameters radius) 0 0
    (angularInverseKernel (radialKernelParameters parameters radius) 1)
    (physicalBulkSevenTrace parameters lower positive radius field 0)

theorem physicalBulkFlux_coefficient (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : RadialPoint) (field : CellL2 7) (mode : ℤ × ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters radius) 0 0
      (physicalBulkFlux parameters lower positive radius field) mode 0 =
      angularInverseMultiplier mode * ((lowRhoPhysicalWeight parameters lower positive radius.val mode : ℂ)⁻¹ * field mode 0) := by
  rw [physicalBulkFlux, angularInverseKernel, scalarModeDiagonalKernel_action_coefficient]
  change angularInverseMultiplier mode * negativeTraceCoefficient _ 0 0 _ mode 0 = _
  rw [physicalBulkSevenTrace_coefficient]

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < L)
    (state : AnnularReconstructionState parameters L compact)

theorem physicalBulkFlux_laws (radius : RadialPoint) (field : CellL2 7) (compatible : BulkSevenCompatibility field) :
    IsAngularMeanFree (radialKernelParameters parameters radius) 0 0
      (physicalBulkFlux parameters lower positive radius field) ∧
    IsAngularDerivative (radialKernelParameters parameters radius) 0 0
      (physicalBulkFlux parameters lower positive radius field)
      (physicalBulkSevenTrace parameters lower positive radius field 0) := by
  have law := compatible.smul field (lowStorageWeight lower positive radius.val : ℂ)⁻¹
  exact ⟨angularInverseKernel_action_meanFree _ 0 0 _,
    angularInverseKernel_derivative _ 0 0 _ (bulkSevenTrace_meanFree parameters radius _ 0 law.massMean)⟩

theorem physicalBulk_correctedFlux (radius : RadialPoint) (field : CellL2 7) (compatible : BulkSevenCompatibility field) :
    radialCorrectedFluxTrace parameters L compact state.val radius 0 0
      (physicalBulkLift parameters lower positive radius 3 (bulkCovariant parameters L compact state radius field))
      (physicalBulkSevenTrace parameters lower positive radius field 3) =
      physicalBulkFlux parameters lower positive radius field := by
  have law := compatible.smul field (lowStorageWeight lower positive radius.val : ℂ)⁻¹
  have flux := physicalBulkFlux_laws parameters lower positive radius field compatible
  rw [physicalBulkLift_action, bulkCovariant_lift]
  exact radialNormalizedCovariantKernel_correctedFlux_eq parameters L compact state.val radius state.property 0 0
    (physicalBulkSevenTrace parameters lower positive radius field)
    (physicalBulkFlux parameters lower positive radius field) flux.1 flux.2
    (bulkSevenTrace_derivative parameters radius _ 3 1 law.scalarDerivative)

/-- The SAME completed U returns the actual prescribed free flux p by the
original physical corrected-flux formula, retaining all known-source terms. -/
theorem sharedFull_originalCorrectedFlux (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      radialCorrectedFluxTrace parameters L compact state.val (collarRadius lower positive bounded radius) 0 0
        (originalPhysicalSlice parameters lower positive bounded
          (sharedFullCovariant parameters L compact lower positive bounded lengthPositive state data solution) radius)
        (physicalBulkSevenTrace parameters lower positive (collarRadius lower positive bounded radius)
          (collectRadial lower (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution) radius) 3) =
        physicalBulkFlux parameters lower positive (collarRadius lower positive bounded radius)
          (collectRadial lower (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution) radius) := by
  filter_upwards [sharedFullCovariant_collected parameters L compact lower positive bounded lengthPositive state data solution,
    fullStrongSevenInput_compatible_ae parameters L lower lengthPositive positive bounded data solution]
    with radius covariant compatible
  unfold originalPhysicalSlice
  rw [covariant]
  exact physicalBulk_correctedFlux parameters L compact lower positive state _ _ compatible

end Grad.AnnularPhysicalReconstruction
