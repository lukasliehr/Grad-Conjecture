import AJG9OriginalPhysicalSlice

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.PhaseAlgebra
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse

/-- Actual seven original physical inputs, including the once-only sources. -/
def physicalBulkSevenTrace (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : RadialPoint) (field : CellL2 7) : SevenSlotTrace (radialKernelParameters parameters radius) 0 0 :=
  bulkSevenTrace parameters radius ((lowStorageWeight lower positive radius.val : ℂ)⁻¹ • field)

theorem physicalBulkSevenTrace_coefficient (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : RadialPoint) (field : CellL2 7) (slot : Fin 7) (mode : ℤ × ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters radius) 0 0
      (physicalBulkSevenTrace parameters lower positive radius field slot) mode 0 =
      (lowRhoPhysicalWeight parameters lower positive radius.val mode : ℂ)⁻¹ * field mode slot := by
  rw [physicalBulkSevenTrace, bulkSevenTrace_coefficient]
  change (Real.exp (radialPhase parameters radius.val mode.2) : ℂ)⁻¹ *
    ((lowStorageWeight lower positive radius.val : ℂ)⁻¹ * field mode slot) = _
  simp only [lowRhoPhysicalWeight, Complex.ofReal_mul, mul_inv_rev, mul_assoc]

/-- Genuine angular derivative, the two original gauges and both algebraic
physical force rows for one and the same original covariant field. -/
structure OriginalSliceLaws (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (radius : RadialPoint)
    (input : SevenSlotTrace (radialKernelParameters parameters radius) 0 0)
    (covariant rotated : NegativeTrace (radialKernelParameters parameters radius) 0 0 3) : Prop where
  angular : IsAngularDerivative (radialKernelParameters parameters radius) 0 0 covariant rotated
  gauges : radialPhysicalGaugeMeans parameters L compact state.val radius 0 0 covariant = 0
  firstForce : -forceCoordinateTrace (radialKernelParameters parameters radius) 0 0 1 rotated -
    (2 : ℂ) • forceCoordinateTrace (radialKernelParameters parameters radius) 0 0 0 covariant +
    fullNegativeKernelAction (radialKernelParameters parameters radius) 0 0
      (radialForceKernel parameters L compact state.val radius 0 0) covariant + input 1 = input 4
  thirdForce : forceCoordinateTrace (radialKernelParameters parameters radius) 0 0 2 rotated +
    forceMeanFreeTrace (radialKernelParameters parameters radius) 0 0
      (fullNegativeKernelAction (radialKernelParameters parameters radius) 0 0
        (radialForceKernel parameters L compact state.val radius 1 0) covariant) -
    (L : ℂ)⁻¹ • input 2 = input 6

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < L)
    (state : AnnularReconstructionState parameters L compact)

theorem physicalBulkLaws (radius : RadialPoint) (field : CellL2 7) (compatible : BulkSevenCompatibility field) :
    OriginalSliceLaws parameters L compact state radius
      (physicalBulkSevenTrace parameters lower positive radius field)
      (physicalBulkLift parameters lower positive radius 3 (bulkCovariant parameters L compact state radius field))
      (physicalBulkLift parameters lower positive radius 3 (bulkRotatedCovariant parameters L compact state radius field)) := by
  rw [physicalBulkLift_action, physicalBulkLift_action]
  let scaled := (lowStorageWeight lower positive radius.val : ℂ)⁻¹ • field
  have law : BulkSevenCompatibility scaled := compatible.smul _ _
  have force := bulkCovariant_forceRows parameters L compact state radius scaled law
  exact ⟨bulkCovariant_genuineAngular parameters L compact state radius scaled law,
    bulkCovariant_gauged parameters L compact state radius scaled law, force.1, force.2⟩

/-- All premises of the physical force/gauge reconstruction are discharged
for the actual shared datum and actual coupled solution, with exact unweighting. -/
theorem sharedFull_originalSliceLaws (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      OriginalSliceLaws parameters L compact state (collarRadius lower positive bounded radius)
        (physicalBulkSevenTrace parameters lower positive (collarRadius lower positive bounded radius)
          (collectRadial lower (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution) radius))
        (originalPhysicalSlice parameters lower positive bounded
          (sharedFullCovariant parameters L compact lower positive bounded lengthPositive state data solution) radius)
        (originalPhysicalSlice parameters lower positive bounded
          (sharedFullRotatedCovariant parameters L compact lower positive bounded lengthPositive state data solution) radius) := by
  filter_upwards [sharedFullCovariant_collected parameters L compact lower positive bounded lengthPositive state data solution,
    sharedFullRotatedCovariant_collected parameters L compact lower positive bounded lengthPositive state data solution,
    fullStrongSevenInput_compatible_ae parameters L lower lengthPositive positive bounded data solution]
    with radius covariant rotated compatible
  unfold originalPhysicalSlice
  rw [covariant, rotated]
  exact physicalBulkLaws parameters L compact lower positive state _ _ compatible

end Grad.AnnularPhysicalReconstruction
