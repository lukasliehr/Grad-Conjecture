import AJG3LiteralSevenBulkTraces
import AHS16OriginalRadiusForceGaugeConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.PhaseAlgebra Grad.AnnularKernelL2

/-- Exactly the support and genuine angular relations of the original seven
physical inputs; no coefficient or inverse regularity is assumed here. -/
structure BulkSevenCompatibility (field : CellL2 7) : Prop where
  massMean : ∀ cell : ℤ, field (0, cell) 0 = 0
  scalarMean : ∀ cell : ℤ, field (0, cell) 3 = 0
  scalarDerivative : ∀ mode : ℤ × ℤ, field mode 1 = (Complex.I * (mode.1 : ℂ)) * field mode 3
  sourceDerivative : ∀ mode : ℤ × ℤ, field mode 5 = (Complex.I * (mode.1 : ℂ)) * field mode 4
  cellMean : ∀ cell : ℤ, field (0, cell) 2 = 0
  sourceTwoMean : ∀ cell : ℤ, field (0, cell) 6 = 0

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (radius : RadialPoint)

def bulkCovariant : CellL2 7 →L[ℂ] CellL2 3 :=
  bulkKernelAction parameters 0 radius (radialNormalizedCovariantKernel parameters L compact state.val radius state.property)

def bulkRotatedCovariant : CellL2 7 →L[ℂ] CellL2 3 :=
  bulkKernelAction parameters 0 radius (radialNormalizedRotatedCovariantKernel parameters L compact state.val radius state.property)

theorem bulkCovariant_lift (field : CellL2 7) :
    bulkNegativeLift parameters radius 3 (bulkCovariant parameters L compact state radius field) =
      fullNegativeKernelAction (radialKernelParameters parameters radius) 0 0
        (radialNormalizedCovariantKernel parameters L compact state.val radius state.property)
        (sevenSlotFlatten (radialKernelParameters parameters radius) 0 0 (bulkSevenTrace parameters radius field)) := by
  rw [bulkSevenTrace_flatten]
  exact bulkNegativeLift_kernel parameters radius _ field

theorem bulkRotatedCovariant_lift (field : CellL2 7) :
    bulkNegativeLift parameters radius 3 (bulkRotatedCovariant parameters L compact state radius field) =
      fullNegativeKernelAction (radialKernelParameters parameters radius) 0 0
        (radialNormalizedRotatedCovariantKernel parameters L compact state.val radius state.property)
        (sevenSlotFlatten (radialKernelParameters parameters radius) 0 0 (bulkSevenTrace parameters radius field)) := by
  rw [bulkSevenTrace_flatten]
  exact bulkNegativeLift_kernel parameters radius _ field

/-- SAME full bulk covariant and rotated outputs have their genuine R law. -/
theorem bulkCovariant_genuineAngular (field : CellL2 7) (compatible : BulkSevenCompatibility field) :
    IsAngularDerivative (radialKernelParameters parameters radius) 0 0
      (bulkNegativeLift parameters radius 3 (bulkCovariant parameters L compact state radius field))
      (bulkNegativeLift parameters radius 3 (bulkRotatedCovariant parameters L compact state radius field)) := by
  rw [bulkCovariant_lift, bulkRotatedCovariant_lift]
  exact radialNormalizedCovariantKernel_derivative parameters L compact state.val radius state.property 0 0
    (bulkSevenTrace parameters radius field)
    (bulkSevenTrace_meanFree parameters radius field 0 compatible.massMean)
    (bulkSevenTrace_derivative parameters radius field 3 1 compatible.scalarDerivative)

/-- Both original gauge means vanish for the same reconstructed bulk field. -/
theorem bulkCovariant_gauged (field : CellL2 7) (compatible : BulkSevenCompatibility field) :
    radialPhysicalGaugeMeans parameters L compact state.val radius 0 0
      (bulkNegativeLift parameters radius 3 (bulkCovariant parameters L compact state radius field)) = 0 := by
  rw [bulkCovariant_lift]
  unfold radialNormalizedCovariantKernel
  rw [fullNegativeKernelAction_add, radialPhysicalGaugeMeans_add,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    radialUnknownUKernel_gauged, zero_add]
  exact radialKnownAStarKernel_gauged parameters L compact state.val radius state.firstSmall 0 0
    (bulkSevenTrace parameters radius field)
    (bulkSevenTrace_meanFree parameters radius field 3 compatible.scalarMean)

/-- The first and third physical force rows for the SAME reconstructed bulk
field, with the prescribed F0/RF0/F2 and all original scalar factors. -/
theorem bulkCovariant_forceRows (field : CellL2 7) (compatible : BulkSevenCompatibility field) :
    let covariant := bulkNegativeLift parameters radius 3 (bulkCovariant parameters L compact state radius field)
    let rotated := bulkNegativeLift parameters radius 3 (bulkRotatedCovariant parameters L compact state radius field)
    let input := bulkSevenTrace parameters radius field
    (-forceCoordinateTrace (radialKernelParameters parameters radius) 0 0 1 rotated -
      (2 : ℂ) • forceCoordinateTrace (radialKernelParameters parameters radius) 0 0 0 covariant +
      fullNegativeKernelAction (radialKernelParameters parameters radius) 0 0
        (radialForceKernel parameters L compact state.val radius 0 0) covariant + input 1 = input 4) ∧
    (forceCoordinateTrace (radialKernelParameters parameters radius) 0 0 2 rotated +
      forceMeanFreeTrace (radialKernelParameters parameters radius) 0 0
        (fullNegativeKernelAction (radialKernelParameters parameters radius) 0 0
          (radialForceKernel parameters L compact state.val radius 1 0) covariant) -
      (L : ℂ)⁻¹ • input 2 = input 6) := by
  dsimp only
  rw [bulkCovariant_lift, bulkRotatedCovariant_lift]
  exact radialNormalizedCovariant_force_rows parameters L compact state.val radius state.property 0 0
    (bulkSevenTrace parameters radius field)
    (bulkSevenTrace_meanFree parameters radius field 0 compatible.massMean)
    (bulkSevenTrace_derivative parameters radius field 3 1 compatible.scalarDerivative)
    (bulkSevenTrace_derivative parameters radius field 4 5 compatible.sourceDerivative)
    (bulkSevenTrace_meanFree parameters radius field 2 compatible.cellMean)
    (bulkSevenTrace_meanFree parameters radius field 6 compatible.sourceTwoMean)

end Grad.AnnularPhysicalReconstruction
