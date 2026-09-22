import AKAR17ActualMatrixCircleProduct
import AKAR16LiteralMeanFreeScalar

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.AnnularReconstruction
open Grad.BoundaryLift Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.ActualSmoothPhysicalField Grad.ActualPhysicalField
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.Constraints Grad.OriginalFlatAxisDecay

variable {dimension : ℕ}
def originalCoreCircle (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : RadialPoint) (angles : ℝ × ℝ) : ComplexEuclidean dimension :=
  coreValue field (Grad.SourceCollarDivision.polarClosedPoint radius.val angles.1 radius.property.1 radius.property.2) angles.2

theorem originalCoreCircle_continuous (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : RadialPoint) : Continuous (originalCoreCircle parameters field radius) := by
  have norms : Summable (fun cell : ℤ => ‖(field.val cell).value‖) := by
    simpa only [pow_zero,one_mul,closedDerivative_zero_order] using
      originalClosedDerivative_frequency_summable parameters field emptyCartesianWord 0
  have point : Continuous (fun angles : ℝ × ℝ => Grad.SourceCollarDivision.polarClosedPoint radius.val angles.1 radius.property.1 radius.property.2) :=
    (polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_fst)).subtype_mk _
  have phase (cell : ℤ) (angle : ℝ) : axialPhase cell angle = cellExponential cell angle :=
    (axialPhase_eq_character cell angle).trans (cellCharacter_coe cell angle)
  unfold originalCoreCircle coreValue
  simp_rw [phase]
  apply continuous_tsum
    (fun cell => ((cellExponential_smooth cell).continuous.comp continuous_snd).smul ((field.val cell).value.continuous.comp point)) norms
  intro cell angles
  change ‖cellExponential cell angles.2 • (field.val cell).value
    (Grad.SourceCollarDivision.polarClosedPoint radius.val angles.1 radius.property.1 radius.property.2)‖ ≤ _
  rw [norm_smul,cellExponential_norm,one_mul]
  exact ContinuousMap.norm_coe_le_norm _ _

theorem originalCoreCircle_axialCoefficient (parameters : PhaseParameters) (field : ACore parameters dimension)
    (radius : RadialPoint) (polar : ℝ) (cell : ℤ) :
    angularCoefficient (fun axial => originalCoreCircle parameters field radius (polar,axial)) cell =
      (field.val cell).value (Grad.SourceCollarDivision.polarClosedPoint radius.val polar radius.property.1 radius.property.2) := by
  let point := Grad.SourceCollarDivision.polarClosedPoint radius.val polar radius.property.1 radius.property.2
  apply angularCoefficient_of_axialSeries (fun cell => (field.val cell).value point)
    (Grad.Constraints.Gauges.originalValueNorm_summable parameters field point)
  intro axial
  exact (coreValue_summable field point axial).hasSum.congr_fun (fun cell => by
    change cellExponential cell axial • _ = axialPhase cell axial • _
    rw [← (axialPhase_eq_character cell axial).trans (cellCharacter_coe cell axial)])

def originalSmoothCircleTrace (parameters : PhaseParameters) (field : GradeCore parameters dimension 4)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.toCore.val cell)) (radius : RadialPoint) (rotated : Bool) : CellL2 dimension :=
  originalA4CircleTrace parameters (aGradeEta parameters field)
    (Grad.OriginalFlatAxisDecay.Consumer.originalFirstJetFlat_of_core parameters field zeroJets) radius rotated

theorem originalSmoothCircleTrace_represents (parameters : PhaseParameters) (field : GradeCore parameters dimension 4)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.toCore.val cell)) (radius : RadialPoint) (rotated : Bool) :
    OriginalCircleRepresents parameters radius (originalSmoothCircleTrace parameters field zeroJets radius rotated)
      (originalCoreCircle parameters (if rotated then rotationCore parameters field.toCore else field.toCore) radius) := by
  intro mode
  rw [originalSmoothCircleTrace,originalA4CircleTrace_originalCoefficient]
  unfold doubleCoefficient
  simp_rw [originalCoreCircle_axialCoefficient]
  apply congrArg (fun function => angularCoefficient function mode.1)
  funext angle
  cases rotated
  · exact congrArg (fun function : C(ClosedDisk,ComplexEuclidean dimension) => function
      (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2))
      (completedOriginalCell_core parameters (by omega) mode.2 field)
  · exact originalRotationAt_core parameters mode.2 _ field

theorem originalSmoothCircleTrace_bound (parameters : PhaseParameters) (field : GradeCore parameters dimension 4)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.toCore.val cell)) (radius : RadialPoint) (rotated : Bool) :
    ‖originalSmoothCircleTrace parameters field zeroJets radius rotated‖ ≤
      flatDecayConstant * radius.val^(3/2:ℝ) * ‖field‖ := by
  simpa only [originalSmoothCircleTrace,aGradeEta_norm] using
    originalA4CircleTrace_bound parameters (aGradeEta parameters field)
      (Grad.OriginalFlatAxisDecay.Consumer.originalFirstJetFlat_of_core parameters field zeroJets) radius rotated

end Grad.OriginalKernelRetainedDecay
