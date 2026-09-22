import SBT9PhysicalBoundary

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.FlatSourceProjection Grad.NonlinearProduct Grad.NonlinearQuotientBounds
open Grad.BoundaryTrace Grad.CompatibleCompletion Grad.NonlinearRange Grad.SourceCollar

/-- Uniform closed-disk majorants for the genuine cellwise angular
derivative justify differentiation of the complete axial Fourier series. -/
theorem coreBoundary_hasDerivAt {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (axialAngle polarAngle : ℝ) :
    HasDerivAt (fun theta : ℝ => coreValue field (boundaryDiskPoint (theta : CellCircle)) axialAngle)
      (coreValue (rotationCore parameters field) (boundaryDiskPoint (polarAngle : CellCircle)) axialAngle) polarAngle := by
  let term (cell : ℤ) (theta : ℝ) := axialPhase cell axialAngle •
    (field.val cell).value (boundaryDiskPoint (theta : CellCircle))
  let derivativeTerm (cell : ℤ) (theta : ℝ) := axialPhase cell axialAngle •
    ((rotationCore parameters field).val cell).value (boundaryDiskPoint (theta : CellCircle))
  have derivativeNorms : Summable (fun cell : ℤ => ‖((rotationCore parameters field).val cell).value‖) := by
    simpa only [pow_zero, one_mul, closedDerivative_zero_order] using
      originalClosedDerivative_frequency_summable parameters (rotationCore parameters field)
        emptyCartesianWord 0
  have each (cell : ℤ) (theta : ℝ) : HasDerivAt (term cell) (derivativeTerm cell theta) theta :=
    (closedBoundary_hasDerivAt (field.val cell) theta).const_smul (axialPhase cell axialAngle)
  have bound (cell : ℤ) (theta : ℝ) :
      ‖derivativeTerm cell theta‖ ≤ ‖((rotationCore parameters field).val cell).value‖ := by
    dsimp only [derivativeTerm]
    rw [norm_smul, norm_axialPhase, one_mul]
    exact ContinuousMap.norm_coe_le_norm _ _
  have initial : Summable (fun cell : ℤ => term cell 0) :=
    coreValue_summable field (boundaryDiskPoint ((0 : ℝ) : CellCircle)) axialAngle
  exact hasDerivAt_tsum derivativeNorms each bound initial polarAngle

/-- Literal derivative of the repaired physical F0, not a named independent
boundary coordinate and not the derivative of a radius-divided extension. -/
theorem sourceForce_physical_outer_hasDerivAt (parameters : PhaseParameters) (L epsilon : ℝ)
    (state : ACore parameters 3) (source : CartesianSourceCore parameters)
    (axialAngle polarAngle : ℝ) :
    HasDerivAt
      (actualAnnularBulkSource parameters L epsilon state 1 (by norm_num) axialAngle source).F0
      (coreValue (rotationCore parameters (tangentialBoundaryCore parameters source.1))
        (boundaryDiskPoint (polarAngle : CellCircle)) axialAngle 0) polarAngle := by
  let projection : ComplexEuclidean 1 →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0
  have derivative := (projection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt polarAngle
    (coreBoundary_hasDerivAt parameters (tangentialBoundaryCore parameters source.1) axialAngle polarAngle)
  have equality : (fun theta : ℝ => projection (coreValue (tangentialBoundaryCore parameters source.1)
      (boundaryDiskPoint (theta : CellCircle)) axialAngle)) =
      (actualAnnularBulkSource parameters L epsilon state 1 (by norm_num) axialAngle source).F0 :=
    funext (sourceForce_physical_outer parameters L epsilon state source axialAngle)
  change HasDerivAt (fun theta : ℝ => projection (coreValue (tangentialBoundaryCore parameters source.1)
    (boundaryDiskPoint (theta : CellCircle)) axialAngle))
    (projection (coreValue (rotationCore parameters (tangentialBoundaryCore parameters source.1))
      (boundaryDiskPoint (polarAngle : CellCircle)) axialAngle)) polarAngle at derivative
  rw [equality] at derivative
  exact derivative

theorem sourceRotation_physical_outer (parameters : PhaseParameters) (L epsilon : ℝ)
    (state : ACore parameters 3) (source : CartesianSourceCore parameters)
    (axialAngle polarAngle : ℝ) :
    coreValue (rotationCore parameters (tangentialBoundaryCore parameters source.1))
      (boundaryDiskPoint (polarAngle : CellCircle)) axialAngle 0 =
      deriv (actualAnnularBulkSource parameters L epsilon state 1 (by norm_num) axialAngle source).F0 polarAngle :=
  (sourceForce_physical_outer_hasDerivAt parameters L epsilon state source axialAngle polarAngle).deriv.symm

end Grad.SourceBoundaryTrace
