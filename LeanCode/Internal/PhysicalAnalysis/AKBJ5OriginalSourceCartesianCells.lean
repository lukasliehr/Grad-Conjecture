import AKBJ3SameGlobalXiFidelityAndMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.ActualScalarWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarFullSource
open Grad.BoundaryTrace Grad.SourceCollar Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.ActualCartesianDescent Grad.PDEBootstrap Grad.NonlinearRange Grad.Constraints.Gauges

/-- Existing smooth extension of the literal original source cell. Its value on the disk is unchanged. -/
def originalCoreCell {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (cell : ℤ) : SpatialPlane → ComplexEuclidean dimension :=
  smoothClosedExtension (field.val cell)

theorem originalCoreCell_smooth {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (cell : ℤ) : ContDiff ℝ ∞ (originalCoreCell parameters field cell) :=
  smoothClosedExtension_smooth (field.val cell)

theorem originalCoreCell_value {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (cell : ℤ) (point : ClosedDisk) : originalCoreCell parameters field cell point.val = (field.val cell).value point :=
  smoothClosedExtension_value (field.val cell) point

/-- Dimension-generic actual source cell integrability on the whole original disk. -/
theorem originalCoreCell_integrable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (cell : ℤ) : IntegrableOn (originalCoreCell parameters field cell) openUnitDisk := by
  have integrable : IntegrableOn (originalCoreCell parameters field cell) (Metric.closedBall (0 : SpatialPlane) 1) :=
    (originalCoreCell_smooth parameters field cell).continuous.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  apply integrable.mono_set
  intro point inside
  simpa only [Metric.mem_closedBall,dist_zero_right] using (show ‖point‖ ≤ 1 from inside.le)

/-- Full original axial Fourier series identifies exactly this source cell at every disk point. -/
theorem originalCoreCell_axialCoefficient {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (cell : ℤ) (point : ClosedDisk) :
    angularCoefficient (fun axial => sourceCoreValue field point axial) cell = originalCoreCell parameters field cell point.val := by
  rw [originalCoreCell_value]
  apply angularCoefficient_of_axialSeries _ (originalValueNorm_summable parameters field point)
  intro axial
  have sum := (coreValue_summable field point axial).hasSum
  apply sum.congr_fun
  intro sourceCell
  congr 1
  exact ((axialPhase_eq_character sourceCell axial).trans (cellCharacter_coe sourceCell axial)).symm

/-- The exact polar source in AM18--20 has this SAME Cartesian source cell. -/
theorem originalCoreCell_polarCoefficient {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (cell : ℤ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (polar : ℝ) :
    angularCoefficient (fun axial => corePolarValue parameters field radius nonnegative bounded (polar,axial)) cell =
      originalCoreCell parameters field cell (polarPlane (radius,polar)) := by
  have value := originalCoreCell_value parameters field cell (Grad.SourceCollarDivision.polarClosedPoint radius polar nonnegative bounded)
  have same : (Grad.SourceCollarDivision.polarClosedPoint radius polar nonnegative bounded).val = polarPlane (radius,polar) := by
    rfl
  rw [same] at value
  exact (corePolarValue_axialCoefficient parameters field radius nonnegative bounded polar cell).trans value.symm

end Grad.ActualScalarWeakEquations
