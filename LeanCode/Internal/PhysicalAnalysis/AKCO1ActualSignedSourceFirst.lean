import AKBS4SameSourceFirstDilation
import AKCB9ActualCellDisplacementCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
namespace Grad.ActualOriginalSourceFirst
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.CartesianStartup
open Grad.ActualScalarWeakEquations Grad.NonlinearQuotientBounds Grad.SpatialDilation Grad.WeightedJets

/-- The SAME original source with a signed scaled axial derivative; the
accepted core time derivative preserves the original analytic width. -/
def originalSignedAxialCore {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (L ell : ℝ) : ℕ → ACore parameters dimension :=
  Nat.rec field (fun _ previous => ((ell/L : ℝ) : ℂ) • timeDerivativeCore parameters previous)

theorem originalSignedAxialCore_val {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (L ell : ℝ) (power : ℕ) (cell : ℤ) :
    (originalSignedAxialCore parameters field L ell power).val cell =
      startupAxialFrequency L ell cell ^ power • field.val cell := by
  induction power with
  | zero => simp only [pow_zero,one_smul]; rfl
  | succ power induction =>
    change ((ell/L : ℝ) : ℂ) • (((cell : ℂ)*Complex.I) •
      (originalSignedAxialCore parameters field L ell power).val cell) = _
    rw [induction,smul_smul,smul_smul,pow_succ']
    congr 1
    unfold startupAxialFrequency
    push_cast
    ring

theorem originalSignedAxialCore_cell {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (L ell : ℝ) (power : ℕ) (cell : ℤ)
    (point : ClosedDisk) :
    originalCoreCell parameters (originalSignedAxialCore parameters field L ell power) cell point.val =
      startupAxialFrequency L ell cell ^ power • originalCoreCell parameters field cell point.val := by
  rw [originalCoreCell_value,originalCoreCell_value,originalSignedAxialCore_val,
    closedJet_value_smul,ContinuousMap.smul_apply]

/-- First graphs at every signed cell power, using the genuine source's
stored smooth core and the existing first-graph dilation. -/
def originalSignedAxialFirst {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (L : ℝ) (scale : Scale) (power : ℕ) : StartupFirst dimension :=
  scaledOriginalSourceFirst parameters (originalSignedAxialCore parameters field L scale.val power) scale

end Grad.ActualOriginalSourceFirst
