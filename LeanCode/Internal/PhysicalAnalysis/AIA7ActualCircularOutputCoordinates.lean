import AIA6ExactPacketOrthogonality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularVariational
open Grad.AnnularTiltedReference Grad.GaugeCoefficients.Physical.Ledger Grad.ActualBoundaryPrimitives

/-- Literal fixed complex multiplier on the actual high Fourier bulk carrier. -/
def highScalarDiagonal (lower : ℝ) (coefficient : HighAnnularMode → ℂ) (bound : ℝ)
    (nonnegative : 0 ≤ bound) (bounded : ∀ mode, ‖coefficient mode‖ ≤ bound) :
    AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  complexLpTwoMap (fun mode => coefficient mode • ContinuousLinearMap.id ℂ (RadialL2 1 lower))
    bound nonnegative (fun mode field => by
      change ‖coefficient mode • field‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (bounded mode) (norm_nonneg _))

theorem highScalarDiagonal_mode (lower : ℝ) (coefficient : HighAnnularMode → ℂ) (bound : ℝ)
    (nonnegative : 0 ≤ bound) (bounded : ∀ mode, ‖coefficient mode‖ ≤ bound)
    (field : AnnularBulk lower) (mode : HighAnnularMode) :
    highScalarDiagonal lower coefficient bound nonnegative bounded field mode = coefficient mode • field mode := rfl

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

/-- The SAME negative circular high A inverse applied to the homogeneous first row. -/
def circularHighX : annularEnergySpace lower L positive →L[ℂ] AnnularBulk lower :=
  -(highScalarDiagonal lower (fun mode => retainedBInverseMultiplier mode.val) (9 / 5) (by norm_num)
    (fun mode => retainedBInverseMultiplier_norm_le mode.val)).comp
      (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength +
        (2 : ℂ) • (highEnergyRadius lower L positive).comp (bEnergyDecode lower L positive))

def circularHighC : annularEnergySpace lower L positive →L[ℂ] AnnularBulk lower :=
  -(highEnergyCell lower L positive).comp (bEnergyDecode lower L positive)

def circularHighRV : annularEnergySpace lower L positive →L[ℂ] AnnularBulk lower :=
  -(highEnergyAngularRadius lower L positive).comp (bEnergyDecode lower L positive) -
    (2 : ℂ) • (highScalarDiagonal lower (fun mode => angularInverseMultiplier mode.val) 1 (by norm_num)
      (fun mode => angularInverseMultiplier_norm_le mode.val)).comp
        (circularHighX parameters lower L positive lengthPositive widthHalf widthLength)

theorem circularHighX_mode (field : annularEnergySpace lower L positive) (mode : HighAnnularMode) :
    circularHighX parameters lower L positive lengthPositive widthHalf widthLength field mode =
      -retainedBInverseMultiplier mode.val •
        (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field mode +
          (2 : ℂ) • highEnergyRadius lower L positive (bEnergyDecode lower L positive field) mode) := by
  change -(retainedBInverseMultiplier mode.val •
    (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field mode +
      (2 : ℂ) • highEnergyRadius lower L positive (bEnergyDecode lower L positive field) mode)) = _
  rw [neg_smul]

theorem circularHighC_mode (field : annularEnergySpace lower L positive) (mode : HighAnnularMode) :
    circularHighC lower L positive field mode = -highEnergyCell lower L positive (bEnergyDecode lower L positive field) mode := rfl

theorem circularHighRV_mode (field : annularEnergySpace lower L positive) (mode : HighAnnularMode) :
    circularHighRV parameters lower L positive lengthPositive widthHalf widthLength field mode =
      -highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive field) mode -
        (2 : ℂ) • (angularInverseMultiplier mode.val • circularHighX parameters lower L positive lengthPositive widthHalf widthLength field mode) := rfl

include lengthPositive in
/-- The raw circle kernel on the actual source-free physical packet. -/
theorem circularBulk_homogeneous_entry (mode : HighAnnularMode) (radial rotated cell value : ℂ) :
    (circularEliminatedBulkKernel parameters L).entry (0, 0) mode.val
      (radial • operatorBasis 0 + rotated • operatorBasis 1 + ((L : ℂ) * cell) • operatorBasis 2 + value • operatorBasis 3) =
      WithLp.toLp 2 ![-retainedBInverseMultiplier mode.val * (radial + 2 * value),
        -cell, -rotated - 2 * angularInverseMultiplier mode.val * (-retainedBInverseMultiplier mode.val * (radial + 2 * value))] := by
  rw [circularEliminatedBulkKernel_entry_zero]
  have nonzero : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr lengthPositive.ne'
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [circularEliminatedXSymbol, highAngularMultiplier, mode.property, operatorBasis, nonzero]

end Grad.AnnularCircularForm
