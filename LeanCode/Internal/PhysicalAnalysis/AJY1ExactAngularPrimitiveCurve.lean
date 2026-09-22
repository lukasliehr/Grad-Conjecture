import AJU12ExactSameRawPhysicalConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.AnnularSmoothCore Grad.BoundaryKernelAction

/-- The original mean-free inverse of R, acting on the same physical
Hilbert coefficients; its zero angular mode is fixed to zero. -/
def physicalAngularPrimitive (parameters : PhaseParameters) : CellL2 1 →L[ℂ] CellL2 1 :=
  boundedHilbertMultiplier parameters 1 angularInverseMultiplier 1 zero_le_one
    angularInverseMultiplier_norm_le

theorem physicalAngularPrimitive_apply (parameters : PhaseParameters)
    (field : CellL2 1) (mode : ℤ × ℤ) :
    physicalAngularPrimitive parameters field mode = angularInverseMultiplier mode • field mode := rfl

theorem physicalAngularPrimitive_smooth (parameters : PhaseParameters) (lower : ℝ)
    (curve : ℝ → CellL2 1) (smooth : ContDiffOn ℝ ∞ curve (Icc lower 1)) :
    ContDiffOn ℝ ∞ (fun radius => physicalAngularPrimitive parameters (curve radius)) (Icc lower 1) :=
  (physicalAngularPrimitive parameters).restrictScalars ℝ |>.contDiff.comp_contDiffOn smooth

theorem physicalAngularPrimitive_grade (parameters : PhaseParameters)
    (curve : ℕ → ℝ → CellL2 1) (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ)
    (same : curve grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • curve 0 radius mode) :
    physicalAngularPrimitive parameters (curve grade radius) mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        physicalAngularPrimitive parameters (curve 0 radius) mode := by
  rw [physicalAngularPrimitive_apply,physicalAngularPrimitive_apply,same,smul_comm]

theorem physicalAngularPrimitive_R (parameters : PhaseParameters) (field : CellL2 1)
    (meanFree : ∀ cell, field (0, cell) = 0) (mode : ℤ × ℤ) :
    (Complex.I * (mode.1 : ℂ)) • physicalAngularPrimitive parameters field mode = field mode := by
  rw [physicalAngularPrimitive_apply]
  by_cases zero : mode.1 = 0
  · have same : mode = (0, mode.2) := Prod.ext zero rfl
    rw [same,meanFree mode.2]
    simp
  · rw [angularInverseMultiplier,if_neg zero,smul_smul,
      mul_inv_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr zero)),one_smul]

end Grad.AnnularPhysicalFourier
