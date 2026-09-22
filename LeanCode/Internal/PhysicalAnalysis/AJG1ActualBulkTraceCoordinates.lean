import AJC19OriginalSharedInverseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.AnnularVariational Grad.SourceCollarDivision
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.BoundaryKernelAction
open Grad.AnnularCrossMaps Grad.PhaseAlgebra Grad.BoundaryTrace Grad.AnnularKernelL2

/-- The kernel reindexing preserves the coefficient envelope. Its boundary
phase differs from the original radial phase by at most gamma. -/
theorem radialBoundaryPhase_gap (parameters : PhaseParameters) (radius : RadialPoint) (cell : ℤ) :
    boundaryPhase (radialKernelParameters parameters radius) cell -
      radialPhase parameters radius.val cell ≤ parameters.gamma := by
  let frequency := cellFrequency cell
  have frequencyNonnegative : 0 ≤ frequency := (cellFrequency_pos cell).le
  have fullLower : frequency ≤ Real.sqrt (1 + frequency ^ 2) := by
    apply (Real.le_sqrt frequencyNonnegative (by positivity)).2
    linarith
  have radialNonnegative : 0 ≤ radius.val * frequency := mul_nonneg radius.property.1 frequencyNonnegative
  have radialUpper : Real.sqrt (1 + frequency ^ 2 * radius.val ^ 2) ≤ radius.val * frequency + 1 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · linarith
    · nlinarith only [radialNonnegative]
  have gap := mul_le_mul_of_nonneg_left
    (show (1 - radius.val) * frequency - Real.sqrt (1 + frequency ^ 2) +
      Real.sqrt (1 + frequency ^ 2 * radius.val ^ 2) ≤ 1 by linarith)
    parameters.gamma_pos.le
  dsimp [boundaryPhase, radialPhase, radialKernelParameters]
  dsimp [frequency] at gap
  nlinarith only [gap]

/-- Exact conversion of stored original bulk coefficients to the already
accepted negative-half trace coordinates at this same radius. -/
def bulkNegativeFactor (parameters : PhaseParameters) (radius : RadialPoint) (mode : ℤ × ℤ) : ℝ :=
  negativeTraceWeight (radialKernelParameters parameters radius) 0 0 mode /
    Real.exp (radialPhase parameters radius.val mode.2)

theorem bulkNegativeFactor_positive (parameters : PhaseParameters) (radius : RadialPoint) (mode : ℤ × ℤ) :
    0 < bulkNegativeFactor parameters radius mode :=
  div_pos (negativeTraceWeight_pos _ _ _ _) (Real.exp_pos _)

theorem bulkNegativeFactor_bound (parameters : PhaseParameters) (radius : RadialPoint) (mode : ℤ × ℤ) :
    bulkNegativeFactor parameters radius mode ≤ Real.exp parameters.gamma := by
  have frequencyOne : 1 ≤ Real.sqrt (Grad.AnnularVariational.annularFrequency mode.1 mode.2) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (annularFrequency_one_le mode.1 mode.2)
  have phase := Real.exp_le_exp.mpr (radialBoundaryPhase_gap parameters radius mode.2)
  rw [Real.exp_sub] at phase
  unfold bulkNegativeFactor
  rw [negativeTraceWeight_base, ← boundaryPhase_at_outer]
  have first := div_le_self (Real.exp_pos (boundaryPhase (radialKernelParameters parameters radius) mode.2)).le frequencyOne
  exact (div_le_div_of_nonneg_right first (Real.exp_pos _).le).trans phase

def bulkNegativeLinear (parameters : PhaseParameters) (radius : RadialPoint) (dimension : ℕ) :
    CellL2 dimension →ₗ[ℂ] NegativeTrace (radialKernelParameters parameters radius) 0 0 dimension where
  toFun field := ⟨fun mode => (bulkNegativeFactor parameters radius mode : ℂ) • field mode,
    (Real.exp parameters.gamma • field).property.mono' (fun mode => by
      change ‖(bulkNegativeFactor parameters radius mode : ℂ) • field mode‖ ≤ ‖Real.exp parameters.gamma • field mode‖
      rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (bulkNegativeFactor_positive parameters radius mode).le,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (bulkNegativeFactor_bound parameters radius mode) (norm_nonneg _))⟩
  map_add' first second := by
    apply lp.ext
    funext mode
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply lp.ext
    funext mode
    change (bulkNegativeFactor parameters radius mode : ℂ) • (scalar • field mode) =
      scalar • ((bulkNegativeFactor parameters radius mode : ℂ) • field mode)
    exact smul_comm _ _ _

theorem bulkNegativeLinear_bound (parameters : PhaseParameters) (radius : RadialPoint) (dimension : ℕ)
    (field : CellL2 dimension) :
    ‖bulkNegativeLinear parameters radius dimension field‖ ≤ Real.exp parameters.gamma * ‖field‖ := by
  have point : ‖bulkNegativeLinear parameters radius dimension field‖ ≤ ‖Real.exp parameters.gamma • field‖ := by
    apply lp.norm_mono (by norm_num)
    intro mode
    change ‖(bulkNegativeFactor parameters radius mode : ℂ) • field mode‖ ≤ ‖Real.exp parameters.gamma • field mode‖
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (bulkNegativeFactor_positive parameters radius mode).le,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_right (bulkNegativeFactor_bound parameters radius mode) (norm_nonneg _)
  simpa only [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] using point

def bulkNegativeLift (parameters : PhaseParameters) (radius : RadialPoint) (dimension : ℕ) :
    CellL2 dimension →L[ℂ] NegativeTrace (radialKernelParameters parameters radius) 0 0 dimension :=
  (bulkNegativeLinear parameters radius dimension).mkContinuous (Real.exp parameters.gamma)
    (bulkNegativeLinear_bound parameters radius dimension)

theorem bulkNegativeLift_apply (parameters : PhaseParameters) (radius : RadialPoint) (dimension : ℕ)
    (field : CellL2 dimension) (mode : ℤ × ℤ) :
    bulkNegativeLift parameters radius dimension field mode = (bulkNegativeFactor parameters radius mode : ℂ) • field mode := rfl

/-- No change to the physical Fourier coefficient or analytic width occurs. -/
theorem bulkNegativeLift_coefficient (parameters : PhaseParameters) (radius : RadialPoint) (dimension : ℕ)
    (field : CellL2 dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters radius) 0 0
      (bulkNegativeLift parameters radius dimension field) mode =
      (Real.exp (radialPhase parameters radius.val mode.2) : ℂ)⁻¹ • field mode := by
  rw [negativeTraceCoefficient, bulkNegativeLift_apply, smul_smul]
  congr 1
  unfold bulkNegativeFactor
  push_cast
  field_simp [(negativeTraceWeight_pos (radialKernelParameters parameters radius) 0 0 mode).ne',
    (Real.exp_pos (radialPhase parameters radius.val mode.2)).ne']

end Grad.AnnularPhysicalReconstruction
