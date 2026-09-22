import AKDR1ActualScalarRecoveryNorm
import ANS5NativeKernelBound
import AKBZ6OriginalPureEndpointNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints
open Grad.Constraints.Gauges Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Envelope Grad.SourceCollarCoefficients
open Grad.ActualAngularInverse Grad.OriginalCartesianTameEstimate

/-- At unit physical scale, the accepted AP row is the literal original row. -/
theorem originalRow_eq_unitAP {dimension grade : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (field : ClosedJet dimension) :
    cellGradeRowLinear (grade := grade) parameters cell field =
      apRowLinear (grade := grade) 1 parameters.sigma0 parameters.gamma 1 cell field := by
  rw [originalWeightedRow_mass,apRowLinear_eq_mass,unit_scaledCellWeight]
  rfl

theorem originalAngularKernel_row_bound {dimension grade : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ angle ∈ Icc (0 : ℝ) (2*Real.pi), ‖weight angle‖ ≤ bound)
    (field : ClosedJet dimension) :
    ‖cellGradeRowLinear (grade := grade) parameters cell (kernelRotationJet weight smooth field)‖ ≤
      (bound * orthogonalGradeConstant grade) * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  rw [originalRow_eq_unitAP,originalRow_eq_unitAP]
  exact apKernel_row_bound 1 parameters.sigma0 parameters.gamma 1 cell weight smooth bound nonnegative bounded field

/-- The already constructed angular integral applied to every original
closed jet, with unchanged Fourier cells and analytic width. -/
def originalAngularKernelCore {dimension : ℕ} (parameters : PhaseParameters)
    (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ angle ∈ Icc (0 : ℝ) (2*Real.pi), ‖weight angle‖ ≤ bound)
    (field : ACore parameters dimension) : ACore parameters dimension :=
  ⟨fun cell => kernelRotationJet weight smooth (field.val cell),by
    intro grade
    let majorant := ((bound * orthogonalGradeConstant grade : ℝ) : ℂ) •
      cartesianGradeCoordinates parameters grade field
    apply (lp.memℓp majorant).mono'
    intro cell
    change ‖cellGradeRowLinear (grade := grade) parameters cell (kernelRotationJet weight smooth (field.val cell))‖ ≤
      ‖((bound * orthogonalGradeConstant grade : ℝ) : ℂ) •
        cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg
      (mul_nonneg nonnegative (orthogonalGradeConstant_nonnegative grade))]
    exact originalAngularKernel_row_bound parameters cell weight smooth bound nonnegative bounded (field.val cell)⟩

theorem originalAngularKernelCore_bound {dimension : ℕ} (parameters : PhaseParameters)
    (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ angle ∈ Icc (0 : ℝ) (2*Real.pi), ‖weight angle‖ ≤ bound)
    (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (originalAngularKernelCore parameters weight smooth bound nonnegative bounded field) ≤
      (bound * orthogonalGradeConstant grade) * originalGradeNorm grade field := by
  unfold originalGradeNorm
  rw [ofCoreLinear_norm_coordinates,ofCoreLinear_norm_coordinates]
  calc
    _ ≤ ‖((bound * orthogonalGradeConstant grade : ℝ) : ℂ) •
        cartesianGradeCoordinates parameters grade field‖ := by
      apply lp.norm_mono (by norm_num)
      intro cell
      change ‖cellGradeRowLinear (grade := grade) parameters cell (kernelRotationJet weight smooth (field.val cell))‖ ≤
        ‖((bound * orthogonalGradeConstant grade : ℝ) : ℂ) •
          cellGradeRowLinear (grade := grade) parameters cell (field.val cell)‖
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg
        (mul_nonneg nonnegative (orthogonalGradeConstant_nonnegative grade))]
      exact originalAngularKernel_row_bound parameters cell weight smooth bound nonnegative bounded (field.val cell)
    _ = _ := by
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg
        (mul_nonneg nonnegative (orthogonalGradeConstant_nonnegative grade))]

end Grad.OriginalCoreRealization
