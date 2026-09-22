import SM1Cutoff
import COR12CellParseval

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

local instance boundaryPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- State-boundary frequency, not the annular convention. -/
def boundaryFrequency (mode : ℤ × ℤ) : ℝ :=
  Real.sqrt (1 + (mode.1 : ℝ) ^ 2 + (mode.2 : ℝ) ^ 2)

theorem boundaryFrequency_one_le (mode : ℤ × ℤ) : 1 ≤ boundaryFrequency mode := by
  have bound : (1 : ℝ) ≤ 1 + (mode.1 : ℝ) ^ 2 + (mode.2 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (mode.1 : ℝ), sq_nonneg (mode.2 : ℝ)]
  simpa only [Real.sqrt_one, boundaryFrequency] using Real.sqrt_le_sqrt bound

theorem boundaryFrequency_pos (mode : ℤ × ℤ) : 0 < boundaryFrequency mode :=
  lt_of_lt_of_le zero_lt_one (boundaryFrequency_one_le mode)

theorem boundaryFrequency_sq (mode : ℤ × ℤ) :
    boundaryFrequency mode ^ 2 = 1 + (mode.1 : ℝ) ^ 2 + (mode.2 : ℝ) ^ 2 := by
  exact Real.sq_sqrt (by positivity)

/-- The original phase evaluated at radius one. -/
def boundaryPhase (parameters : PhaseParameters) (cell : ℤ) : ℝ :=
  parameters.sigma0 * cellFrequency cell -
    parameters.gamma * (Real.sqrt (1 + cellFrequency cell ^ 2) - 1)

def boundaryWeight (parameters : PhaseParameters) (grade : ℕ) (mode : ℤ × ℤ) : ℝ :=
  Real.exp (boundaryPhase parameters mode.2) *
    Real.sqrt (boundaryFrequency mode ^ (2 * grade - 1))

theorem boundaryWeight_pos (parameters : PhaseParameters) (grade : ℕ) (mode : ℤ × ℤ) :
    0 < boundaryWeight parameters grade mode := by
  exact mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 (pow_pos (boundaryFrequency_pos mode) _))

/-- Weighted coordinates of the literal half-order Hilbert target. -/
abbrev BoundaryGrade (_parameters : PhaseParameters) (Value : Type*)
    [NormedAddCommGroup Value] (_grade : ℕ) := lp (fun _ : ℤ × ℤ => Value) 2

def boundaryCoefficient {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (parameters : PhaseParameters) (grade : ℕ) (field : BoundaryGrade parameters Value grade)
    (mode : ℤ × ℤ) : Value :=
  ((boundaryWeight parameters grade mode : ℂ)⁻¹) • field mode

theorem boundary_weighted_coefficient {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (parameters : PhaseParameters) (grade : ℕ)
    (field : BoundaryGrade parameters Value grade) (mode : ℤ × ℤ) :
    (boundaryWeight parameters grade mode : ℂ) • boundaryCoefficient parameters grade field mode =
      field mode := by
  exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (boundaryWeight_pos parameters grade mode).ne') _

theorem boundary_norm_sq {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (parameters : PhaseParameters) (grade : ℕ) (field : BoundaryGrade parameters Value grade) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ, Real.exp (2 * boundaryPhase parameters mode.2) *
      boundaryFrequency mode ^ (2 * grade - 1) * ‖boundaryCoefficient parameters grade field mode‖ ^ 2 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normFormula
  rw [normFormula]
  congr 1
  funext mode
  rw [← boundary_weighted_coefficient parameters grade field mode, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (boundaryWeight_pos parameters grade mode)]
  have exponential : Real.exp (2 * boundaryPhase parameters mode.2) =
      Real.exp (boundaryPhase parameters mode.2) ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  rw [exponential, boundaryWeight]
  simp only [mul_pow, Real.sq_sqrt (pow_nonneg (boundaryFrequency_pos mode).le _)]

def boundaryCirclePoint (angle : CellCircle) : SpatialPlane :=
  WithLp.toLp 2 ![(AddCircle.toCircle angle : ℂ).re, (AddCircle.toCircle angle : ℂ).im]

theorem boundaryCirclePoint_norm (angle : CellCircle) : ‖boundaryCirclePoint angle‖ = 1 := by
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_two]
  change Real.sqrt (‖(AddCircle.toCircle angle : ℂ).re‖ ^ 2 +
    ‖(AddCircle.toCircle angle : ℂ).im‖ ^ 2) = 1
  simp only [Real.norm_eq_abs, sq_abs]
  simpa only [Complex.norm_def, Complex.normSq_apply, pow_two] using
    Circle.norm_coe (AddCircle.toCircle angle)

def boundaryDiskPoint (angle : CellCircle) : ClosedDisk :=
  ⟨boundaryCirclePoint angle, (boundaryCirclePoint_norm angle).le⟩

/-- The actual angular Fourier coefficient of the original cell coefficient
at the physical unit circle. Both circle measures are probability Haar. -/
def originalBoundaryCoefficient {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  fourierCoeff (fun angle : CellCircle => (field.1 mode.2).value (boundaryDiskPoint angle)) mode.1

/-- Literal N21, stated first on the common original smooth core. -/
def BoundaryTraceGoal : Prop :=
  ∀ grade : ℕ, 1 ≤ grade → ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ dimension (parameters : PhaseParameters) (field : ACore parameters dimension),
      Summable (fun mode : ℤ × ℤ => Real.exp (2 * boundaryPhase parameters mode.2) *
        boundaryFrequency mode ^ (2 * grade - 1) * ‖originalBoundaryCoefficient parameters field mode‖ ^ 2) ∧
      (∑' mode : ℤ × ℤ, Real.exp (2 * boundaryPhase parameters mode.2) *
        boundaryFrequency mode ^ (2 * grade - 1) * ‖originalBoundaryCoefficient parameters field mode‖ ^ 2) ≤
        constant * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2

end Grad.BoundaryTrace
