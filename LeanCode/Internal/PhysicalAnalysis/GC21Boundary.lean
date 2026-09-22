import GC18Consumer
import BT20Completion

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.AnalyticWeights.Calculus Grad.BoundaryTrace

/-- Literal AP3 frequency: the cell variable is n*ell/L, not n. -/
def apBoundaryFrequency (L ell : ℝ) (mode : ℤ × ℤ) : ℝ :=
  Real.sqrt (1 + (mode.1 : ℝ) ^ 2 + ((mode.2 : ℝ) * ell / L) ^ 2)

theorem apBoundaryFrequency_one_le (L ell : ℝ) (mode : ℤ × ℤ) : 1 ≤ apBoundaryFrequency L ell mode := by
  have bound : (1 : ℝ) ≤ 1 + (mode.1 : ℝ) ^ 2 + ((mode.2 : ℝ) * ell / L) ^ 2 := by
    nlinarith [sq_nonneg (mode.1 : ℝ), sq_nonneg ((mode.2 : ℝ) * ell / L)]
  simpa only [Real.sqrt_one, apBoundaryFrequency] using Real.sqrt_le_sqrt bound

theorem apBoundaryFrequency_pos (L ell : ℝ) (mode : ℤ × ℤ) : 0 < apBoundaryFrequency L ell mode :=
  zero_lt_one.trans_le (apBoundaryFrequency_one_le L ell mode)

theorem apBoundaryFrequency_sq (L ell : ℝ) (mode : ℤ × ℤ) :
    apBoundaryFrequency L ell mode ^ 2 = 1 + (mode.1 : ℝ) ^ 2 + ((mode.2 : ℝ) * ell / L) ^ 2 :=
  Real.sq_sqrt (by positivity)

def apBoundaryPhase (sigma gamma ell : ℝ) (cell : ℤ) : ℝ :=
  Grad.AnalyticWeights.phase sigma gamma ell cell

theorem apWeight_boundary (sigma gamma ell : ℝ) (cell : ℤ) (angle : CellCircle) :
    originalWeight sigma gamma ell cell (boundaryDiskPoint angle).val =
      Real.exp (apBoundaryPhase sigma gamma ell cell) := by
  rw [originalWeight, physicalWeight_exp]
  change Real.exp (Grad.AnalyticWeights.phase sigma gamma (ell * ‖boundaryCirclePoint angle‖) cell) = _
  rw [boundaryCirclePoint_norm, mul_one]
  rfl

def apBoundaryWeight (L sigma gamma ell : ℝ) (grade : ℕ) (mode : ℤ × ℤ) : ℝ :=
  Real.exp (apBoundaryPhase sigma gamma ell mode.2) *
    Real.sqrt (apBoundaryFrequency L ell mode ^ (2 * grade - 1))

theorem apBoundaryWeight_pos (L sigma gamma ell : ℝ) (grade : ℕ) (mode : ℤ × ℤ) :
    0 < apBoundaryWeight L sigma gamma ell grade mode :=
  mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 (pow_pos (apBoundaryFrequency_pos L ell mode) _))

/-- Weighted coordinates of the original full-cell AP3 Hilbert space. -/
abbrev APBoundaryGrade (_L _sigma _gamma _ell : ℝ) (dimension _grade : ℕ) :=
  lp (fun _ : ℤ × ℤ => PhysicalValue dimension) 2

def apBoundaryCoefficient {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell dimension grade) (mode : ℤ × ℤ) : PhysicalValue dimension :=
  ((apBoundaryWeight L sigma gamma ell grade mode : ℂ)⁻¹) • field mode

theorem apBoundary_weighted_coefficient {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell dimension grade) (mode : ℤ × ℤ) :
    (apBoundaryWeight L sigma gamma ell grade mode : ℂ) •
      apBoundaryCoefficient L sigma gamma ell grade field mode = field mode :=
  smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (apBoundaryWeight_pos L sigma gamma ell grade mode).ne') _

theorem apBoundary_norm_sq {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell dimension grade) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ, Real.exp (2 * apBoundaryPhase sigma gamma ell mode.2) *
      apBoundaryFrequency L ell mode ^ (2 * grade - 1) *
        ‖apBoundaryCoefficient L sigma gamma ell grade field mode‖ ^ 2 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normFormula
  rw [normFormula]
  congr 1
  funext mode
  rw [← apBoundary_weighted_coefficient L sigma gamma ell grade field mode, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (apBoundaryWeight_pos L sigma gamma ell grade mode)]
  have exponential : Real.exp (2 * apBoundaryPhase sigma gamma ell mode.2) =
      Real.exp (apBoundaryPhase sigma gamma ell mode.2) ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  rw [exponential, apBoundaryWeight]
  simp only [mul_pow, Real.sq_sqrt (pow_nonneg (apBoundaryFrequency_pos L ell mode).le _)]

def apCoreBoundaryCoefficient {dimension : ℕ} (field : ℤ →₀ ClosedJet dimension)
    (mode : ℤ × ℤ) : PhysicalValue dimension :=
  fourierCoeff (fun angle : CellCircle => (field mode.2).value (boundaryDiskPoint angle)) mode.1

/-- Exact completed trace interface, to be constructed on the actual AP2
closure. The one constant is uniform in every cap radius and Fourier cell. -/
def APTraceGoal : Prop :=
  ∀ grade : ℕ, 1 ≤ grade → ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (L sigma gamma ell : ℝ), Admissible L sigma gamma ell → ∀ dimension : ℕ,
      ∃ trace : apGrade L sigma gamma ell dimension grade →L[ℂ]
          APBoundaryGrade L sigma gamma ell dimension grade,
        (∀ core : ℤ →₀ ClosedJet dimension, ∀ mode,
          apBoundaryCoefficient L sigma gamma ell grade (trace (apFiniteInto L sigma gamma ell core)) mode =
            apCoreBoundaryCoefficient core mode) ∧
        ∀ field, ‖trace field‖ ≤ constant * ‖field‖

end Grad.GaugeCoefficients.Physical.WeightedTrace
