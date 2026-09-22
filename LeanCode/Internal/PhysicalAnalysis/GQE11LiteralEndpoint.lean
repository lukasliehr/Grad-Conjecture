import GQE4SmoothContractions

noncomputable section
set_option maxHeartbeats 500000

open MeasureTheory

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.BoundaryTrace

local instance boundaryPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

def boundaryFourierLinear (dimension : ℕ) (mode : ℤ) :
    C(ClosedDisk, ComplexEuclidean dimension) →ₗ[ℂ] ComplexEuclidean dimension where
  toFun field := fourierCoeff (fun angle : CellCircle => field (boundaryDiskPoint angle)) mode
  map_add' first second := congrFun (fourierCoeff.add
    ((first.continuous.comp boundaryDiskPoint_continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((second.continuous.comp boundaryDiskPoint_continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))) mode
  map_smul' scalar field := fourierCoeff.const_smul (fun angle : CellCircle => field (boundaryDiskPoint angle)) scalar mode

theorem boundaryFourierLinear_bound (dimension : ℕ) (mode : ℤ)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) : ‖boundaryFourierLinear dimension mode field‖ ≤ ‖field‖ := by
  change ‖∫ angle : CellCircle, fourier (-mode) angle • field (boundaryDiskPoint angle) ∂AddCircle.haarAddCircle‖ ≤ _
  have pointwise (angle : CellCircle) : ‖fourier (-mode) angle • field (boundaryDiskPoint angle)‖ ≤ ‖field‖ := by
    rw [norm_smul, show ‖fourier (-mode) angle‖ = 1 by
      simpa only [cellCharacter] using cellCharacter_apply_norm (-mode) angle, one_mul]
    exact field.norm_coe_le_norm (boundaryDiskPoint angle)
  have bound := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (Filter.Eventually.of_forall pointwise)
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using bound

def boundaryFourierCLM (dimension : ℕ) (mode : ℤ) :
    C(ClosedDisk, ComplexEuclidean dimension) →L[ℂ] ComplexEuclidean dimension :=
  (boundaryFourierLinear dimension mode).mkContinuous 1 (fun field =>
    (boundaryFourierLinear_bound dimension mode field).trans_eq (one_mul ‖field‖).symm)

def apBoundaryCoefficientCLM {dimension : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ) (mode : ℤ × ℤ) :
    APBoundaryGrade L sigma gamma ell dimension grade →L[ℂ] ComplexEuclidean dimension :=
  ((apBoundaryWeight L sigma gamma ell grade mode : ℂ)⁻¹) •
    lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode

/-- The accepted AP3 trace is the literal endpoint Fourier coefficient
of the faithful continuous AP2 realization whenever q>=2. -/
theorem apBoundaryTrace_literal {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (field : apGrade L sigma gamma ell dimension grade)
    (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade
      (apBoundaryTrace L sigma gamma ell grade (by omega) field) mode =
      fourierCoeff (fun angle : CellCircle => apTrace admissible large mode.2 field (boundaryDiskPoint angle)) mode.1 := by
  let first : apGrade L sigma gamma ell dimension grade →L[ℂ] ComplexEuclidean dimension :=
    (apBoundaryCoefficientCLM L sigma gamma ell grade mode).comp
    (apBoundaryTrace L sigma gamma ell grade (by omega))
  let second := (boundaryFourierCLM dimension mode.1).comp (apTrace admissible large mode.2)
  have identity : first = second := by
    apply apFiniteGenerator_ext L sigma gamma ell
    intro cell core
    change apBoundaryCoefficient L sigma gamma ell grade
        (apBoundaryTrace L sigma gamma ell grade (by omega) (apFiniteInto L sigma gamma ell (Finsupp.single cell core))) mode =
      fourierCoeff (fun angle : CellCircle => apTrace admissible large mode.2
        (apFiniteInto L sigma gamma ell (Finsupp.single cell core)) (boundaryDiskPoint angle)) mode.1
    rw [apBoundaryTrace_coefficient, apTrace_core]
    rfl
  exact congrArg (fun mapping : apGrade L sigma gamma ell dimension grade →L[ℂ] ComplexEuclidean dimension => mapping field) identity

theorem apHighTrace_literal {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (field : apGrade L sigma gamma ell dimension grade)
    (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade
      (apHighTrace L sigma gamma ell grade (by omega) field) mode =
      if 3 ≤ |mode.1| then
        fourierCoeff (fun angle : CellCircle => apTrace admissible large mode.2 field (boundaryDiskPoint angle)) mode.1 else 0 := by
  change apBoundaryCoefficient L sigma gamma ell grade
    (apHighProjection L sigma gamma ell grade (apBoundaryTrace L sigma gamma ell grade (by omega) field)) mode = _
  rw [apHighProjection_coefficient, apBoundaryTrace_literal admissible large]

end Grad.GaugeCoefficients.Physical.Compensated
