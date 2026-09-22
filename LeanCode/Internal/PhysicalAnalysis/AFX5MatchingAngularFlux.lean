import AFX4MatchingTraceBounds
import SBT6LiteralAngular

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

theorem matchingAngularFrequency_le (L ell : ℝ) (mode : ℤ × ℤ) :
    |(mode.1 : ℝ)| ≤ apBoundaryFrequency L ell mode := by
  apply (sq_le_sq₀ (abs_nonneg _) (apBoundaryFrequency_pos L ell mode).le).mp
  rw [sq_abs, apBoundaryFrequency_sq]
  nlinarith [sq_nonneg ((mode.2 : ℝ) * ell / L)]

theorem matchingBoundaryWeight_succ (L sigma gamma ell : ℝ) (grade : ℕ) (positive : 1 ≤ grade)
    (mode : ℤ × ℤ) :
    apBoundaryWeight L sigma gamma ell (grade + 1) mode =
      apBoundaryFrequency L ell mode * apBoundaryWeight L sigma gamma ell grade mode := by
  have exponent : 2 * (grade + 1) - 1 = 2 + (2 * grade - 1) := by omega
  unfold apBoundaryWeight
  rw [exponent, pow_add, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (apBoundaryFrequency_pos L ell mode)]
  ring

def matchingAngularMultiplier (L ell : ℝ) (mode : ℤ × ℤ) : ℂ :=
  Complex.I * (mode.1 : ℂ) / (apBoundaryFrequency L ell mode : ℂ)

theorem matchingAngularMultiplier_bound (L ell : ℝ) (mode : ℤ × ℤ) :
    ‖matchingAngularMultiplier L ell mode‖ ≤ 1 := by
  unfold matchingAngularMultiplier
  rw [norm_div, norm_mul, Complex.norm_I, one_mul]
  have castNorm : ‖(mode.1 : ℂ)‖ = |(mode.1 : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  rw [castNorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (apBoundaryFrequency_pos L ell mode)]
  exact (div_le_one (apBoundaryFrequency_pos L ell mode)).mpr (matchingAngularFrequency_le L ell mode)

def matchingAngularLinear (L sigma gamma ell : ℝ) (grade : ℕ) :
    APBoundaryGrade L sigma gamma ell 1 (grade + 1) →ₗ[ℂ] APBoundaryGrade L sigma gamma ell 1 grade where
  toFun field := ⟨fun mode => matchingAngularMultiplier L ell mode • field mode,
    field.property.mono' (fun mode => by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (matchingAngularMultiplier_bound L ell mode)
        (norm_nonneg (field mode))).trans_eq (one_mul _))⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    change matchingAngularMultiplier L ell mode • (scalar • field mode) =
      scalar • (matchingAngularMultiplier L ell mode • field mode)
    exact smul_comm _ _ _

/-- Angular differentiation in the original half-order trace scale.
The polynomial weight loses exactly one order, with norm at most one. -/
def matchingAngular (L sigma gamma ell : ℝ) (grade : ℕ) :
    APBoundaryGrade L sigma gamma ell 1 (grade + 1) →L[ℂ] APBoundaryGrade L sigma gamma ell 1 grade :=
  (matchingAngularLinear L sigma gamma ell grade).mkContinuous 1 (fun field => by
    rw [one_mul]
    apply lp.norm_mono (by norm_num)
    intro mode
    change ‖matchingAngularMultiplier L ell mode • field mode‖ ≤ ‖field mode‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (matchingAngularMultiplier_bound L ell mode)
      (norm_nonneg (field mode))).trans_eq (one_mul _))

theorem matchingAngular_bound (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) :
    ‖matchingAngular L sigma gamma ell grade field‖ ≤ ‖field‖ := by
  apply lp.norm_mono (by norm_num)
  intro mode
  change ‖matchingAngularMultiplier L ell mode • field mode‖ ≤ ‖field mode‖
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (matchingAngularMultiplier_bound L ell mode)
    (norm_nonneg (field mode))).trans_eq (one_mul _)

theorem matchingAngular_coefficient (L sigma gamma ell : ℝ) (grade : ℕ) (positive : 1 ≤ grade)
    (field : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade (matchingAngular L sigma gamma ell grade field) mode =
      (Complex.I * (mode.1 : ℂ)) • apBoundaryCoefficient L sigma gamma ell (grade + 1) field mode := by
  change ((apBoundaryWeight L sigma gamma ell grade mode : ℂ)⁻¹) •
    (matchingAngularMultiplier L ell mode • field mode) =
      (Complex.I * (mode.1 : ℂ)) • (((apBoundaryWeight L sigma gamma ell (grade + 1) mode : ℂ)⁻¹) • field mode)
  rw [smul_smul, smul_smul, matchingBoundaryWeight_succ L sigma gamma ell grade positive]
  congr 1
  unfold matchingAngularMultiplier
  push_cast
  ring

theorem matchingClosedBoundary_rotation (field : ClosedJet 1) (mode : ℤ) :
    fourierCoeff (fun angle : CellCircle => (Grad.NonlinearRange.rotationJet field).value (boundaryDiskPoint angle)) mode =
      (Complex.I * (mode : ℂ)) • fourierCoeff (fun angle : CellCircle => field.value (boundaryDiskPoint angle)) mode := by
  rw [← angularCoefficient_circle, ← angularCoefficient_circle]
  apply angularCoefficient_derivative
  · exact field.value.continuous.comp (boundaryDiskPoint_continuous.comp (AddCircle.continuous_mk' _))
  · exact (Grad.NonlinearRange.rotationJet field).value.continuous.comp
      (boundaryDiskPoint_continuous.comp (AddCircle.continuous_mk' _))
  · exact Grad.SourceBoundaryTrace.closedBoundary_hasDerivAt field
  · rw [Grad.SourceBoundaryTrace.boundaryDiskPoint_pi]

theorem matchingSmoothTrace_coefficient {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (large : 2 ≤ grade)
    (field : APSmooth L sigma gamma ell 1) (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade
      (apBoundaryTrace L sigma gamma ell grade (by omega) (field.val grade)) mode =
      fourierCoeff (fun angle : CellCircle =>
        (apSmoothJet admissible 1 mode.2 field).value (boundaryDiskPoint angle)) mode.1 :=
  (apBoundaryTrace_literal admissible large (field.val grade) mode).trans
    (congrArg (fun value : C(ClosedDisk, ComplexEuclidean 1) =>
      fourierCoeff (fun angle : CellCircle => value (boundaryDiskPoint angle)) mode.1)
        (apSmoothJet_value_trace admissible large field mode.2).symm)

/-- On the actual smooth core the weighted Fourier map is the literal
Cartesian angular derivative, followed by the original trace. -/
theorem matchingAngular_smooth {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (large : 2 ≤ grade)
    (field : APSmooth L sigma gamma ell 1) :
    matchingAngular L sigma gamma ell grade
      (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega) (field.val (grade + 1))) =
      apBoundaryTrace L sigma gamma ell grade (by omega)
        ((apSmoothRotation admissible 1 field).val grade) := by
  let source := apBoundaryTrace L sigma gamma ell (grade + 1) (by omega) (field.val (grade + 1))
  let output := apBoundaryTrace L sigma gamma ell grade (by omega) ((apSmoothRotation admissible 1 field).val grade)
  have coefficients (mode : ℤ × ℤ) :
      apBoundaryCoefficient L sigma gamma ell grade (matchingAngular L sigma gamma ell grade source) mode =
        apBoundaryCoefficient L sigma gamma ell grade output mode := by
    have derivative := (matchingSmoothTrace_coefficient admissible grade large (apSmoothRotation admissible 1 field) mode).trans
      ((congrArg (fun jet : ClosedJet 1 =>
        fourierCoeff (fun angle : CellCircle => jet.value (boundaryDiskPoint angle)) mode.1)
          (apSmoothRotation_jet admissible field mode.2)).trans
            (matchingClosedBoundary_rotation (apSmoothJet admissible 1 mode.2 field) mode.1))
    exact (matchingAngular_coefficient L sigma gamma ell grade (by omega) source mode).trans
      ((congrArg (fun value : ComplexEuclidean 1 => (Complex.I * (mode.1 : ℂ)) • value)
        (matchingSmoothTrace_coefficient admissible (grade + 1) (by omega) field mode)).trans derivative.symm)
  apply Subtype.ext
  funext mode
  exact (apBoundary_weighted_coefficient L sigma gamma ell grade
    (matchingAngular L sigma gamma ell grade source) mode).symm.trans
      ((congrArg (fun value : ComplexEuclidean 1 =>
        (apBoundaryWeight L sigma gamma ell grade mode : ℂ) • value) (coefficients mode)).trans
          (apBoundary_weighted_coefficient L sigma gamma ell grade output mode))

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

/-- The AR8 angular flux is the derivative of the actual two-term primitive. -/
def completedMatchingX (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] APBoundaryGrade L sigma gamma ell 1 grade :=
  (matchingAngular L sigma gamma ell grade).comp (completedMatchingP admissible data grade core)

theorem completedMatchingX_core (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (grade : ℕ) (large : 2 ≤ grade) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : core) :
    completedMatchingX admissible data grade core (compensatedIntoClosure admissible grade core field) =
      apBoundaryTrace L sigma gamma ell grade (by omega)
        ((apSmoothRotation admissible 1 (smoothMatchingPrimitive admissible data coherent field.val)).val grade) :=
  (congrArg (matchingAngular L sigma gamma ell grade)
    (completedMatchingP_core admissible data coherent grade core field)).trans
      (matchingAngular_smooth admissible grade large (smoothMatchingPrimitive admissible data coherent field.val))

theorem completedMatchingX_coefficient (data : LedgerData L sigma gamma ell) (grade : ℕ) (positive : 1 ≤ grade)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade (completedMatchingX admissible data grade core field) mode =
      (Complex.I * (mode.1 : ℂ)) • apBoundaryCoefficient L sigma gamma ell (grade + 1)
        (completedMatchingP admissible data grade core field) mode :=
  matchingAngular_coefficient L sigma gamma ell grade positive _ mode

theorem completedMatchingX_bound (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedMatchingX admissible data grade core field‖ ≤ matchingTraceConstant data grade * ‖field‖ :=
  (matchingAngular_bound L sigma gamma ell grade _).trans
    (completedMatchingP_bound admissible data grade core field)

end Grad.GaugeCoefficients.Physical.Compensated
