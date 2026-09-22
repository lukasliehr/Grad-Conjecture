import ANP13OriginalSourceBounds

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
variable {L sigma gamma ell : ℝ}

def rawStateEntryConstant (grade : ℕ) : ℝ :=
  orthogonalGradeConstant (grade + 2) + averageGradeConstant (grade + 1) + orthogonalGradeConstant (grade + 1)

theorem rawStateEntryConstant_nonnegative (grade : ℕ) : 0 ≤ rawStateEntryConstant grade :=
  add_nonneg (add_nonneg (orthogonalGradeConstant_nonnegative _) (averageGradeConstant_nonnegative _))
    (orthogonalGradeConstant_nonnegative _)

def rawStateBoundConstant (grade : ℕ) : ℝ := Real.sqrt 5 * rawStateEntryConstant grade

theorem rawStateBoundConstant_nonnegative (grade : ℕ) : 0 ≤ rawStateBoundConstant grade :=
  mul_nonneg (Real.sqrt_nonneg _) (rawStateEntryConstant_nonnegative grade)

/-- The literal five-slot compensated graph norm is bounded at its original
Sobolev grades and analytic width, uniformly over all raw angular modes. -/
theorem rawStateProjector_bound (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (state : CompensatedData L sigma gamma ell) (grade : ℕ) :
    compensatedNorm admissible grade (rawStateProjector L sigma gamma ell mode state) ≤
      rawStateBoundConstant grade * compensatedNorm admissible grade state := by
  let N := compensatedNorm admissible grade state
  have nonnegative : 0 ≤ N := compensatedNorm_nonnegative admissible grade state
  have firstC : orthogonalGradeConstant (grade + 2) ≤ rawStateEntryConstant grade := by
    unfold rawStateEntryConstant
    linarith [averageGradeConstant_nonnegative (grade + 1), orthogonalGradeConstant_nonnegative (grade + 1)]
  have vectorC : averageGradeConstant (grade + 1) ≤ rawStateEntryConstant grade := by
    unfold rawStateEntryConstant
    linarith [orthogonalGradeConstant_nonnegative (grade + 2), orthogonalGradeConstant_nonnegative (grade + 1)]
  have scalarC : orthogonalGradeConstant (grade + 1) ≤ rawStateEntryConstant grade := by
    unfold rawStateEntryConstant
    linarith [orthogonalGradeConstant_nonnegative (grade + 2), averageGradeConstant_nonnegative (grade + 1)]
  have theta := (apSmoothAngularMode_bound mode state.1 (grade + 2)).trans
    ((mul_le_mul_of_nonneg_left (compensatedGraphEntry_bound admissible grade state 0)
      (orthogonalGradeConstant_nonnegative _)).trans (mul_le_mul_of_nonneg_right firstC nonnegative))
  have vector := (apSmoothRawVector_bound mode (apSmoothPlanar L sigma gamma ell state.2) (grade + 1)).trans
    ((mul_le_mul_of_nonneg_left (compensatedGraphEntry_bound admissible grade state 1)
      (averageGradeConstant_nonnegative _)).trans (mul_le_mul_of_nonneg_right vectorC nonnegative))
  have rotatedVector := (apSmoothRawVector_bound mode
    (apSmoothRotation admissible 2 (apSmoothPlanar L sigma gamma ell state.2)) (grade + 1)).trans
      ((mul_le_mul_of_nonneg_left (compensatedGraphEntry_bound admissible grade state 2)
        (averageGradeConstant_nonnegative _)).trans (mul_le_mul_of_nonneg_right vectorC nonnegative))
  have scalar := (apSmoothAngularMode_bound mode (apSmoothScalar L sigma gamma ell state.2) (grade + 1)).trans
    ((mul_le_mul_of_nonneg_left (compensatedGraphEntry_bound admissible grade state 3)
      (orthogonalGradeConstant_nonnegative _)).trans (mul_le_mul_of_nonneg_right scalarC nonnegative))
  have rotatedScalar := (apSmoothAngularMode_bound mode
    (apSmoothRotation admissible 1 (apSmoothScalar L sigma gamma ell state.2)) (grade + 1)).trans
      ((mul_le_mul_of_nonneg_left (compensatedGraphEntry_bound admissible grade state 4)
        (orthogonalGradeConstant_nonnegative _)).trans (mul_le_mul_of_nonneg_right scalarC nonnegative))
  have planarLaw := apSmoothRawStored_planar admissible mode state.2
  have scalarLaw := apSmoothRawStored_scalar admissible mode state.2
  have rotationPlanar := (congrArg (apSmoothRotation admissible 2) planarLaw).trans
    (apSmoothRotation_rawVector admissible mode _)
  have rotationScalar := (congrArg (apSmoothRotation admissible 1) scalarLaw).trans
    (apSmoothRotation_angular admissible mode _)
  have bounds (index : Fin 5) :
      ‖compensatedGraphEntry admissible grade index (rawStateProjector L sigma gamma ell mode state)‖ ≤
        rawStateEntryConstant grade * N := by
    fin_cases index
    · exact theta
    · exact (congrArg (fun field => ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) field‖) planarLaw).le.trans vector
    · exact (congrArg (fun field => ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) field‖) rotationPlanar).le.trans rotatedVector
    · exact (congrArg (fun field => ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) field‖) scalarLaw).le.trans scalar
    · exact (congrArg (fun field => ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) field‖) rotationScalar).le.trans rotatedScalar
  exact (compensatedGraph_bound_of_entries admissible grade _ (rawStateEntryConstant grade * N)
    (mul_nonneg (rawStateEntryConstant_nonnegative grade) nonnegative) bounds).trans_eq (by
      unfold rawStateBoundConstant; rw [mul_assoc])

theorem rawStateComplement_bound (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (grade : ℕ) :
    compensatedNorm admissible grade (rawStateComplement L sigma gamma ell state) ≤
      (1 + 3 * rawStateBoundConstant grade) * compensatedNorm admissible grade state :=
  exceptionalComplement_bound _ (compensatedGraphLinear admissible grade) _ state
    (fun mode => rawStateProjector_bound admissible mode state grade)

end Grad.RawCircularSectors
