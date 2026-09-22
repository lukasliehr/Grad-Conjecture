import ANF3OriginalBoundaryMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarForcing
open Grad.BoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

def forceRadial (admissible : Admissible L sigma gamma ell)
    (force : APSmooth L sigma gamma ell 2) : APSmooth L sigma gamma ell 1 :=
  apSmoothRadial admissible (forceLift admissible force)

def radialResponseConstant (L sigma gamma : ℝ) (grade : ℕ) : ℝ :=
  fixedRowBoundConstant L sigma gamma grade radialRowJet *
    (‖planarInclusionMap‖ * vectorInverseConstant grade)

theorem radialResponseConstant_nonnegative (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ radialResponseConstant L sigma gamma grade :=
  mul_nonneg (fixedRowBoundConstant_nonnegative admissible grade radialRowJet)
    (mul_nonneg (norm_nonneg _) (vectorInverseConstant_nonnegative _))

theorem forceRadial_bound (admissible : Admissible L sigma gamma ell)
    (force : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (forceRadial admissible force)‖ ≤
      radialResponseConstant L sigma gamma grade * ‖apSmoothGrade L sigma gamma ell 2 grade force‖ :=
  (apFixedRow_bound admissible grade radialRowJet ((forceLift admissible force).val grade)).trans
    ((mul_le_mul_of_nonneg_left (forceLift_bound admissible force grade)
      (fixedRowBoundConstant_nonnegative admissible grade radialRowJet)).trans_eq
        (by unfold radialResponseConstant; ring))

/-- The original AN16 datum B Ph(beta - Y dot u_f on the circle).
Boundary grade s+1 is precisely the native H(s+1/2) scale. -/
def boundaryForcing (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (source : SmoothCapSource L sigma gamma ell)
    (beta : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) :
    APBoundaryGrade L sigma gamma ell 1 (grade + 1) :=
  boundaryB L sigma gamma ell (grade + 1)
    (beta - apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
      (apSmoothGrade L sigma gamma ell 1 (grade + 1) (forceRadial admissible source.1)))

def boundaryForcingConstant (L sigma gamma : ℝ) (grade : ℕ) : ℝ :=
  Real.sqrt (traceCellConstant (grade + 1)) * radialResponseConstant L sigma gamma (grade + 1)

theorem boundaryForcingConstant_nonnegative (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ boundaryForcingConstant L sigma gamma grade :=
  mul_nonneg (Real.sqrt_nonneg _) (radialResponseConstant_nonnegative admissible _)

theorem boundaryForcing_bound (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (source : SmoothCapSource L sigma gamma ell)
    (beta : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) :
    ‖boundaryForcing admissible grade source beta‖ ≤ ‖beta‖ +
      boundaryForcingConstant L sigma gamma grade * ‖capSourceGrade grade source‖ := by
  have sourceBound := (forceRadial_bound admissible source.1 (grade + 1)).trans
    (mul_le_mul_of_nonneg_left (capSource_components_bound grade source).1
      (radialResponseConstant_nonnegative admissible _))
  have traceBound := (apBoundaryTrace_bound L sigma gamma ell (grade + 1) (by omega)
    (apSmoothGrade L sigma gamma ell 1 (grade + 1) (forceRadial admissible source.1))).trans
      (mul_le_mul_of_nonneg_left sourceBound (Real.sqrt_nonneg _))
  have estimate := (boundaryB_bound (grade + 1)
    (beta - apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
      (apSmoothGrade L sigma gamma ell 1 (grade + 1) (forceRadial admissible source.1)))).trans
    ((norm_sub_le _ _).trans (add_le_add le_rfl traceBound))
  exact estimate.trans_eq (by unfold boundaryForcingConstant; ring)

/-- The original AN17 bulk and boundary forcing estimate; no auxiliary trace
or interior extension norm appears on the right side. -/
theorem actualScalarForcing_consumer (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (source : SmoothCapSource L sigma gamma ell)
    (beta : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (scalarForcing admissible source)‖ +
      ‖boundaryForcing admissible grade source beta‖ ≤
        (forcingConstant L gamma grade + boundaryForcingConstant L sigma gamma grade) *
          ‖capSourceGrade grade source‖ + ‖beta‖ :=
  (add_le_add (scalarForcing_bound admissible source grade)
    (boundaryForcing_bound admissible grade source beta)).trans_eq (by ring)

end Grad.ActualScalarForcing
