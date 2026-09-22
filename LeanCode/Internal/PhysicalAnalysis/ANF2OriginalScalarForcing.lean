import ANF1OriginalFullMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarForcing
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

def forceResponse (admissible : Admissible L sigma gamma ell)
    (force : APSmooth L sigma gamma ell 2) : APSmooth L sigma gamma ell 2 :=
  -apVectorInverse admissible force

def forceLift (admissible : Admissible L sigma gamma ell)
    (force : APSmooth L sigma gamma ell 2) : APSmooth L sigma gamma ell 3 :=
  apSmoothValueMap L sigma gamma ell planarInclusionMap (forceResponse admissible force)

/-- The literal AN15 load, with the original scaled axial derivative. -/
def scalarForcingInput (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 1 :=
  source.2.1 + apSmoothDiv admissible (forceLift admissible source.1) +
    apSmoothAxial L sigma gamma ell 1 (reconstructedScalar admissible source.2.2)

def scalarForcing (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 1 :=
  apFullB admissible (scalarForcingInput admissible source)

theorem forceResponse_bound (admissible : Admissible L sigma gamma ell)
    (force : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (forceResponse admissible force)‖ ≤
      vectorInverseConstant grade * ‖apSmoothGrade L sigma gamma ell 2 grade force‖ := by
  have law := (apSmoothGrade L sigma gamma ell 2 grade).map_neg (apVectorInverse admissible force)
  exact (congrArg norm law).le.trans ((norm_neg _).le.trans (apVectorInverse_bound admissible force grade))

theorem forceLift_bound (admissible : Admissible L sigma gamma ell)
    (force : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 3 grade (forceLift admissible force)‖ ≤
      (‖planarInclusionMap‖ * vectorInverseConstant grade) *
        ‖apSmoothGrade L sigma gamma ell 2 grade force‖ :=
  (apSmoothValueMap_bound planarInclusionMap (forceResponse admissible force) grade).trans
    ((mul_le_mul_of_nonneg_left (forceResponse_bound admissible force grade) (norm_nonneg _)).trans_eq (by ring))

def forcingInputConstant (L gamma : ℝ) (grade : ℕ) : ℝ :=
  1 + divergenceForwardConstant L gamma grade * (‖planarInclusionMap‖ * vectorInverseConstant (grade + 1)) +
    apLoweringConstant grade * angularInverseConstant (grade + 1)

def forcingConstant (L gamma : ℝ) (grade : ℕ) : ℝ :=
  fullBConstant grade * forcingInputConstant L gamma grade

theorem forcingInputConstant_nonnegative (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ forcingInputConstant L gamma grade := by
  unfold forcingInputConstant
  exact add_nonneg (add_nonneg zero_le_one (mul_nonneg (divergenceForwardConstant_nonnegative admissible grade)
    (mul_nonneg (norm_nonneg _) (vectorInverseConstant_nonnegative _))))
    (mul_nonneg (apLoweringConstant_nonnegative _) (angularInverseConstant_nonnegative _))

theorem forcingConstant_nonnegative (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ forcingConstant L gamma grade :=
  mul_nonneg (fullBConstant_nonnegative _) (forcingInputConstant_nonnegative admissible _)

theorem scalarForcingInput_bound (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (scalarForcingInput admissible source)‖ ≤
      forcingInputConstant L gamma grade * ‖capSourceGrade grade source‖ := by
  let project := apSmoothGrade L sigma gamma ell 1 grade
  have parts := capSource_components_bound grade source
  have liftBound := (forceLift_bound admissible source.1 (grade + 1)).trans
    (mul_le_mul_of_nonneg_left parts.1 (mul_nonneg (norm_nonneg _) (vectorInverseConstant_nonnegative _)))
  have divBound := (apSmoothDiv_bound admissible (forceLift admissible source.1) grade).trans
    (mul_le_mul_of_nonneg_left liftBound (divergenceForwardConstant_nonnegative admissible grade))
  have scalarBound : ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (reconstructedScalar admissible source.2.2)‖ ≤
      angularInverseConstant (grade + 1) * ‖capSourceGrade grade source‖ :=
    (apShiftInverse_bound admissible 0 (grade + 1) source.2.2).trans
      (mul_le_mul_of_nonneg_left parts.2.2 (angularInverseConstant_nonnegative _))
  have axialBound := (apAxial_bound L sigma gamma ell 1 grade
    ((reconstructedScalar admissible source.2.2).val (grade + 1))).trans
      (mul_le_mul_of_nonneg_left scalarBound (apLoweringConstant_nonnegative _))
  have law : project (scalarForcingInput admissible source) =
      project source.2.1 + project (apSmoothDiv admissible (forceLift admissible source.1)) +
        project (apSmoothAxial L sigma gamma ell 1 (reconstructedScalar admissible source.2.2)) := by
    exact (project.map_add _ _).trans (congrArg (fun v => v + project
      (apSmoothAxial L sigma gamma ell 1 (reconstructedScalar admissible source.2.2))) (project.map_add _ _))
  have triangle := (norm_add_le (project source.2.1 + project (apSmoothDiv admissible (forceLift admissible source.1)))
    (project (apSmoothAxial L sigma gamma ell 1 (reconstructedScalar admissible source.2.2)))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  exact (congrArg norm law).le.trans (triangle.trans
    ((add_le_add (add_le_add parts.2.1 divBound) axialBound).trans_eq (by unfold forcingInputConstant; ring)))

/-- Original AN17 bulk bound. The constant depends only on L,gamma,s and
uses exactly G in Hs, f and Hc in H(s+1), at the original analytic width. -/
theorem scalarForcing_bound (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (scalarForcing admissible source)‖ ≤
      forcingConstant L gamma grade * ‖capSourceGrade grade source‖ :=
  (apFullB_bound admissible (scalarForcingInput admissible source) grade).trans
    ((mul_le_mul_of_nonneg_left (scalarForcingInput_bound admissible source grade)
      (fullBConstant_nonnegative grade)).trans_eq (by unfold forcingConstant; ring))

end Grad.ActualScalarForcing
