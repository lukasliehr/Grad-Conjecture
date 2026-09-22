import ACF2OriginalFixedMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.SameCellFixedMultiplication
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.BoundaryTrace
open Grad.ActualScalarForcing Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

def radialForcingConstant (grade : ℕ) : ℝ :=
  fixedRowConstant grade radialRowJet * (‖planarInclusionMap‖ * vectorInverseConstant grade)

theorem radialForcingConstant_nonnegative (grade : ℕ) : 0 ≤ radialForcingConstant grade :=
  mul_nonneg (fixedRowConstant_nonnegative grade radialRowJet)
    (mul_nonneg (norm_nonneg _) (vectorInverseConstant_nonnegative grade))

/-- The literal frozen ANF forceRadial, with a constant independent of every
physical parameter. All cells and the original same-grade norm are retained. -/
theorem forceRadial_uniform_bound (admissible : Admissible L sigma gamma ell)
    (force : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (forceRadial admissible force)‖ ≤
      radialForcingConstant grade * ‖apSmoothGrade L sigma gamma ell 2 grade force‖ :=
  (apSmoothFixedJet_uniform_bound admissible radialRowJet (forceLift admissible force) grade).trans
    ((mul_le_mul_of_nonneg_left (forceLift_bound admissible force grade)
      (fixedRowConstant_nonnegative grade radialRowJet)).trans_eq (mul_assoc _ _ _).symm)

def boundaryResponseConstant (grade : ℕ) : ℝ :=
  Real.sqrt (traceCellConstant (grade + 1)) * radialForcingConstant (grade + 1)

theorem boundaryResponseConstant_nonnegative (grade : ℕ) : 0 ≤ boundaryResponseConstant grade :=
  mul_nonneg (Real.sqrt_nonneg _) (radialForcingConstant_nonnegative _)

theorem boundaryForcing_uniform_bound (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (source : SmoothCapSource L sigma gamma ell) (beta : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) :
    ‖boundaryForcing admissible grade source beta‖ ≤
      ‖beta‖ + boundaryResponseConstant grade * ‖capSourceGrade grade source‖ := by
  have sourceBound := (forceRadial_uniform_bound admissible source.1 (grade + 1)).trans
    (mul_le_mul_of_nonneg_left (capSource_components_bound grade source).1 (radialForcingConstant_nonnegative _))
  have traceBound := (apBoundaryTrace_bound L sigma gamma ell (grade + 1) (by omega)
    (apSmoothGrade L sigma gamma ell 1 (grade + 1) (forceRadial admissible source.1))).trans
      (mul_le_mul_of_nonneg_left sourceBound (Real.sqrt_nonneg _))
  have estimate := (boundaryB_bound (grade + 1)
    (beta - apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
      (apSmoothGrade L sigma gamma ell 1 (grade + 1) (forceRadial admissible source.1)))).trans
    ((norm_sub_le _ _).trans (add_le_add le_rfl traceBound))
  exact estimate.trans_eq (by unfold boundaryResponseConstant; ring)

/-- Actual AN17 with constants before sigma and ell, at unchanged original
analytic width. This sharpens frozen ANF without changing any accepted map. -/
theorem actualScalarForcing_uniform_width (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (source : SmoothCapSource L sigma gamma ell) (beta : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (scalarForcing admissible source)‖ +
      ‖boundaryForcing admissible grade source beta‖ ≤
        (forcingConstant L gamma grade + boundaryResponseConstant grade) * ‖capSourceGrade grade source‖ + ‖beta‖ :=
  (add_le_add (scalarForcing_bound admissible source grade) (boundaryForcing_uniform_bound admissible grade source beta)).trans_eq (by ring)

/-- Quantifier-explicit all-cell same-grade force-radial estimate: the
nonnegative constant is selected before every physical parameter and input. -/
theorem actualUniformForceRadial (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (length width damping scale : ℝ)
      (admissible : Admissible length width damping scale) (force : APSmooth length width damping scale 2),
      ‖apSmoothGrade length width damping scale 1 grade (forceRadial admissible force)‖ ≤
        constant * ‖apSmoothGrade length width damping scale 2 grade force‖ :=
  ⟨radialForcingConstant grade, radialForcingConstant_nonnegative grade,
    fun _ _ _ _ admissible force => forceRadial_uniform_bound admissible force grade⟩

end Grad.SameCellFixedMultiplication
