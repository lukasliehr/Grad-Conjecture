import ASX17SignedForce
import ANM6BoundaryAndNorm

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace Grad.CircularHighWeak

/-- The original radial row expressed through the two actual Cartesian spin components. -/
theorem radialRow_spins (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : ClosedJet 3) :
    apProductJet radialRowJet field = (1 / 2 : ℂ) •
      (coordinateMultiplyJet ((-sign : ℤ) : ℝ) (valueMapJet (spinValue (sign : ℂ)) (valueMapJet planarPartMap field)) +
       coordinateMultiplyJet (sign : ℝ) (valueMapJet (spinValue ((-sign : ℤ) : ℂ)) (valueMapJet planarPartMap field))) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (apProductJet radialRowJet field).value point 0 = _
  rcases signed with rfl | rfl <;>
    simp [apProductJet_value, radialRowJet_value, closedJet_value_add, closedJet_value_smul,
      coordinateMultiplyJet_value, signedComplexCoordinate, valueMapJet_value, spinValue_apply, planarPartMap] <;>
    ring_nf <;> simp [Complex.I_sq]

/-- A raw exceptional vector has an actual scalar radial row of mode 2 sigma. -/
theorem radialRow_secondMode (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : ClosedJet 3)
    (positive : angularClosedJet (3 * sign) (valueMapJet (spinValue (sign : ℂ)) (valueMapJet planarPartMap field)) =
      valueMapJet (spinValue (sign : ℂ)) (valueMapJet planarPartMap field))
    (negative : angularClosedJet sign (valueMapJet (spinValue ((-sign : ℤ) : ℂ)) (valueMapJet planarPartMap field)) =
      valueMapJet (spinValue ((-sign : ℤ) : ℂ)) (valueMapJet planarPartMap field)) :
    angularClosedJet (2 * sign) (apProductJet radialRowJet field) = apProductJet radialRowJet field := by
  have opposite : -sign = 1 ∨ -sign = -1 := by omega
  rw [radialRow_spins sign signed, angularClosedJet_smul, angularClosedJet_add,
    signedCoordinate_mode (-sign) opposite, signedCoordinate_mode sign signed]
  rw [show 2 * sign - -sign = 3 * sign by omega, show 2 * sign - sign = sign by omega, positive, negative]

/-- Every literal low scalar angular mode vanishes under the original AP high trace. -/
theorem apHighTrace_lowMode_zero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (low : |mode| ≤ 2) (field : APSmooth L sigma gamma ell 1)
    (pure : ∀ cell, angularClosedJet mode (apSmoothJet admissible 1 cell field) = apSmoothJet admissible 1 cell field)
    (grade : ℕ) (large : 2 ≤ grade) :
    apHighTrace L sigma gamma ell grade (by omega) (apSmoothGrade L sigma gamma ell 1 grade field) = 0 := by
  apply lp.ext
  funext frequency
  have coefficient := apHighTrace_literal admissible large (apSmoothGrade L sigma gamma ell 1 grade field) frequency
  have trace : apTrace admissible large frequency.2 (apSmoothGrade L sigma gamma ell 1 grade field) =
      (apSmoothJet admissible 1 frequency.2 field).value :=
    (apSmoothJet_value_trace admissible large field frequency.2).symm
  rw [trace, boundaryCoefficient_angular] at coefficient
  have absent : (if 3 ≤ |frequency.1| then
      (angularClosedJet frequency.1 (apSmoothJet admissible 1 frequency.2 field)).value (boundaryDiskPoint 0) else 0) = 0 := by
    split_ifs with high
    · have distinct : frequency.1 ≠ mode := by intro same; rw [same] at high; omega
      have law := angularClosedJet_projection frequency.1 mode (apSmoothJet admissible 1 frequency.2 field)
      rw [pure frequency.2, if_neg distinct] at law
      rw [law]
      rfl
    · rfl
  have zero := coefficient.trans absent
  have weighted := apBoundary_weighted_coefficient L sigma gamma ell grade
    (apHighTrace L sigma gamma ell grade (by omega) (apSmoothGrade L sigma gamma ell 1 grade field)) frequency
  exact weighted.symm.trans ((congrArg (fun value =>
    (apBoundaryWeight L sigma gamma ell grade frequency : ℂ) • value) zero).trans (smul_zero _))

end Grad.ActualExceptionalInverse
