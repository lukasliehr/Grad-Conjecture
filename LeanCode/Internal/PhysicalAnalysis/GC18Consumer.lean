import GC18PublicConstruction

noncomputable section

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

/-- The literal original cap range is contained in the stronger uniform
range proved by the construction; no analytic width or norm is changed. -/
theorem originalCap_admissible (parameters : PhaseParameters) {L ell : ℝ}
    (lengthPositive : 0 < L) (capPositive : 0 < ell)
    (capSmall : ell < min (1 / 2 : ℝ) L) :
    Admissible L parameters.sigma0 parameters.gamma ell := by
  refine ⟨lengthPositive, parameters.gamma_pos, parameters.gamma_lt_min, capPositive, le_min ?_ ?_⟩
  · linarith [(lt_min_iff.mp capSmall).1]
  · exact (lt_min_iff.mp capSmall).2.le

/-- Public actual-ledger consumer: all grades, including zero and one,
use the same fixed low neighborhood and the original complete V=ran C0. -/
theorem actualRadialGaugeInverse_ready (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualRadialGaugeInverseGoal parameters L radius threshold :=
  actualRadialGaugeInverse parameters L radius threshold positive radiusNonnegative thresholdPositive

/-- Exact original AP2 norm, full Fourier cells and Cartesian derivatives.
This is the inherited Hilbert norm, not an equivalent replacement norm. -/
theorem originalWeightedCompletion_norm (L sigma gamma ell : ℝ) (dimension grade : ℕ)
    (field : apGrade L sigma gamma ell dimension grade) :
    ‖field‖ ^ 2 = ∑' cell : ℤ, ∑ index : DerivativeIndex grade, ‖field.val cell index‖ ^ 2 :=
  apGrade_norm_sq L sigma gamma ell dimension grade field

/-- Actual full-cell field multiplication, with its uniform same-grade
bound and faithful L2 Fourier realization at every grade q≥0. -/
theorem originalWeightedMultiplier_ready {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (input output grade : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade input output)
    (field : apGrade L sigma gamma ell input grade) :
    ‖apCompletedBilinear admissible input output grade coefficient field‖ ≤
      apMultiplierConstant L sigma gamma grade * ‖coefficient‖ * ‖field‖ ∧
    ∀ angle : ℝ, apL2PhysicalValue admissible angle
        (apCompletedBilinear admissible input output grade coefficient field) =
      closedOperatorL2 (cMapCoefficient admissible grade input output angle coefficient)
        (apL2PhysicalValue admissible angle field) :=
  (completeWeightedMultiplier admissible input output grade coefficient field).2

end Grad.GaugeCoefficients.Physical.RadialLedger
