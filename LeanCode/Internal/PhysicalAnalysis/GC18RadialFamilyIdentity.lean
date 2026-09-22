import GC18RadialClosure

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearDivision

/-- The completed radial identity is grade-compatible on the actual coherent
coefficient family, at every integer cell and closed-disk point. -/
theorem radialDivisionFamily_identity {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) (grade : ℕ) (cell : ℤ) (point : ClosedDisk) :
    coefficientDerivative (angularFamily family grade) cell (zeroDerivativeIndexAt grade) point -
      coefficientDerivative (angularFamily family grade) cell (zeroDerivativeIndexAt grade) closedOrigin =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • coefficientDerivative (radialDivisionFamily admissible family grade)
        cell (zeroDerivativeIndexAt grade) point := by
  have angularCoherent := angularFamily_coherent family coherent
  have radialCoherent := radialDivisionFamily_coherent admissible family coherent
  rw [angularCoherent grade 2 (zeroDerivativeIndexAt grade) (zeroDerivativeIndexAt 2) rfl cell point,
    angularCoherent grade 2 (zeroDerivativeIndexAt grade) (zeroDerivativeIndexAt 2) rfl cell closedOrigin,
    radialCoherent grade 0 (zeroDerivativeIndexAt grade) (zeroDerivativeIndexAt 0) rfl cell point]
  exact coefficientRadialDivision admissible input output (family 2) cell point

/-- AO9 for a vanishing averaged numerator; zero on the axis is a literal
value hypothesis and never a division of an unknown field. -/
theorem radialDivisionFamily_identity_of_origin_zero {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (origin : ∀ cell, coefficientDerivative (angularFamily family 0) cell (zeroDerivativeIndexAt 0) closedOrigin = 0)
    (grade : ℕ) (cell : ℤ) (point : ClosedDisk) :
    coefficientDerivative (angularFamily family grade) cell (zeroDerivativeIndexAt grade) point =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • coefficientDerivative (radialDivisionFamily admissible family grade)
        cell (zeroDerivativeIndexAt grade) point := by
  have identity := radialDivisionFamily_identity admissible family coherent grade cell point
  rw [angularFamily_coherent family coherent grade 0 (zeroDerivativeIndexAt grade)
    (zeroDerivativeIndexAt 0) rfl cell closedOrigin, origin cell, sub_zero] at identity
  exact identity

end Grad.GaugeCoefficients.Physical.RadialLedger
