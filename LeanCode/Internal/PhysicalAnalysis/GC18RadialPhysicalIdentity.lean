import GC18RadialFamilyIdentity

noncomputable section

set_option maxHeartbeats 1400000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearDivision

/-- AO9 after the full, untruncated Fourier realization. -/
theorem radialDivisionFamily_physical_identity {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (angularFamily family grade) angle point -
      coefficientPhysicalValue (angularFamily family grade) angle closedOrigin =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) •
        coefficientPhysicalValue (radialDivisionFamily admissible family grade) angle point := by
  rw [coherent_physicalValue (angularFamily family) (angularFamily_coherent family coherent),
    coherent_physicalValue (angularFamily family) (angularFamily_coherent family coherent),
    coherent_physicalValue (radialDivisionFamily admissible family) (radialDivisionFamily_coherent admissible family coherent)]
  change (∑' cell : ℤ, fourierPhase cell angle • coefficientValue (angularFamily family 0) cell point) -
    (∑' cell : ℤ, fourierPhase cell angle • coefficientValue (angularFamily family 0) cell closedOrigin) =
    ((‖point.val‖ ^ 2 : ℝ) : ℂ) •
      (∑' cell : ℤ, fourierPhase cell angle • coefficientValue (radialDivisionFamily admissible family 0) cell point)
  rw [← (fourierTerm_summable admissible (angularFamily family 0) angle point).tsum_sub
    (fourierTerm_summable admissible (angularFamily family 0) angle closedOrigin),
    ← Summable.tsum_const_smul ((‖point.val‖ ^ 2 : ℝ) : ℂ)
      (fourierTerm_summable admissible (radialDivisionFamily admissible family 0) angle point)]
  apply tsum_congr
  intro cell
  rw [← smul_sub (fourierPhase cell angle)
    (coefficientValue (angularFamily family 0) cell point)
    (coefficientValue (angularFamily family 0) cell closedOrigin)]
  have identity := radialDivisionFamily_identity admissible family coherent 0 cell point
  change coefficientValue (angularFamily family 0) cell point -
      coefficientValue (angularFamily family 0) cell closedOrigin =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • coefficientValue (radialDivisionFamily admissible family 0) cell point at identity
  rw [identity]
  exact smul_comm (fourierPhase cell angle) ((‖point.val‖ ^ 2 : ℝ) : ℂ)
    (coefficientValue (radialDivisionFamily admissible family 0) cell point)

theorem radialDivisionFamily_matrix_identity {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (angularFamily family) grade angle point -
      familyMatrix (angularFamily family) grade angle closedOrigin =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • familyMatrix (radialDivisionFamily admissible family) grade angle point := by
  have identity := congrArg (operatorMatrix (input := input) (output := output))
    (radialDivisionFamily_physical_identity admissible family coherent grade angle point)
  unfold familyMatrix
  simpa only [operatorMatrix_sub, operatorMatrix_smul] using identity

end Grad.GaugeCoefficients.Physical.RadialLedger
