import GC18NumeratorOrigin

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearDivision

theorem radialSandwich_physical_left {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (column : CoefficientFamily L sigma gamma ell 1 3)
    (gaugeCoherent : FamilyCoherent gauge) (columnCoherent : FamilyCoherent column)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (angularFamily
      (sandwichFamily admissible (tangentRowFamily L sigma gamma ell) gauge column) grade) angle point =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • coefficientPhysicalValue (radialDivisionFamily admissible
        (sandwichFamily admissible (tangentRowFamily L sigma gamma ell) gauge column) grade) angle point := by
  have identity := radialDivisionFamily_physical_identity admissible
    (sandwichFamily admissible (tangentRowFamily L sigma gamma ell) gauge column)
    (sandwichFamily_coherent admissible _ _ _ (tangentRow_coherent L sigma gamma ell) gaugeCoherent columnCoherent)
    grade angle point
  rw [angularFamily_physical_origin,
    sandwich_physical_origin_left admissible gauge column gaugeCoherent columnCoherent, sub_zero] at identity
  exact identity

theorem radialSandwich_physical_right {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (row : CoefficientFamily L sigma gamma ell 3 1) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (rowCoherent : FamilyCoherent row) (gaugeCoherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (angularFamily
      (sandwichFamily admissible row gauge (tangentColumnFamily L sigma gamma ell)) grade) angle point =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • coefficientPhysicalValue (radialDivisionFamily admissible
        (sandwichFamily admissible row gauge (tangentColumnFamily L sigma gamma ell)) grade) angle point := by
  have identity := radialDivisionFamily_physical_identity admissible
    (sandwichFamily admissible row gauge (tangentColumnFamily L sigma gamma ell))
    (sandwichFamily_coherent admissible _ _ _ rowCoherent gaugeCoherent (tangentColumn_coherent L sigma gamma ell))
    grade angle point
  rw [angularFamily_physical_origin,
    sandwich_physical_origin_right admissible row gauge rowCoherent gaugeCoherent, sub_zero] at identity
  exact identity

/-- Actual GC17 consumer of the newly proved AO9 identity, in the original
full-cell Fourier realization. The axis cancellation is proved from the
literal JY factors; no missing GC03 identity is supplied as a premise. -/
theorem actualRadialNumeratorIdentities {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {field : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (angularFamily (sandwichFamily admissible
      (tangentRowFamily L parameters.sigma0 parameters.gamma ell) ledger.val.gaugeDeviation
      (tangentColumnFamily L parameters.sigma0 parameters.gamma ell)) grade) angle point =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • coefficientPhysicalValue
        (muDeviation admissible ledger.val.gaugeDeviation grade) angle point ∧
    coefficientPhysicalValue (angularFamily (sandwichFamily admissible
      (tangentRowFamily L parameters.sigma0 parameters.gamma ell) ledger.val.gaugeDeviation
      (scalarColumnFamily L parameters.sigma0 parameters.gamma ell)) grade) angle point =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • coefficientPhysicalValue
        (etaCoefficient admissible ledger.val.gaugeDeviation grade) angle point ∧
    coefficientPhysicalValue (angularFamily (sandwichFamily admissible
      (scalarRowFamily L parameters.sigma0 parameters.gamma ell) ledger.val.gaugeDeviation
      (tangentColumnFamily L parameters.sigma0 parameters.gamma ell)) grade) angle point =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • coefficientPhysicalValue
        (nuCoefficient admissible ledger.val.gaugeDeviation grade) angle point := by
  have coherent : FamilyCoherent ledger.val.gaugeDeviation := ledger.property.1.2.2.2.1
  exact ⟨radialSandwich_physical_left admissible ledger.val.gaugeDeviation _ coherent
      (tangentColumn_coherent L parameters.sigma0 parameters.gamma ell) grade angle point,
    radialSandwich_physical_left admissible ledger.val.gaugeDeviation _ coherent
      (scalarColumn_coherent L parameters.sigma0 parameters.gamma ell) grade angle point,
    radialSandwich_physical_right admissible _ ledger.val.gaugeDeviation
      (scalarRow_coherent L parameters.sigma0 parameters.gamma ell) coherent grade angle point⟩

end Grad.GaugeCoefficients.Physical.RadialLedger
