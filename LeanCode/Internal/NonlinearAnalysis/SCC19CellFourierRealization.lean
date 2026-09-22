import SCC18KappaCellCalculus

noncomputable section
open scoped BigOperators

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.SourceCollarDivision Grad.SourceCollarRestriction

theorem coefficientColumnJet_value {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (cell : ℤ) (column : PhysicalValue input) (point : ClosedDisk) :
    (coefficientColumnJet parameters family coherent cell column).value point =
      coefficientValue (family 0) cell point column := rfl

theorem coefficientColumnJet_fourier {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input) (angle : ℝ) (point : ClosedDisk) :
    HasSum (fun cell => fourierPhase cell angle •
      (coefficientColumnJet parameters family coherent cell column).value point)
      (coefficientPhysicalValue (family 0) angle point column) := by
  rw [coherent_physicalValue family coherent]
  have sum := (ContinuousLinearMap.apply ℂ (PhysicalValue output) column).hasSum
    (fourierTerm_summable (unitDiskAdmissible parameters) (family 0) angle point).hasSum
  apply sum.congr_fun
  intro cell
  rw [coefficientColumnJet_value]
  rfl

theorem coefficientColumnJet_polarFourier {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input)
    (radius polarAngle axialAngle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    HasSum (fun cell => fourierPhase cell axialAngle •
      originalPolarValue (coefficientColumnJet parameters family coherent cell column) (radius, polarAngle))
      (coefficientPhysicalValue (family 0) axialAngle (polarClosedPoint radius polarAngle nonnegative bounded) column) := by
  apply (coefficientColumnJet_fourier parameters family coherent column axialAngle
    (polarClosedPoint radius polarAngle nonnegative bounded)).congr_fun
  intro cell
  rw [originalPolarValue_closed _ radius polarAngle nonnegative bounded]

theorem coefficientColumnJet_scalarFourier {input : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input 1)
    (coherent : FamilyCoherent family) (column : PhysicalValue input)
    (radius polarAngle axialAngle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    HasSum (fun cell => fourierPhase cell axialAngle *
      originalPolarValue (coefficientColumnJet parameters family coherent cell column) (radius, polarAngle) 0)
      (coefficientPhysicalValue (family 0) axialAngle (polarClosedPoint radius polarAngle nonnegative bounded) column 0) := by
  have sum := (PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0 : PhysicalValue 1 →L[ℂ] ℂ).hasSum
    (coefficientColumnJet_polarFourier parameters family coherent column radius polarAngle axialAngle nonnegative bounded)
  exact sum

end Grad.SourceCollarCoefficients
