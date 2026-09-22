import AKZ3OriginalMatrixRadialKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped Topology BigOperators
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.BoundaryTrace
open Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

variable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family)

theorem physicalMatrixScalar_axialCoefficient (row : Fin output) (column : Fin input)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (cell : ℤ) :
    angularCoefficient (fun axialAngle => familyMatrix family 0 axialAngle
      (polarClosedPoint radius angle nonnegative bounded) row column) cell =
      originalPolarValue (coefficientColumnJet parameters family coherent cell (operatorBasis column)) (radius,angle) row := by
  have vectorNorms := coefficientColumnJet_norm_summable parameters family coherent (operatorBasis column)
    (polarClosedPoint radius angle nonnegative bounded)
  have scalarNorms : Summable (fun cell =>
      ‖originalPolarValue (coefficientColumnJet parameters family coherent cell (operatorBasis column)) (radius,angle) row‖) := by
    simp_rw [originalPolarValue_closed _ radius angle nonnegative bounded]
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => PiLp.norm_apply_le _ row) vectorNorms
  apply angularCoefficient_of_axialSeries _ scalarNorms _ _ cell
  intro axialAngle
  exact (PiLp.proj 2 (fun _ : Fin output => ℂ) row : PhysicalValue output →L[ℂ] ℂ).hasSum
    (coefficientColumnJet_polarFourier parameters family coherent (operatorBasis column)
      radius angle axialAngle nonnegative bounded)

/-- These are the actual two iterated Fourier integrals of the same matrix,
with original angular and axial periods. -/
theorem physicalMatrixScalar_doubleCoefficient (row : Fin output) (column : Fin input)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun angle => angularCoefficient (fun axialAngle => familyMatrix family 0 axialAngle
      (polarClosedPoint radius angle nonnegative bounded) row column) mode.2) mode.1 =
      physicalMatrixScalar parameters family coherent row column 0 radius mode := by
  simp_rw [physicalMatrixScalar_axialCoefficient parameters family coherent row column radius _ nonnegative bounded mode.2]
  exact (angularCoefficient_component
    (fun angle => originalPolarValue (coefficientColumnJet parameters family coherent mode.2 (operatorBasis column)) (radius,angle))
    ((originalPolarValue_smooth _).continuous.comp (continuous_const.prodMk continuous_id)) row mode.1).symm

end Grad.ActualPhysicalField
