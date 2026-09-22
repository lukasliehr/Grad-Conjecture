import GPA1ClassicalAngularInterface

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ActualPhysicalAngular
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.GenericCarriers Grad.SourceCollarCoefficients
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Radial Grad.NonlinearRange

theorem polarClosedPoint_orbit (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Grad.GaugeCoefficients.Radial.rotatedPoint angle (polarClosedPoint radius 0 nonnegative bounded) =
      polarClosedPoint radius angle nonnegative bounded := by
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [Grad.GaugeCoefficients.Radial.rotatedPoint, planeRotation, polarClosedPoint, polarPlane, collarPlane, mul_comm]

theorem originalPolar_hasDerivAt {dimension : ℕ} (field : ClosedJet dimension)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    HasDerivAt (fun time => originalPolarValue field (radius, time))
      ((rotationJet field).value (polarClosedPoint radius angle nonnegative bounded)) angle := by
  have derivative := closedOrbit_hasDerivAt field (polarClosedPoint radius 0 nonnegative bounded) angle
  simp_rw [polarClosedPoint_orbit] at derivative
  simpa only [originalPolarValue_closed field _ _ nonnegative bounded] using derivative

theorem originalPolar_angularJet {dimension : ℕ} (field : ClosedJet dimension)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    angularJet 1 (originalPolarValue field) (radius, angle) =
      (rotationJet field).value (polarClosedPoint radius angle nonnegative bounded) := by
  have derivative := angularJet_hasDerivAt 0 (originalPolarValue field) (originalPolarValue_smooth field) radius angle
  rw [angularJet_zero] at derivative
  exact derivative.unique (originalPolar_hasDerivAt field radius angle nonnegative bounded)

theorem coefficientColumn_value_bound {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output) (coherent : FamilyCoherent family)
    (cell : ℤ) (column : PhysicalValue input) (point : ClosedDisk) :
    ‖(coefficientColumnJet parameters family coherent cell column).value point‖ ≤
      coefficientCellBudget (family 0) cell * ‖column‖ := by
  rw [coefficientColumnJet_value]
  apply ((coefficientValue (family 0) cell point).le_opNorm column).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg column)
  apply (coefficientValue_point_norm_le (unitDiskAdmissible parameters) (family 0) cell point).trans
  exact Finset.single_le_sum (f := fun index : DerivativeIndex 0 => ‖(family 0).val (cell, index)‖)
    (fun index _ => norm_nonneg ((family 0).val (cell, index))) (Finset.mem_univ zeroDerivativeIndex)

end Grad.ActualPhysicalAngular
