import GC18RadialPhysicalIdentity

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearDivision

theorem radialRotatedPoint_origin (angle : ℝ) :
    Grad.GaugeCoefficients.Radial.rotatedPoint angle closedOrigin = closedOrigin := by
  apply Subtype.ext
  change planeRotation angle (0 : SpatialPlane) = 0
  exact (planeRotationEquiv angle).map_zero

theorem coefficientAngular_origin (L sigma gamma ell : ℝ) (grade input output : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade input output) (cell : ℤ) :
    coefficientDerivative (coefficientAngularMap L sigma gamma ell grade input output coefficient)
      cell (zeroDerivativeIndexAt grade) closedOrigin =
      coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) closedOrigin := by
  rw [coefficientAngular_value]
  unfold angularMeanValue
  simp_rw [radialRotatedPoint_origin]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const, sub_zero, one_smul]

theorem angularFamily_physical_origin {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (grade : ℕ) (angle : ℝ) :
    coefficientPhysicalValue (angularFamily family grade) angle closedOrigin =
      coefficientPhysicalValue (family grade) angle closedOrigin := by
  apply tsum_congr
  intro cell
  exact congrArg (fun value : OperatorValue input output => fourierPhase cell angle • value)
    (coefficientAngular_origin L sigma gamma ell grade input output (family grade) cell)

theorem tangentColumn_physical_origin {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) :
    coefficientPhysicalValue (tangentColumnFamily L sigma gamma ell grade) angle closedOrigin = 0 := by
  unfold tangentColumnFamily
  rw [family_physicalValue_sub admissible
    (coordinateFamily L sigma gamma ell 0 (matrixUnit (input := 1) (output := 3) 1 0))
    (coordinateFamily L sigma gamma ell 1 (matrixUnit (input := 1) (output := 3) 0 0))
    (fixedJetFamily_coherent L sigma gamma ell _)
    (fixedJetFamily_coherent L sigma gamma ell _), coordinateFamily_physicalValue, coordinateFamily_physicalValue]
  change (0 : ℂ) • matrixUnit (input := 1) (output := 3) 1 0 -
    (0 : ℂ) • matrixUnit (input := 1) (output := 3) 0 0 = 0
  rw [zero_smul ℂ (matrixUnit (input := 1) (output := 3) 1 0),
    zero_smul ℂ (matrixUnit (input := 1) (output := 3) 0 0), sub_self]

theorem tangentRow_physical_origin {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (angle : ℝ) :
    coefficientPhysicalValue (tangentRowFamily L sigma gamma ell grade) angle closedOrigin = 0 := by
  unfold tangentRowFamily
  rw [family_physicalValue_sub admissible
    (coordinateFamily L sigma gamma ell 0 (matrixUnit (input := 3) (output := 1) 0 1))
    (coordinateFamily L sigma gamma ell 1 (matrixUnit (input := 3) (output := 1) 0 0))
    (fixedJetFamily_coherent L sigma gamma ell _)
    (fixedJetFamily_coherent L sigma gamma ell _), coordinateFamily_physicalValue, coordinateFamily_physicalValue]
  change (0 : ℂ) • matrixUnit (input := 3) (output := 1) 0 1 -
    (0 : ℂ) • matrixUnit (input := 3) (output := 1) 0 0 = 0
  rw [zero_smul ℂ (matrixUnit (input := 3) (output := 1) 0 1),
    zero_smul ℂ (matrixUnit (input := 3) (output := 1) 0 0), sub_self]

theorem sandwich_physical_origin_left {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (column : CoefficientFamily L sigma gamma ell 1 3)
    (gaugeCoherent : FamilyCoherent gauge) (columnCoherent : FamilyCoherent column)
    (grade : ℕ) (angle : ℝ) :
    coefficientPhysicalValue (sandwichFamily admissible (tangentRowFamily L sigma gamma ell) gauge column grade)
      angle closedOrigin = 0 := by
  unfold sandwichFamily composeFamily
  rw [family_physicalValue_comp admissible _ _ (tangentRow_coherent L sigma gamma ell)
    (gaugeCoherent.comp admissible columnCoherent), tangentRow_physical_origin admissible]
  exact ContinuousLinearMap.zero_comp _

theorem sandwich_physical_origin_right {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (row : CoefficientFamily L sigma gamma ell 3 1) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (rowCoherent : FamilyCoherent row) (gaugeCoherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) :
    coefficientPhysicalValue (sandwichFamily admissible row gauge (tangentColumnFamily L sigma gamma ell) grade)
      angle closedOrigin = 0 := by
  unfold sandwichFamily composeFamily
  rw [family_physicalValue_comp admissible _ _ rowCoherent
      (gaugeCoherent.comp admissible (tangentColumn_coherent L sigma gamma ell)),
    family_physicalValue_comp admissible _ _ gaugeCoherent (tangentColumn_coherent L sigma gamma ell),
    tangentColumn_physical_origin admissible, ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_zero]

end Grad.GaugeCoefficients.Physical.RadialLedger
