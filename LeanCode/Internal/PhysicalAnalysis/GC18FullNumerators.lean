import GC18ClosedMean

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearDivision

theorem radialDivisionFamily_add {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (first second : CoefficientFamily L sigma gamma ell input output) :
    radialDivisionFamily admissible (fun grade => first grade + second grade) =
      fun grade => radialDivisionFamily admissible first grade + radialDivisionFamily admissible second grade := by
  funext grade
  simp only [radialDivisionFamily, radialFamily, laplacianFamily, angularFamily, map_add]

theorem angularFamily_add {L sigma gamma ell : ℝ} {input output : ℕ}
    (first second : CoefficientFamily L sigma gamma ell input output) :
    angularFamily (fun grade => first grade + second grade) =
      fun grade => angularFamily first grade + angularFamily second grade := by
  funext grade
  exact map_add (coefficientAngularMap L sigma gamma ell grade input output) _ _

/-- Equality of full physical numerators determines their actual completed
IΔΠ values, including the axis. -/
theorem radialDivisionFamily_physical_congr {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (first second : CoefficientFamily L sigma gamma ell input output)
    (firstCoherent : FamilyCoherent first) (secondCoherent : FamilyCoherent second)
    (grade : ℕ) (angle : ℝ)
    (same : ∀ point, coefficientPhysicalValue (first grade) angle point =
      coefficientPhysicalValue (second grade) angle point) (point : ClosedDisk) :
    coefficientPhysicalValue (radialDivisionFamily admissible first grade) angle point =
      coefficientPhysicalValue (radialDivisionFamily admissible second grade) angle point := by
  have means (point : ClosedDisk) :
      coefficientPhysicalValue (angularFamily first grade) angle point =
        coefficientPhysicalValue (angularFamily second grade) angle point := by
    rw [angularFamily_physicalValue admissible first firstCoherent,
      angularFamily_physicalValue admissible second secondCoherent]
    simp_rw [same]
  apply continuous_closedDisk_eq_of_offAxis _ _
    (coefficientPhysicalValue_continuous admissible _ (radialDivisionFamily_coherent admissible first firstCoherent) grade angle)
    (coefficientPhysicalValue_continuous admissible _ (radialDivisionFamily_coherent admissible second secondCoherent) grade angle)
    ?_ point
  intro other offAxis
  have firstIdentity := radialDivisionFamily_physical_identity admissible first firstCoherent grade angle other
  have secondIdentity := radialDivisionFamily_physical_identity admissible second secondCoherent grade angle other
  rw [means other, means closedOrigin] at firstIdentity
  have nonzero : ((‖other.val‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr offAxis))
  exact (smul_right_injective (OperatorValue input output) nonzero) (firstIdentity.symm.trans secondIdentity)

def fullGaugeFamily {L sigma gamma ell : ℝ} (gauge : CoefficientFamily L sigma gamma ell 3 3) :
    CoefficientFamily L sigma gamma ell 3 3 :=
  fun grade => identityFamily L sigma gamma ell 3 grade + gauge grade

theorem fullGaugeFamily_coherent {L sigma gamma ell : ℝ}
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) :
    FamilyCoherent (fullGaugeFamily gauge) := (identityFamily_coherent L sigma gamma ell 3).add coherent

theorem fullGaugeFamily_physicalValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (fullGaugeFamily gauge grade) angle point =
      ContinuousLinearMap.id ℂ (PhysicalValue 3) + coefficientPhysicalValue (gauge grade) angle point := by
  unfold fullGaugeFamily
  rw [family_physicalValue_add admissible (identityFamily L sigma gamma ell 3) gauge (identityFamily_coherent L sigma gamma ell 3) coherent,
    identityFamily, identityFamily_physicalValue]

theorem sandwichFull_physicalValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (row : CoefficientFamily L sigma gamma ell 3 1)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (column : CoefficientFamily L sigma gamma ell 1 3)
    (rowCoherent : FamilyCoherent row) (gaugeCoherent : FamilyCoherent gauge) (columnCoherent : FamilyCoherent column)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (sandwichFamily admissible row (fullGaugeFamily gauge) column grade) angle point =
      coefficientPhysicalValue (composeFamily admissible row column grade) angle point +
        coefficientPhysicalValue (sandwichFamily admissible row gauge column grade) angle point := by
  unfold sandwichFamily composeFamily
  rw [family_physicalValue_comp admissible row _ rowCoherent
    ((fullGaugeFamily_coherent gauge gaugeCoherent).comp admissible columnCoherent),
    family_physicalValue_comp admissible _ _ (fullGaugeFamily_coherent gauge gaugeCoherent) columnCoherent,
    fullGaugeFamily_physicalValue admissible gauge gaugeCoherent,
    family_physicalValue_comp admissible row column rowCoherent columnCoherent,
    family_physicalValue_comp admissible row _ rowCoherent (gaugeCoherent.comp admissible columnCoherent),
    family_physicalValue_comp admissible gauge column gaugeCoherent columnCoherent,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_add]

theorem radialSandwich_full_decomposition {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (row : CoefficientFamily L sigma gamma ell 3 1)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (column : CoefficientFamily L sigma gamma ell 1 3)
    (rowCoherent : FamilyCoherent row) (gaugeCoherent : FamilyCoherent gauge) (columnCoherent : FamilyCoherent column)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (radialDivisionFamily admissible
      (sandwichFamily admissible row (fullGaugeFamily gauge) column) grade) angle point =
      coefficientPhysicalValue (radialDivisionFamily admissible (composeFamily admissible row column) grade) angle point +
        coefficientPhysicalValue (radialDivisionFamily admissible (sandwichFamily admissible row gauge column) grade) angle point := by
  have firstCoherent := sandwichFamily_coherent admissible row (fullGaugeFamily gauge) column
    rowCoherent (fullGaugeFamily_coherent gauge gaugeCoherent) columnCoherent
  have sandwichCoherent := sandwichFamily_coherent admissible row gauge column rowCoherent gaugeCoherent columnCoherent
  have productCoherent : FamilyCoherent (composeFamily admissible row column) := rowCoherent.comp admissible columnCoherent
  have identity := radialDivisionFamily_physical_congr admissible
    (sandwichFamily admissible row (fullGaugeFamily gauge) column)
    (fun grade => composeFamily admissible row column grade + sandwichFamily admissible row gauge column grade)
    firstCoherent (productCoherent.add sandwichCoherent) grade angle (fun other => by
      rw [sandwichFull_physicalValue admissible row gauge column rowCoherent gaugeCoherent columnCoherent,
        family_physicalValue_add admissible _ _ productCoherent sandwichCoherent]) point
  rw [radialDivisionFamily_add, family_physicalValue_add admissible _ _
    (radialDivisionFamily_coherent admissible _ productCoherent)
    (radialDivisionFamily_coherent admissible _ sandwichCoherent)] at identity
  exact identity

/-- The actual μ is IΔΠ(JYᵀ C JY), not merely a perturbative stand-in. -/
theorem muCoefficient_full_formula {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (muCoefficient admissible gauge grade) angle point =
      coefficientPhysicalValue (radialDivisionFamily admissible
        (sandwichFamily admissible (tangentRowFamily L sigma gamma ell) (fullGaugeFamily gauge)
          (tangentColumnFamily L sigma gamma ell)) grade) angle point := by
  rw [radialSandwich_full_decomposition admissible _ gauge _
    (tangentRow_coherent L sigma gamma ell) coherent (tangentColumn_coherent L sigma gamma ell)]
  change coefficientPhysicalValue (muCoefficient admissible gauge grade) angle point =
    coefficientPhysicalValue (radialDivisionFamily admissible (radiusSquaredFamily admissible) grade) angle point +
      coefficientPhysicalValue (muDeviation admissible gauge grade) angle point
  rw [radialRadiusSquared_physicalValue admissible]
  unfold muCoefficient
  rw [family_physicalValue_add admissible (identityFamily L sigma gamma ell 1) (muDeviation admissible gauge) (identityFamily_coherent L sigma gamma ell 1)
    (muDeviation_coherent admissible gauge coherent), identityFamily, identityFamily_physicalValue]

end Grad.GaugeCoefficients.Physical.RadialLedger
