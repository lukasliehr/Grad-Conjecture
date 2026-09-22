import AFZ2ActualDefectFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 150000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

theorem apFamilyMultiplier_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (large : 2 ≤ grade) (angle : ℝ)
    (family : CoefficientFamily L sigma gamma ell input output)
    (field : apGrade L sigma gamma ell input grade) (point : ClosedDisk) (row : Fin output) :
    apPhysicalValue admissible large angle (apMultiplier admissible (family grade) field) point row =
      ∑ column : Fin input, familyMatrix family grade angle point row column *
        apPhysicalValue admissible large angle field point column := by
  have value := congrArg (fun mapping : C(ClosedDisk, ComplexEuclidean output) => mapping point row)
    (apMultiplier_physical admissible large angle (family grade) field)
  change _ = coefficientPhysicalValue (family grade) angle point
    (apPhysicalValue admissible large angle field point) row at value
  exact value.trans (operatorMatrix_action _ _ row)

theorem matchingTraceDeviation_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix data.traceDeviation grade angle point =
      familyMatrix (normalRowFamily data) grade angle point - circleTraceCovector point := by
  have addition := familyMatrix_add admissible (referenceRowFamily L sigma gamma ell) data.traceDeviation
    (fixedJetFamily_coherent L sigma gamma ell radialRowJet) coherent.2.2.2.2.2.1 grade angle point
  have reference := referenceRowFamily_matrix L sigma gamma ell grade angle point
  have normalized := addition.trans (congrArg (fun matrix : Matrix (Fin 1) (Fin 3) ℂ =>
    matrix + familyMatrix data.traceDeviation grade angle point) reference)
  have shifted := congrArg (fun matrix : Matrix (Fin 1) (Fin 3) ℂ => matrix - circleTraceCovector point) normalized
  exact (shifted.trans (by abel)).symm

theorem matchingFluxDeviation_matrix_actual {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix ledger.val.fluxDeviation grade angle point = actualMatchingMatrix ledger grade angle point + 1 :=
  ledger.property.2.2.2.2.2.1 grade angle point

theorem apMatchingDefect_physical_summands {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ)
    (vector : apGrade L sigma gamma ell 3 grade)
    (psi : apGrade L sigma gamma ell 1 grade) (point : ClosedDisk) :
    let D := familyMatrix data.fluxDeviation grade angle point
    let rowDelta := familyMatrix data.traceDeviation grade angle point
    let w := apPhysicalValue admissible large angle vector point
    let v := apPhysicalValue admissible large angle psi point 0
    apPhysicalValue admissible large angle (apMatchingDefectBulk admissible data grade vector psi) point 0 =
      (point.val 0 : ℂ) * (∑ column : Fin 3, D 0 column * w column) +
      (point.val 1 : ℂ) * (∑ column : Fin 3, D 1 column * w column) +
      (∑ column : Fin 3, rowDelta 0 column * w column) +
      ((point.val 0 : ℂ) * (D 1 0 * (point.val 0 : ℂ) + D 1 1 * (point.val 1 : ℂ)) -
        (point.val 1 : ℂ) * (D 0 0 * (point.val 0 : ℂ) + D 0 1 * (point.val 1 : ℂ))) * v := by
  dsimp only
  let D := familyMatrix data.fluxDeviation grade angle point
  let radial := apRadialContraction admissible grade (apMultiplier admissible (data.fluxDeviation grade) vector)
  let normal := apMultiplier admissible (data.traceDeviation grade) vector
  let cross := apTangentContraction admissible grade
    (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi))
  let value := fun field : apGrade L sigma gamma ell 1 grade => apPhysicalValue admissible large angle field point 0
  have addition : value (radial + normal + cross) = value radial + value normal + value cross :=
    (congrArg (fun mapping : C(ClosedDisk, ComplexEuclidean 1) => mapping point 0)
      ((apPhysicalValue admissible large angle).map_add (radial + normal) cross)).trans
    (congrArg (fun result : ℂ => result + value cross)
      (congrArg (fun mapping : C(ClosedDisk, ComplexEuclidean 1) => mapping point 0)
        ((apPhysicalValue admissible large angle).map_add radial normal)))
  have radialValue := (apRadialContraction_physical admissible large angle
      (apMultiplier admissible (data.fluxDeviation grade) vector) point).trans
    (congrArg₂ (fun first second : ℂ => (point.val 0 : ℂ) * first + (point.val 1 : ℂ) * second)
      (apFamilyMultiplier_physical admissible large angle data.fluxDeviation vector point 0)
      (apFamilyMultiplier_physical admissible large angle data.fluxDeviation vector point 1))
  have normalValue := apFamilyMultiplier_physical admissible large angle data.traceDeviation vector point 0
  have columnValue (row : Fin 3) :
      (∑ column : Fin 3, D row column *
        apPhysicalValue admissible large angle (apMatchingRadialColumn admissible grade psi) point column) =
      ∑ column : Fin 3, D row column *
        ![(point.val 0 : ℂ) * apPhysicalValue admissible large angle psi point 0,
          (point.val 1 : ℂ) * apPhysicalValue admissible large angle psi point 0, 0] column :=
    Finset.sum_congr rfl (fun column _ => congrArg (fun result : ℂ => D row column * result)
      (apMatchingRadialColumn_physical admissible large angle psi point column))
  have crossValue := apTangentContraction_physical admissible large angle
    (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi)) point
  change value cross = -(point.val 1 : ℂ) * apPhysicalValue admissible large angle
      (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi)) point 0 +
    (point.val 0 : ℂ) * apPhysicalValue admissible large angle
      (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi)) point 1 at crossValue
  have crossProducts := congrArg₂ (fun first second : ℂ => -(point.val 1 : ℂ) * second + (point.val 0 : ℂ) * first)
    ((apFamilyMultiplier_physical admissible large angle data.fluxDeviation
      (apMatchingRadialColumn admissible grade psi) point 1).trans (columnValue 1))
    ((apFamilyMultiplier_physical admissible large angle data.fluxDeviation
      (apMatchingRadialColumn admissible grade psi) point 0).trans (columnValue 0))
  have crossAlgebra :
      -(point.val 1 : ℂ) * (∑ column : Fin 3, D 0 column *
        ![(point.val 0 : ℂ) * apPhysicalValue admissible large angle psi point 0,
          (point.val 1 : ℂ) * apPhysicalValue admissible large angle psi point 0, 0] column) +
      (point.val 0 : ℂ) * (∑ column : Fin 3, D 1 column *
        ![(point.val 0 : ℂ) * apPhysicalValue admissible large angle psi point 0,
          (point.val 1 : ℂ) * apPhysicalValue admissible large angle psi point 0, 0] column) =
      ((point.val 0 : ℂ) * (D 1 0 * (point.val 0 : ℂ) + D 1 1 * (point.val 1 : ℂ)) -
        (point.val 1 : ℂ) * (D 0 0 * (point.val 0 : ℂ) + D 0 1 * (point.val 1 : ℂ))) *
          apPhysicalValue admissible large angle psi point 0 := by
    simp [Fin.sum_univ_three]
    ring
  exact addition.trans (congrArg₂ (fun first second : ℂ => first + second)
    (congrArg₂ (fun first second : ℂ => first + second) radialValue normalValue)
    (crossValue.trans (crossProducts.trans crossAlgebra)))

/-- Literal AR16 on the entire closed cap. D is the SAME signed physical
B_C+I; Lambda is the SAME actual physical normal row of GQE9. -/
theorem actualMatchingDefect_physical_summands {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ)
    (vector : apGrade L parameters.sigma0 parameters.gamma ell 3 grade)
    (psi : apGrade L parameters.sigma0 parameters.gamma ell 1 grade) (point : ClosedDisk) :
    let D := actualMatchingMatrix ledger grade angle point + 1
    let rowDelta := familyMatrix (normalRowFamily ledger.val) grade angle point - circleTraceCovector point
    let w := apPhysicalValue admissible large angle vector point
    let v := apPhysicalValue admissible large angle psi point 0
    apPhysicalValue admissible large angle (apMatchingDefectBulk admissible ledger.val grade vector psi) point 0 =
      (point.val 0 : ℂ) * (∑ column : Fin 3, D 0 column * w column) +
      (point.val 1 : ℂ) * (∑ column : Fin 3, D 1 column * w column) +
      (∑ column : Fin 3, rowDelta 0 column * w column) +
      ((point.val 0 : ℂ) * (D 1 0 * (point.val 0 : ℂ) + D 1 1 * (point.val 1 : ℂ)) -
        (point.val 1 : ℂ) * (D 0 0 * (point.val 0 : ℂ) + D 0 1 * (point.val 1 : ℂ))) * v := by
  have formula := apMatchingDefect_physical_summands admissible ledger.val large angle vector psi point
  simpa only [matchingFluxDeviation_matrix_actual ledger,
    matchingTraceDeviation_matrix admissible ledger.val ledger.property.1] using formula

end Grad.GaugeCoefficients.Physical.Compensated
