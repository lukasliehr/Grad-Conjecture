import AFX1ActualFluxBulk

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

def actualMatchingMatrix {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) : Matrix (Fin 3) (Fin 3) ℂ :=
  (physicalFrameMatrix parameters L ell epsilon base angle point).det •
    (familyMatrix ledger.val.frameInverse grade angle point *
      (familyMatrix ledger.val.frameInverse grade angle point).transpose)

theorem apMatchingFlux_physical {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ)
    (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade) (point : ClosedDisk)
    (row : Fin 3) :
    apPhysicalValue admissible large angle (apMatchingFlux admissible ledger.val grade field) point row =
      ∑ column : Fin 3, actualMatchingMatrix ledger grade angle point row column *
        apPhysicalValue admissible large angle field point column := by
  have literal := ledger.property.2.2.2.2.2.1 grade angle point
  have product := congrArg (fun mapping : C(ClosedDisk, ComplexEuclidean 3) => mapping point row)
    (apMultiplier_physical admissible large angle (ledger.val.fluxDeviation grade) field)
  change _ = coefficientPhysicalValue (ledger.val.fluxDeviation grade) angle point
    (apPhysicalValue admissible large angle field point) row at product
  rw [operatorMatrix_action, literal] at product
  change _ = ∑ column : Fin 3, (actualMatchingMatrix ledger grade angle point + 1) row column *
    apPhysicalValue admissible large angle field point column at product
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at product
  change apPhysicalValue admissible large angle
    (-field + apMultiplier admissible (ledger.val.fluxDeviation grade) field) point row = _
  simp only [map_add, map_neg, ContinuousMap.add_apply, ContinuousMap.neg_apply,
    PiLp.add_apply, PiLp.neg_apply]
  rw [product]
  abel

theorem apMatchingRadialColumn_physical {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ)
    (field : apGrade L sigma gamma ell 1 grade) (point : ClosedDisk) (row : Fin 3) :
    apPhysicalValue admissible large angle (apMatchingRadialColumn admissible grade field) point row =
      ![(point.val 0 : ℂ) * apPhysicalValue admissible large angle field point 0,
        (point.val 1 : ℂ) * apPhysicalValue admissible large angle field point 0, 0] row := by
  have value := congrArg (fun mapping : C(ClosedDisk, ComplexEuclidean 3) => mapping point row)
    (apMultiplier_physical admissible large angle
      (fixedJetFamily L sigma gamma ell matchingRadialColumnJet grade) field)
  change _ = coefficientPhysicalValue (fixedJetFamily L sigma gamma ell matchingRadialColumnJet grade) angle point
    (apPhysicalValue admissible large angle field point) row at value
  rw [fixedJetFamily_physicalValue, matchingRadialColumnJet_value] at value
  exact value

/-- The two smooth Cartesian AR8 summands, on the entire closed cap.
At radius one these are precisely `nᵀ B_C w` and `(tᵀ B_C n) ψ`. -/
theorem actualMatchingPrimitive_physical_summands {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ)
    (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade)
    (psi : apGrade L parameters.sigma0 parameters.gamma ell 1 grade) (point : ClosedDisk) :
    let B := actualMatchingMatrix ledger grade angle point
    let w := apPhysicalValue admissible large angle field point
    let v := apPhysicalValue admissible large angle psi point 0
    apPhysicalValue admissible large angle
      (apRadialContraction admissible grade (apMatchingFlux admissible ledger.val grade field) +
        apTangentContraction admissible grade
          (apMatchingFlux admissible ledger.val grade (apMatchingRadialColumn admissible grade psi))) point 0 =
      (point.val 0 : ℂ) * (∑ column : Fin 3, B 0 column * w column) +
      (point.val 1 : ℂ) * (∑ column : Fin 3, B 1 column * w column) +
      ((point.val 0 : ℂ) * (B 1 0 * (point.val 0 : ℂ) + B 1 1 * (point.val 1 : ℂ)) -
        (point.val 1 : ℂ) * (B 0 0 * (point.val 0 : ℂ) + B 0 1 * (point.val 1 : ℂ))) * v := by
  dsimp only
  rw [map_add]
  change apPhysicalValue admissible large angle
      (apRadialContraction admissible grade (apMatchingFlux admissible ledger.val grade field)) point 0 +
    apPhysicalValue admissible large angle
      (apTangentContraction admissible grade
        (apMatchingFlux admissible ledger.val grade (apMatchingRadialColumn admissible grade psi))) point 0 = _
  rw [apRadialContraction_physical, apTangentContraction_physical]
  simp only [storedTangentDot, apMatchingFlux_physical ledger large angle, apMatchingRadialColumn_physical]
  simp [Fin.sum_univ_three]
  ring

theorem apMatchingPrimitive_mean_projection {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ)
    (field : apGrade L sigma gamma ell 3 grade) (psi : apGrade L sigma gamma ell 1 grade) :
    let raw := apRadialContraction admissible grade (apMatchingFlux admissible data grade field) +
      apTangentContraction admissible grade
        (apMatchingFlux admissible data grade (apMatchingRadialColumn admissible grade psi))
    apPhysicalValue admissible large angle (apMatchingPrimitive admissible data grade field psi) =
      apPhysicalValue admissible large angle raw -
        cMapAngular 1 0 (apPhysicalValue admissible large angle raw) := by
  dsimp only
  let raw := apRadialContraction admissible grade (apMatchingFlux admissible data grade field) +
    apTangentContraction admissible grade
      (apMatchingFlux admissible data grade (apMatchingRadialColumn admissible grade psi))
  exact ((apPhysicalValue admissible large angle).map_sub raw (apAngularMean L sigma gamma ell 1 grade raw)).trans
    (congrArg (fun value : C(ClosedDisk, ComplexEuclidean 1) => apPhysicalValue admissible large angle raw - value)
      (apAngularMean_physical admissible large angle raw))

end Grad.GaugeCoefficients.Physical.Compensated
