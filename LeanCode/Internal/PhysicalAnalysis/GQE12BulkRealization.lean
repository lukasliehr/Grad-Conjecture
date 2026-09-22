import GQE10NormalTraceDifference
import GQE11LiteralEndpoint

noncomputable section
set_option maxHeartbeats 500000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearQuotientBounds Grad.RepresentedKernel.SpatialProduct Grad.GaugeCoefficients.Radial

theorem apAngularMean_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (field : apGrade L sigma gamma ell dimension grade) :
    apPhysicalValue admissible large angle (apAngularMean L sigma gamma ell dimension grade field) =
      cMapAngular dimension 0 (apPhysicalValue admissible large angle field) := by
  let first := (apPhysicalValue (dimension := dimension) admissible large angle).comp
    (apAngularMean L sigma gamma ell dimension grade)
  let second := (cMapAngular dimension 0).comp (apPhysicalValue (dimension := dimension) admissible large angle)
  have identity : first = second := by
    apply apFiniteGenerator_ext L sigma gamma ell
    intro cell core
    change apPhysicalValue admissible large angle
        (apAngularMean L sigma gamma ell dimension grade (apFiniteInto L sigma gamma ell (Finsupp.single cell core))) =
      cMapAngular dimension 0 (apPhysicalValue admissible large angle (apFiniteInto L sigma gamma ell (Finsupp.single cell core)))
    rw [apAngularMean_core, apFiniteJetMap_single, apPhysicalValue_single, apPhysicalValue_single, map_smul]
    apply congrArg (fun value : C(ClosedDisk, ComplexEuclidean dimension) => axialPhase cell angle • value)
    apply ContinuousMap.ext
    intro point
    exact (closedCharacterProjection_jet 0 core point).symm
  exact congrArg (fun mapping : apGrade L sigma gamma ell dimension grade →L[ℂ]
    C(ClosedDisk, ComplexEuclidean dimension) => mapping field) identity

theorem apRadialContraction_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (field : apGrade L sigma gamma ell 3 grade) (point : ClosedDisk) :
    apPhysicalValue admissible large angle (apRadialContraction admissible grade field) point 0 =
      (point.val 0 : ℂ) * apPhysicalValue admissible large angle field point 0 +
        (point.val 1 : ℂ) * apPhysicalValue admissible large angle field point 1 := by
  have physical := apMultiplier_physical admissible large angle
    (fixedJetFamily L sigma gamma ell radialRowJet grade) field
  have value := congrArg (fun mapping : C(ClosedDisk, ComplexEuclidean 1) => mapping point 0) physical
  change _ = coefficientPhysicalValue (fixedJetFamily L sigma gamma ell radialRowJet grade) angle point
    (apPhysicalValue admissible large angle field point) 0 at value
  exact value.trans ((congrArg (fun coefficient : OperatorValue 3 1 =>
    coefficient (apPhysicalValue admissible large angle field point) 0)
      (fixedJetFamily_physicalValue L sigma gamma ell radialRowJet grade angle point)).trans (radialRowJet_value point _))

theorem apTangentContraction_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (field : apGrade L sigma gamma ell 3 grade) (point : ClosedDisk) :
    apPhysicalValue admissible large angle (apTangentContraction admissible grade field) point 0 =
      storedTangentDot point (apPhysicalValue admissible large angle field point) := by
  have physical := apMultiplier_physical admissible large angle
    (fixedJetFamily L sigma gamma ell tangentRowJet grade) field
  have value := congrArg (fun mapping : C(ClosedDisk, ComplexEuclidean 1) => mapping point 0) physical
  change _ = coefficientPhysicalValue (fixedJetFamily L sigma gamma ell tangentRowJet grade) angle point
    (apPhysicalValue admissible large angle field point) 0 at value
  exact value.trans ((congrArg (fun coefficient : OperatorValue 3 1 =>
    coefficient (apPhysicalValue admissible large angle field point) 0)
      (fixedJetFamily_physicalValue L sigma gamma ell tangentRowJet grade angle point)).trans (tangentRowJet_value point _))

/-- Full-cell physical bulk product, before restriction to r=1. -/
theorem actualNormalBulk_physical {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ)
    (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade) (point : ClosedDisk) :
    apPhysicalValue admissible large angle (apMultiplier admissible (normalRowFamily ledger.val grade) field) point 0 =
      ∑ column : Fin 3,
        ((spatialColumn point).transpose * familyMatrix ledger.val.seedInverse grade angle point *
          planarPhysicalInclusion.transpose * (familyMatrix ledger.val.frameInverse grade angle point).transpose) 0 column *
            apPhysicalValue admissible large angle field point column := by
  have value := congrArg (fun mapping : C(ClosedDisk, ComplexEuclidean 1) => mapping point 0)
    (apMultiplier_physical admissible large angle (normalRowFamily ledger.val grade) field)
  change _ = coefficientPhysicalValue (normalRowFamily ledger.val grade) angle point
    (apPhysicalValue admissible large angle field point) 0 at value
  apply value.trans
  rw [operatorMatrix_action]
  change (∑ column : Fin 3, familyMatrix (normalRowFamily ledger.val) grade angle point 0 column *
    apPhysicalValue admissible large angle field point column) = _
  rw [actualNormalRow_matrix ledger]

end Grad.GaugeCoefficients.Physical.Compensated
