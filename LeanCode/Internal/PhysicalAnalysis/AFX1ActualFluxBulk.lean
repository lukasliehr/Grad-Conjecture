import AFL4FullReferenceUniqueness
import GQF44ActualConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Radial

/-- The smooth Cartesian column `(Y₁,Y₂,0)`, valid also at the axis. -/
def matchingRadialColumnJet : SmoothOperatorJet 1 3 :=
  operatorJetAdd (coordinateOperatorJet 0 (matrixUnit 0 0))
    (coordinateOperatorJet 1 (matrixUnit 1 0))

theorem matchingRadialColumnJet_value (point : ClosedDisk) (value : ComplexEuclidean 1)
    (coordinate : Fin 3) :
    matchingRadialColumnJet.value point value coordinate =
      ![(point.val 0 : ℂ) * value 0, (point.val 1 : ℂ) * value 0, 0] coordinate := by
  change ((coordinateOperatorJet 0 (matrixUnit (input := 1) (output := 3) 0 0)).value point +
    (coordinateOperatorJet 1 (matrixUnit (input := 1) (output := 3) 1 0)).value point) value coordinate = _
  fin_cases coordinate <;> simp [coordinateOperatorJet_value, matrixUnit_apply, operatorBasis]

theorem matchingTangentRadialJet_zero (field : ClosedJet 1) :
    apProductJet tangentRowJet (apProductJet matchingRadialColumnJet field) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (apProductJet tangentRowJet (apProductJet matchingRadialColumnJet field)).value point 0 = 0
  rw [apProductJet_value, tangentRowJet_value, apProductJet_value]
  simp only [storedTangentDot, matchingRadialColumnJet_value, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

def apMatchingRadialColumn (grade : ℕ) :
    apGrade L sigma gamma ell 1 grade →L[ℂ] apGrade L sigma gamma ell 3 grade :=
  apMultiplier admissible (fixedJetFamily L sigma gamma ell matchingRadialColumnJet grade)

theorem apMatchingRadialColumn_single (grade : ℕ) (cell : ℤ) (field : ClosedJet 1) :
    apMatchingRadialColumn admissible grade (apFiniteInto L sigma gamma ell (Finsupp.single cell field)) =
      apFiniteInto L sigma gamma ell (Finsupp.single cell (apProductJet matchingRadialColumnJet field)) := by
  exact (apMultiplier_single admissible cell 0 matchingRadialColumnJet field).trans
    (congrArg (fun index => apFiniteInto L sigma gamma ell
      (Finsupp.single index (apProductJet matchingRadialColumnJet field))) (add_zero cell))

theorem apMatchingTangentRadial_zero (grade : ℕ) (field : apGrade L sigma gamma ell 1 grade) :
    apTangentContraction admissible grade (apMatchingRadialColumn admissible grade field) = 0 := by
  have equality : (apTangentContraction admissible grade).comp (apMatchingRadialColumn admissible grade) = 0 := by
    apply apFiniteGenerator_ext L sigma gamma ell
    intro cell core
    change apTangentContraction admissible grade
      (apMatchingRadialColumn admissible grade (apFiniteInto L sigma gamma ell (Finsupp.single cell core))) = 0
    rw [apMatchingRadialColumn_single, apTangentContraction_single,
      matchingTangentRadialJet_zero, Finsupp.single_zero, map_zero]
  exact congrArg (fun mapping => mapping field) equality

/-- The actual signed inverse-Gram flux matrix: `B_C = -I + (B_C+I)`. -/
def apMatchingFlux (data : LedgerData L sigma gamma ell) (grade : ℕ) :
    apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 3 grade :=
  -ContinuousLinearMap.id ℂ _ + apMultiplier admissible (data.fluxDeviation grade)

/-- AR8 before mean removal and trace. Both physical flux terms are retained. -/
def apMatchingPrimitive (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (vector : apGrade L sigma gamma ell 3 grade) (psi : apGrade L sigma gamma ell 1 grade) :
    apGrade L sigma gamma ell 1 grade :=
  apMeanFree L sigma gamma ell 1 grade
    (apRadialContraction admissible grade (apMatchingFlux admissible data grade vector) +
      apTangentContraction admissible grade
        (apMatchingFlux admissible data grade (apMatchingRadialColumn admissible grade psi)))

theorem apMatchingPrimitive_deviation (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (vector : apGrade L sigma gamma ell 3 grade) (psi : apGrade L sigma gamma ell 1 grade) :
    apMatchingPrimitive admissible data grade vector psi =
      -apMeanFree L sigma gamma ell 1 grade (apRadialContraction admissible grade vector) +
        apMeanFree L sigma gamma ell 1 grade
          (apRadialContraction admissible grade (apMultiplier admissible (data.fluxDeviation grade) vector) +
            apTangentContraction admissible grade
              (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi))) := by
  unfold apMatchingPrimitive apMatchingFlux
  simp only [add_apply, neg_apply, ContinuousLinearMap.id_apply,
    map_add, map_neg, apMatchingTangentRadial_zero, neg_zero, zero_add]
  abel

end Grad.GaugeCoefficients.Physical.Compensated
