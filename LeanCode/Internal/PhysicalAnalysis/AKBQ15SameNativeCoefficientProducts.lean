import AKBQ14SameScaledForceMatrices
import AKBQ3SameMatrixActionAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Grad.ActualScaledNativeCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualCurrentPrimitives Grad.Constraints.Gauges

 theorem nativePlanarSelection (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : ComplexEuclidean 3) :
    WithLp.toLp 2 ((planarFrameColumns.transpose * matrix).mulVec value) =
      planarPartMap (WithLp.toLp 2 (matrix.mulVec value)) := by
  rw [← Matrix.mulVec_mulVec]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [planarFrameColumns,Matrix.mulVec,dotProduct,Fin.sum_univ_three,planarPartMap]

 theorem nativeThirdSelection (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : ComplexEuclidean 3) :
    WithLp.toLp 2 ((thirdFrameColumn.transpose * matrix).mulVec value) =
      toroidalPartMap (WithLp.toLp 2 (matrix.mulVec value)) := by
  rw [← Matrix.mulVec_mulVec]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [thirdFrameColumn,Matrix.mulVec,dotProduct,Fin.sum_univ_three,toroidalPartMap]

variable {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {field : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)

include low

/-- Actual scaled planar coefficient product, with the original full native matrix action retained. -/
theorem scaledLedgerPlanarForce_action (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (value : ComplexEuclidean 3) :
    coefficientPhysicalValue (ledger.val.rotatedPlanarProduct grade) angle point value =
      planarPartMap (coefficientPhysicalValue (forceMatrixFamily parameters L epsilon field grade) angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) value) := by
  rw [operatorMatrix_action]
  have matrix := congrArg (fun matrix : Matrix (Fin 2) (Fin 3) ℂ => WithLp.toLp 2 (matrix.mulVec value))
    (scaledLedgerPlanarForce_native ledger low grade angle point)
  exact matrix.trans ((nativePlanarSelection _ value).trans
    (congrArg planarPartMap (operatorMatrix_action _ value).symm))

/-- Actual scaled third coefficient product; its -2L force normalization may be applied after this equality. -/
theorem scaledLedgerThirdForce_action (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (value : ComplexEuclidean 3) :
    coefficientPhysicalValue (ledger.val.rotatedThirdProduct grade) angle point value =
      toroidalPartMap (coefficientPhysicalValue (forceMatrixFamily parameters L epsilon field grade) angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) value) := by
  rw [operatorMatrix_action]
  have matrix := congrArg (fun matrix : Matrix (Fin 1) (Fin 3) ℂ => WithLp.toLp 2 (matrix.mulVec value))
    (scaledLedgerThirdForce_native ledger low grade angle point)
  exact matrix.trans ((nativeThirdSelection _ value).trans
    (congrArg toroidalPartMap (operatorMatrix_action _ value).symm))

/-- Actual scaled h product is the full signed native cofactor action plus the same covariant itself. -/
theorem scaledLedgerFlux_action (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (value : ComplexEuclidean 3) :
    coefficientPhysicalValue (ledger.val.fluxDeviation grade) angle point value =
      coefficientPhysicalValue (originalCofactorFamily parameters L epsilon field grade) angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) value + value := by
  rw [operatorMatrix_action]
  have matrix := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℂ => WithLp.toLp 2 (matrix.mulVec value))
    (scaledLedgerFlux_native ledger low grade angle point)
  refine matrix.trans ?_
  rw [Matrix.add_mulVec,Matrix.one_mulVec]
  have native := operatorMatrix_action
    (coefficientPhysicalValue (originalCofactorFamily parameters L epsilon field grade) angle
      (physicalScaledPoint ell admissible.2.2.2.1.le
        (admissible.2.2.2.2.trans (min_le_left _ _)) point)) value
  exact congrArg (fun other : ComplexEuclidean 3 => other + value) native.symm

end Grad.ActualScaledNativeCoefficients
