import GC17Transpose
import GC17PrimitiveEstimates
import GC17FixedMatrices

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def composeFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input middle output : ℕ} (outer : CoefficientFamily L sigma gamma ell middle output)
    (inner : CoefficientFamily L sigma gamma ell input middle) : CoefficientFamily L sigma gamma ell input output :=
  fun grade => coefficientComposition admissible grade (outer grade) (inner grade)

def familyMatrix {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    Matrix (Fin output) (Fin input) ℂ := operatorMatrix (coefficientPhysicalValue (family grade) angle point)

theorem familyMatrix_comp {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input middle output : ℕ} (outer : CoefficientFamily L sigma gamma ell middle output)
    (inner : CoefficientFamily L sigma gamma ell input middle)
    (outerCoherent : FamilyCoherent outer) (innerCoherent : FamilyCoherent inner)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (composeFamily admissible outer inner) grade angle point =
      familyMatrix outer grade angle point * familyMatrix inner grade angle point := by
  unfold familyMatrix composeFamily
  rw [family_physicalValue_comp admissible outer inner outerCoherent innerCoherent, operatorMatrix_comp]

theorem familyMatrix_add {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (first second : CoefficientFamily L sigma gamma ell input output)
    (firstCoherent : FamilyCoherent first) (secondCoherent : FamilyCoherent second)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (fun order => first order + second order) grade angle point =
      familyMatrix first grade angle point + familyMatrix second grade angle point := by
  unfold familyMatrix
  rw [family_physicalValue_add admissible first second firstCoherent secondCoherent, operatorMatrix_add]

theorem familyMatrix_sub {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (first second : CoefficientFamily L sigma gamma ell input output)
    (firstCoherent : FamilyCoherent first) (secondCoherent : FamilyCoherent second)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (fun order => first order - second order) grade angle point =
      familyMatrix first grade angle point - familyMatrix second grade angle point := by
  unfold familyMatrix
  rw [family_physicalValue_sub admissible first second firstCoherent secondCoherent, operatorMatrix_sub]

theorem familyMatrix_transpose {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (transposeFamily admissible family) grade angle point = (familyMatrix family grade angle point).transpose :=
  transposeFamily_physicalValue admissible family coherent grade angle point

theorem familyMatrix_constant {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (matrix : Matrix (Fin output) (Fin input) ℂ) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (constantFamily L sigma gamma ell (matrixOperator matrix)) grade angle point = matrix :=
  constantMatrix_physicalValue admissible matrix grade angle point

theorem familyMatrix_zero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (input output grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (zeroFamily L sigma gamma ell input output) grade angle point = 0 := by
  unfold familyMatrix
  rw [coherent_physicalValue _ (zeroFamily_coherent L sigma gamma ell input output)]
  change operatorMatrix (seedFourierCLM admissible input output angle point 0) = 0
  rw [map_zero]
  rfl

theorem familyMatrix_identity (L sigma gamma ell : ℝ) (dimension grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (identityFamily L sigma gamma ell dimension) grade angle point = 1 := by
  unfold familyMatrix identityFamily
  rw [identityFamily_physicalValue, operatorMatrix_one]

theorem familyMatrix_referenceFrame {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (constantFamily L sigma gamma ell referenceFrame) grade angle point = operatorMatrix referenceFrame := by
  unfold familyMatrix
  rw [constantFamily_physicalValue admissible]

theorem fullFrameFamily_matrix {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (fullFrameFamily parameters L ell epsilon field) grade angle point =
      physicalFrameMatrix parameters L ell epsilon field angle point := by
  unfold familyMatrix fullFrameFamily
  rw [family_physicalValue_add admissible _ _
    (constantFamily_coherent L parameters.sigma0 parameters.gamma ell referenceFrame)
    (actualFrameFamily_coherent parameters admissible epsilon field), constantFamily_physicalValue admissible,
    coherent_physicalValue _ (actualFrameFamily_coherent parameters admissible epsilon field)]
  rfl

theorem seedMatrixFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter : ℝ) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (seedMatrixFamily admissible rho alpha delta parameter) grade angle point =
      physicalSeedMatrix rho alpha delta parameter angle := by
  unfold familyMatrix seedMatrixFamily
  rw [family_physicalValue_add admissible _ _ (identityFamily_coherent L sigma gamma ell 2)
    (seedDeviationFamily_coherent admissible rho alpha delta parameter), identityFamily_physicalValue,
    coherent_physicalValue _ (seedDeviationFamily_coherent admissible rho alpha delta parameter), seedMatrixDeviation_fourier]
  congr 1
  abel

theorem familyMatrix_spatialColumn {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (spatialColumnFamily L sigma gamma ell) grade angle point = spatialColumn point :=
  spatialColumnFamily_physicalValue admissible grade angle point

end Grad.GaugeCoefficients.Physical.Ledger
