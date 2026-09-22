import GC17Determinant
import GC17GaugeFormula

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def fluxFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (frame inverse : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 3 3 :=
  composeFamily admissible (scalarLiftFamily admissible 3 (determinantFamily admissible frame))
    (composeFamily admissible inverse (transposeFamily admissible inverse))

def fluxProfile (frame inverse : EstimateProfile) : EstimateProfile :=
  (scalarLiftProfile 3 (determinantProfile frame)).comp 4 (inverse.comp 4 (transposeProfile 4 3 3 inverse))

theorem fluxFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (frame inverse : CoefficientFamily L sigma gamma ell 3 3)
    (frameCoherent : FamilyCoherent frame) (inverseCoherent : FamilyCoherent inverse) :
    FamilyCoherent (fluxFamily admissible frame inverse) :=
  (scalarLiftFamily_coherent admissible 3 _ (determinantFamily_coherent admissible frame frameCoherent)).comp admissible
    (inverseCoherent.comp admissible (transposeFamily_coherent admissible inverse inverseCoherent))

theorem fluxFamily_estimate {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {frameProfile inverseProfile : EstimateProfile}
    {frame frameReference inverse inverseReference : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (frameEstimate : FamilyEstimate parameters field rho epsilon 4 frameProfile frame frameReference)
    (inverseEstimate : FamilyEstimate parameters field rho epsilon 4 inverseProfile inverse inverseReference) :
    FamilyEstimate parameters field rho epsilon 4 (fluxProfile frameProfile inverseProfile)
      (fluxFamily admissible frame inverse) (fluxFamily admissible frameReference inverseReference) :=
  FamilyEstimate.comp admissible low
    (scalarLiftFamily_estimate admissible low 3 (determinantFamily_estimate admissible low frameEstimate))
    (FamilyEstimate.comp admissible low inverseEstimate (transposeFamily_estimate admissible low inverseEstimate))

theorem fluxFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (frame inverse : CoefficientFamily L sigma gamma ell 3 3)
    (frameCoherent : FamilyCoherent frame) (inverseCoherent : FamilyCoherent inverse)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (fluxFamily admissible frame inverse) grade angle point =
      (familyMatrix frame grade angle point).det •
        (familyMatrix inverse grade angle point * (familyMatrix inverse grade angle point).transpose) := by
  have determinantCoherent := determinantFamily_coherent admissible frame frameCoherent
  have liftCoherent := scalarLiftFamily_coherent admissible 3 _ determinantCoherent
  have transposeCoherent := transposeFamily_coherent admissible inverse inverseCoherent
  have productCoherent : FamilyCoherent (composeFamily admissible inverse (transposeFamily admissible inverse)) :=
    inverseCoherent.comp admissible transposeCoherent
  unfold fluxFamily
  rw [familyMatrix_comp admissible _ _ liftCoherent productCoherent,
    scalarLiftFamily_matrix admissible 3 _ determinantCoherent grade angle point _
      (determinantFamily_matrix admissible frame frameCoherent grade angle point),
    familyMatrix_comp admissible _ _ inverseCoherent transposeCoherent,
    familyMatrix_transpose admissible _ inverseCoherent, Matrix.smul_mul, Matrix.one_mul]

theorem physicalGaugeMatrix_circle (point : ClosedDisk) :
    physicalGaugeMatrix 1 0 (operatorMatrix referenceFrame).transpose point = 1 := by
  rw [← physicalGaugeMatrix_factor]
  rw [referenceFrame_matrix_transpose, referenceFrame_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, planarFrameColumns,
      planarPhysicalInclusion, toroidalPhysicalColumn, thirdFrameColumn, Matrix.cons_val_two]

theorem gaugeFamily_circle {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (gaugeFamily admissible (identityFamily L sigma gamma ell 2)
      (zeroFamily L sigma gamma ell 2 2) (constantFamily L sigma gamma ell referenceFrame)) grade angle point = 1 := by
  have identityCoherent : FamilyCoherent (identityFamily L sigma gamma ell 2) :=
    identityFamily_coherent L sigma gamma ell 2
  rw [gaugeFamily_matrix admissible _ _ _ identityCoherent
    (zeroFamily_coherent L sigma gamma ell 2 2) (constantFamily_coherent L sigma gamma ell referenceFrame),
    familyMatrix_identity, familyMatrix_zero admissible, familyMatrix_referenceFrame admissible,
    physicalGaugeMatrix_circle]

theorem fluxFamily_circle {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (fluxFamily admissible (constantFamily L sigma gamma ell referenceFrame)
      (constantFamily L sigma gamma ell referenceFrame)) grade angle point = -1 := by
  rw [fluxFamily_matrix admissible _ _ (constantFamily_coherent L sigma gamma ell referenceFrame)
    (constantFamily_coherent L sigma gamma ell referenceFrame), familyMatrix_referenceFrame admissible,
    referenceFrame_matrix_det, referenceFrame_matrix_transpose, referenceFrame_matrix_square]
  simp

theorem traceFamily_circle {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (traceFamily admissible (identityFamily L sigma gamma ell 2)
      (constantFamily L sigma gamma ell referenceFrame)) grade angle point = circleTraceCovector point := by
  have identityCoherent : FamilyCoherent (identityFamily L sigma gamma ell 2) :=
    identityFamily_coherent L sigma gamma ell 2
  rw [traceFamily_matrix admissible _ _ identityCoherent
    (constantFamily_coherent L sigma gamma ell referenceFrame), familyMatrix_identity,
    familyMatrix_referenceFrame admissible]
  exact circleTrace_matrix point

theorem rotatedProductFamily_circle {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {columns : ℕ} (selector : Matrix (Fin 3) (Fin columns) ℂ) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (rotatedProductFamily admissible selector (zeroFamily L sigma gamma ell 3 3)
      (constantFamily L sigma gamma ell referenceFrame)) grade angle point = 0 := by
  rw [rotatedProductFamily_matrix admissible selector _ _ (zeroFamily_coherent L sigma gamma ell 3 3)
    (constantFamily_coherent L sigma gamma ell referenceFrame), familyMatrix_zero admissible]
  simp

theorem seedDerivativeFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter : ℝ) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (fun q => seedDerivativeCoefficient admissible q rho alpha delta parameter) grade angle point =
      operatorMatrix (fourierEvaluation (seedDerivativeCoefficient admissible 0 rho alpha delta parameter) angle point) := by
  unfold familyMatrix
  rw [coherent_physicalValue _ (seedDerivativeFamily_coherent admissible rho alpha delta parameter)]

end Grad.GaugeCoefficients.Physical.Ledger
