import GC17FamilyMatrices

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def traceFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seedInverse : CoefficientFamily L sigma gamma ell 2 2)
    (frameInverse : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 3 1 :=
  composeFamily admissible
    (composeFamily admissible
      (composeFamily admissible (transposeFamily admissible (spatialColumnFamily L sigma gamma ell)) seedInverse)
      (constantFamily L sigma gamma ell (matrixOperator planarPhysicalInclusion.transpose)))
    (transposeFamily admissible frameInverse)

def traceProfile (seedInverse frameInverse : EstimateProfile) : EstimateProfile :=
  (((transposeProfile 4 1 2 spatialColumnProfile).comp 4 seedInverse).comp 4
    (constantProfile (matrixOperator planarPhysicalInclusion.transpose))).comp 4
      (transposeProfile 4 3 3 frameInverse)

theorem traceFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seedInverse : CoefficientFamily L sigma gamma ell 2 2)
    (frameInverse : CoefficientFamily L sigma gamma ell 3 3)
    (seedCoherent : FamilyCoherent seedInverse) (frameCoherent : FamilyCoherent frameInverse) :
    FamilyCoherent (traceFamily admissible seedInverse frameInverse) :=
  (((transposeFamily_coherent admissible _ (spatialColumnFamily_coherent L sigma gamma ell)).comp
    admissible seedCoherent).comp admissible
      (constantFamily_coherent L sigma gamma ell (matrixOperator planarPhysicalInclusion.transpose))).comp
        admissible (transposeFamily_coherent admissible frameInverse frameCoherent)

theorem traceFamily_estimate {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {seedProfile frameProfile : EstimateProfile}
    {seedInverse seedReference : CoefficientFamily L parameters.sigma0 parameters.gamma ell 2 2}
    {frameInverse frameReference : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (seedEstimate : FamilyEstimate parameters field rho epsilon 4 seedProfile seedInverse seedReference)
    (frameEstimate : FamilyEstimate parameters field rho epsilon 4 frameProfile frameInverse frameReference) :
    FamilyEstimate parameters field rho epsilon 4 (traceProfile seedProfile frameProfile)
      (traceFamily admissible seedInverse frameInverse) (traceFamily admissible seedReference frameReference) := by
  have columnEstimate := spatialColumnFamily_estimate (L := L) (ell := ell) parameters field rho epsilon 4
  have columnTranspose := transposeFamily_estimate admissible low columnEstimate
  have inverseTranspose := transposeFamily_estimate admissible low frameEstimate
  exact FamilyEstimate.comp admissible low
    (FamilyEstimate.comp admissible low (FamilyEstimate.comp admissible low columnTranspose seedEstimate)
      (constantFamily_estimate parameters admissible field rho epsilon 4 (matrixOperator planarPhysicalInclusion.transpose)))
    inverseTranspose

theorem traceFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seedInverse : CoefficientFamily L sigma gamma ell 2 2)
    (frameInverse : CoefficientFamily L sigma gamma ell 3 3)
    (seedCoherent : FamilyCoherent seedInverse) (frameCoherent : FamilyCoherent frameInverse)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (traceFamily admissible seedInverse frameInverse) grade angle point =
      (spatialColumn point).transpose * familyMatrix seedInverse grade angle point *
        planarPhysicalInclusion.transpose * (familyMatrix frameInverse grade angle point).transpose := by
  have columnCoherent := spatialColumnFamily_coherent L sigma gamma ell
  have columnTranspose := transposeFamily_coherent admissible _ columnCoherent
  have fixedCoherent := constantFamily_coherent L sigma gamma ell (matrixOperator planarPhysicalInclusion.transpose)
  have inverseTranspose := transposeFamily_coherent admissible frameInverse frameCoherent
  have firstCoherent : FamilyCoherent (composeFamily admissible
      (transposeFamily admissible (spatialColumnFamily L sigma gamma ell)) seedInverse) :=
    columnTranspose.comp admissible seedCoherent
  have secondCoherent : FamilyCoherent (composeFamily admissible
      (composeFamily admissible (transposeFamily admissible (spatialColumnFamily L sigma gamma ell)) seedInverse)
      (constantFamily L sigma gamma ell (matrixOperator planarPhysicalInclusion.transpose))) :=
    firstCoherent.comp admissible fixedCoherent
  unfold traceFamily
  rw [familyMatrix_comp admissible _ _ secondCoherent inverseTranspose,
    familyMatrix_comp admissible _ _ firstCoherent fixedCoherent,
    familyMatrix_comp admissible _ _ columnTranspose seedCoherent,
    familyMatrix_transpose admissible _ columnCoherent, familyMatrix_spatialColumn admissible,
    familyMatrix_constant admissible, familyMatrix_transpose admissible _ frameCoherent]

def rotatedProductFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {columns : ℕ} (selector : Matrix (Fin 3) (Fin columns) ℂ)
    (rotated frameInverse : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 3 columns :=
  composeFamily admissible
    (transposeFamily admissible (composeFamily admissible rotated
      (constantFamily L sigma gamma ell (matrixOperator selector))))
    (transposeFamily admissible frameInverse)

def rotatedProductProfile {columns : ℕ} (selector : Matrix (Fin 3) (Fin columns) ℂ)
    (rotated frameInverse : EstimateProfile) : EstimateProfile :=
  (transposeProfile 5 columns 3 (rotated.comp 5 (constantProfile (matrixOperator selector)))).comp 5
    (transposeProfile 5 3 3 frameInverse)

theorem rotatedProductFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {columns : ℕ} (selector : Matrix (Fin 3) (Fin columns) ℂ)
    (rotated frameInverse : CoefficientFamily L sigma gamma ell 3 3)
    (rotatedCoherent : FamilyCoherent rotated) (inverseCoherent : FamilyCoherent frameInverse) :
    FamilyCoherent (rotatedProductFamily admissible selector rotated frameInverse) :=
  (transposeFamily_coherent admissible _ (rotatedCoherent.comp admissible
    (constantFamily_coherent L sigma gamma ell (matrixOperator selector)))).comp admissible
      (transposeFamily_coherent admissible frameInverse inverseCoherent)

theorem rotatedProductFamily_estimate {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {rotatedProfile frameProfile : EstimateProfile}
    {rotated rotatedReference frameInverse frameReference : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (low : physicalBudget parameters field rho epsilon 5 ≤ 1)
    {columns : ℕ} (selector : Matrix (Fin 3) (Fin columns) ℂ)
    (rotatedEstimate : FamilyEstimate parameters field rho epsilon 5 rotatedProfile rotated rotatedReference)
    (inverseEstimate : FamilyEstimate parameters field rho epsilon 5 frameProfile frameInverse frameReference) :
    FamilyEstimate parameters field rho epsilon 5 (rotatedProductProfile selector rotatedProfile frameProfile)
      (rotatedProductFamily admissible selector rotated frameInverse)
      (rotatedProductFamily admissible selector rotatedReference frameReference) :=
  FamilyEstimate.comp admissible low
    (transposeFamily_estimate admissible low (FamilyEstimate.comp admissible low rotatedEstimate
      (constantFamily_estimate parameters admissible field rho epsilon 5 (matrixOperator selector))))
    (transposeFamily_estimate admissible low inverseEstimate)

theorem rotatedProductFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {columns : ℕ} (selector : Matrix (Fin 3) (Fin columns) ℂ)
    (rotated frameInverse : CoefficientFamily L sigma gamma ell 3 3)
    (rotatedCoherent : FamilyCoherent rotated) (inverseCoherent : FamilyCoherent frameInverse)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (rotatedProductFamily admissible selector rotated frameInverse) grade angle point =
      (familyMatrix rotated grade angle point * selector).transpose *
        (familyMatrix frameInverse grade angle point).transpose := by
  have fixedCoherent := constantFamily_coherent L sigma gamma ell (matrixOperator selector)
  have productCoherent : FamilyCoherent (composeFamily admissible rotated
      (constantFamily L sigma gamma ell (matrixOperator selector))) := rotatedCoherent.comp admissible fixedCoherent
  unfold rotatedProductFamily
  rw [familyMatrix_comp admissible _ _ (transposeFamily_coherent admissible _ productCoherent)
    (transposeFamily_coherent admissible _ inverseCoherent),
    familyMatrix_transpose admissible _ productCoherent, familyMatrix_transpose admissible _ inverseCoherent,
    familyMatrix_comp admissible _ _ rotatedCoherent fixedCoherent, familyMatrix_constant admissible]

end Grad.GaugeCoefficients.Physical.Ledger
