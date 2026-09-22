import GC17TraceProducts

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def gaugeColumnFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seedDerivative : CoefficientFamily L sigma gamma ell 2 2) : CoefficientFamily L sigma gamma ell 1 3 :=
  fun grade => constantFamily L sigma gamma ell (matrixOperator toroidalPhysicalColumn) grade +
    composeFamily admissible (constantFamily L sigma gamma ell (matrixOperator planarPhysicalInclusion))
      (composeFamily admissible seedDerivative (spatialColumnFamily L sigma gamma ell)) grade

def gaugeColumnProfile (seedDerivative : EstimateProfile) : EstimateProfile :=
  (constantProfile (matrixOperator toroidalPhysicalColumn)).add
    ((constantProfile (matrixOperator planarPhysicalInclusion)).comp 4
      (seedDerivative.comp 4 spatialColumnProfile))

def gaugePlanarFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seed : CoefficientFamily L sigma gamma ell 2 2) : CoefficientFamily L sigma gamma ell 3 3 :=
  composeFamily admissible (constantFamily L sigma gamma ell (matrixOperator planarFrameColumns))
    (composeFamily admissible (transposeFamily admissible seed)
      (constantFamily L sigma gamma ell (matrixOperator planarPhysicalInclusion.transpose)))

def gaugePlanarProfile (seed : EstimateProfile) : EstimateProfile :=
  (constantProfile (matrixOperator planarFrameColumns)).comp 4
    ((transposeProfile 4 2 2 seed).comp 4 (constantProfile (matrixOperator planarPhysicalInclusion.transpose)))

def gaugeStackFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seed seedDerivative : CoefficientFamily L sigma gamma ell 2 2) : CoefficientFamily L sigma gamma ell 3 3 :=
  fun grade => gaugePlanarFamily admissible seed grade +
    composeFamily admissible (constantFamily L sigma gamma ell (matrixOperator thirdFrameColumn))
      (transposeFamily admissible (gaugeColumnFamily admissible seedDerivative)) grade

def gaugeStackProfile (seed seedDerivative : EstimateProfile) : EstimateProfile :=
  (gaugePlanarProfile seed).add
    ((constantProfile (matrixOperator thirdFrameColumn)).comp 4
      (transposeProfile 4 1 3 (gaugeColumnProfile seedDerivative)))

def gaugeFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seed seedDerivative : CoefficientFamily L sigma gamma ell 2 2)
    (frameInverse : CoefficientFamily L sigma gamma ell 3 3) : CoefficientFamily L sigma gamma ell 3 3 :=
  composeFamily admissible (gaugeStackFamily admissible seed seedDerivative) (transposeFamily admissible frameInverse)

def gaugeProfile (seed seedDerivative frameInverse : EstimateProfile) : EstimateProfile :=
  (gaugeStackProfile seed seedDerivative).comp 4 (transposeProfile 4 3 3 frameInverse)

theorem gaugeColumnFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seedDerivative : CoefficientFamily L sigma gamma ell 2 2) (coherent : FamilyCoherent seedDerivative) :
    FamilyCoherent (gaugeColumnFamily admissible seedDerivative) :=
  (constantFamily_coherent L sigma gamma ell (matrixOperator toroidalPhysicalColumn)).add
    ((constantFamily_coherent L sigma gamma ell (matrixOperator planarPhysicalInclusion)).comp admissible
      (coherent.comp admissible (spatialColumnFamily_coherent L sigma gamma ell)))

theorem gaugePlanarFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seed : CoefficientFamily L sigma gamma ell 2 2) (coherent : FamilyCoherent seed) :
    FamilyCoherent (gaugePlanarFamily admissible seed) :=
  (constantFamily_coherent L sigma gamma ell (matrixOperator planarFrameColumns)).comp admissible
    ((transposeFamily_coherent admissible seed coherent).comp admissible
      (constantFamily_coherent L sigma gamma ell (matrixOperator planarPhysicalInclusion.transpose)))

theorem gaugeStackFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seed seedDerivative : CoefficientFamily L sigma gamma ell 2 2)
    (seedCoherent : FamilyCoherent seed) (derivativeCoherent : FamilyCoherent seedDerivative) :
    FamilyCoherent (gaugeStackFamily admissible seed seedDerivative) :=
  (gaugePlanarFamily_coherent admissible seed seedCoherent).add
    ((constantFamily_coherent L sigma gamma ell (matrixOperator thirdFrameColumn)).comp admissible
      (transposeFamily_coherent admissible _ (gaugeColumnFamily_coherent admissible seedDerivative derivativeCoherent)))

theorem gaugeFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seed seedDerivative : CoefficientFamily L sigma gamma ell 2 2)
    (frameInverse : CoefficientFamily L sigma gamma ell 3 3)
    (seedCoherent : FamilyCoherent seed) (derivativeCoherent : FamilyCoherent seedDerivative)
    (inverseCoherent : FamilyCoherent frameInverse) : FamilyCoherent (gaugeFamily admissible seed seedDerivative frameInverse) :=
  (gaugeStackFamily_coherent admissible seed seedDerivative seedCoherent derivativeCoherent).comp admissible
    (transposeFamily_coherent admissible frameInverse inverseCoherent)

theorem gaugeFamily_estimate {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {seedProfile derivativeProfile frameProfile : EstimateProfile}
    {seed seedReference derivative derivativeReference : CoefficientFamily L parameters.sigma0 parameters.gamma ell 2 2}
    {frameInverse frameReference : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (seedEstimate : FamilyEstimate parameters field rho epsilon 4 seedProfile seed seedReference)
    (derivativeEstimate : FamilyEstimate parameters field rho epsilon 4 derivativeProfile derivative derivativeReference)
    (frameEstimate : FamilyEstimate parameters field rho epsilon 4 frameProfile frameInverse frameReference) :
    FamilyEstimate parameters field rho epsilon 4 (gaugeProfile seedProfile derivativeProfile frameProfile)
      (gaugeFamily admissible seed derivative frameInverse) (gaugeFamily admissible seedReference derivativeReference frameReference) := by
  have columnEstimate := (constantFamily_estimate parameters admissible field rho epsilon 4
      (matrixOperator toroidalPhysicalColumn)).add
    (FamilyEstimate.comp admissible low
      (constantFamily_estimate parameters admissible field rho epsilon 4 (matrixOperator planarPhysicalInclusion))
      (FamilyEstimate.comp admissible low derivativeEstimate
        (spatialColumnFamily_estimate (L := L) (ell := ell) parameters field rho epsilon 4)))
  have planarEstimate := FamilyEstimate.comp admissible low
    (constantFamily_estimate parameters admissible field rho epsilon 4 (matrixOperator planarFrameColumns))
    (FamilyEstimate.comp admissible low (transposeFamily_estimate admissible low seedEstimate)
      (constantFamily_estimate parameters admissible field rho epsilon 4 (matrixOperator planarPhysicalInclusion.transpose)))
  have stackEstimate := planarEstimate.add (FamilyEstimate.comp admissible low
    (constantFamily_estimate parameters admissible field rho epsilon 4 (matrixOperator thirdFrameColumn))
    (transposeFamily_estimate admissible low columnEstimate))
  exact FamilyEstimate.comp admissible low stackEstimate (transposeFamily_estimate admissible low frameEstimate)

theorem gaugeColumnFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seedDerivative : CoefficientFamily L sigma gamma ell 2 2) (coherent : FamilyCoherent seedDerivative)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (gaugeColumnFamily admissible seedDerivative) grade angle point =
      toroidalPhysicalColumn + planarPhysicalInclusion * (familyMatrix seedDerivative grade angle point * spatialColumn point) := by
  have eCoherent := constantFamily_coherent L sigma gamma ell (matrixOperator toroidalPhysicalColumn)
  have iCoherent := constantFamily_coherent L sigma gamma ell (matrixOperator planarPhysicalInclusion)
  have yCoherent := spatialColumnFamily_coherent L sigma gamma ell
  have innerCoherent : FamilyCoherent (composeFamily admissible seedDerivative (spatialColumnFamily L sigma gamma ell)) :=
    coherent.comp admissible yCoherent
  have productCoherent : FamilyCoherent (composeFamily admissible
      (constantFamily L sigma gamma ell (matrixOperator planarPhysicalInclusion))
      (composeFamily admissible seedDerivative (spatialColumnFamily L sigma gamma ell))) :=
    iCoherent.comp admissible innerCoherent
  unfold gaugeColumnFamily
  rw [familyMatrix_add admissible _ _ eCoherent productCoherent,
    familyMatrix_comp admissible _ _ iCoherent innerCoherent, familyMatrix_comp admissible _ _ coherent yCoherent,
    familyMatrix_constant admissible, familyMatrix_constant admissible, familyMatrix_spatialColumn admissible]

theorem gaugePlanarFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seed : CoefficientFamily L sigma gamma ell 2 2) (coherent : FamilyCoherent seed)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (gaugePlanarFamily admissible seed) grade angle point =
      planarFrameColumns * ((familyMatrix seed grade angle point).transpose * planarPhysicalInclusion.transpose) := by
  have jCoherent := constantFamily_coherent L sigma gamma ell (matrixOperator planarFrameColumns)
  have iCoherent := constantFamily_coherent L sigma gamma ell (matrixOperator planarPhysicalInclusion.transpose)
  have tCoherent := transposeFamily_coherent admissible seed coherent
  have innerCoherent : FamilyCoherent (composeFamily admissible (transposeFamily admissible seed)
      (constantFamily L sigma gamma ell (matrixOperator planarPhysicalInclusion.transpose))) :=
    tCoherent.comp admissible iCoherent
  unfold gaugePlanarFamily
  rw [familyMatrix_comp admissible _ _ jCoherent innerCoherent, familyMatrix_comp admissible _ _ tCoherent iCoherent,
    familyMatrix_constant admissible, familyMatrix_constant admissible, familyMatrix_transpose admissible _ coherent]

theorem physicalGaugeMatrix_factor (seed derivative : Matrix (Fin 2) (Fin 2) ℂ)
    (inverseTranspose : Matrix (Fin 3) (Fin 3) ℂ) (point : ClosedDisk) :
    (planarFrameColumns * (seed.transpose * planarPhysicalInclusion.transpose) +
      thirdFrameColumn * (toroidalPhysicalColumn + planarPhysicalInclusion * (derivative * spatialColumn point)).transpose) *
        inverseTranspose = physicalGaugeMatrix seed derivative inverseTranspose point := by
  rw [Matrix.add_mul]
  simp only [Matrix.mul_assoc]
  ext row column
  fin_cases row <;>
    simp [physicalGaugeMatrix, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      planarFrameColumns, thirdFrameColumn] <;> ring

theorem gaugeFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (seed seedDerivative : CoefficientFamily L sigma gamma ell 2 2)
    (frameInverse : CoefficientFamily L sigma gamma ell 3 3)
    (seedCoherent : FamilyCoherent seed) (derivativeCoherent : FamilyCoherent seedDerivative)
    (inverseCoherent : FamilyCoherent frameInverse) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (gaugeFamily admissible seed seedDerivative frameInverse) grade angle point =
      physicalGaugeMatrix (familyMatrix seed grade angle point) (familyMatrix seedDerivative grade angle point)
        (familyMatrix frameInverse grade angle point).transpose point := by
  have stackCoherent := gaugeStackFamily_coherent admissible seed seedDerivative seedCoherent derivativeCoherent
  have planarCoherent := gaugePlanarFamily_coherent admissible seed seedCoherent
  have columnCoherent := gaugeColumnFamily_coherent admissible seedDerivative derivativeCoherent
  have eCoherent := constantFamily_coherent L sigma gamma ell (matrixOperator thirdFrameColumn)
  have columnTranspose := transposeFamily_coherent admissible _ columnCoherent
  have bottomCoherent : FamilyCoherent (composeFamily admissible
      (constantFamily L sigma gamma ell (matrixOperator thirdFrameColumn))
      (transposeFamily admissible (gaugeColumnFamily admissible seedDerivative))) := eCoherent.comp admissible columnTranspose
  unfold gaugeFamily
  rw [familyMatrix_comp admissible _ _ stackCoherent (transposeFamily_coherent admissible _ inverseCoherent),
    familyMatrix_transpose admissible _ inverseCoherent]
  unfold gaugeStackFamily
  rw [familyMatrix_add admissible _ _ planarCoherent bottomCoherent,
    familyMatrix_comp admissible _ _ eCoherent columnTranspose,
    familyMatrix_constant admissible, familyMatrix_transpose admissible _ columnCoherent,
    gaugeColumnFamily_matrix admissible _ derivativeCoherent, gaugePlanarFamily_matrix admissible _ seedCoherent]
  exact physicalGaugeMatrix_factor _ _ _ point

end Grad.GaugeCoefficients.Physical.Ledger
