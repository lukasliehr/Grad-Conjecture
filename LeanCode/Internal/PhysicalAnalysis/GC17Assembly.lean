import GC17Flux

noncomputable section

set_option maxHeartbeats 1800000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

/-- Finite coefficient recipes, always subtracting the same literal circle
recipe. The public witness below instantiates every input from the physical state. -/
def assembleData {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (frame inverse : CoefficientFamily L sigma gamma ell 3 3)
    (seed seedInverse derivative : CoefficientFamily L sigma gamma ell 2 2)
    (rotated : CoefficientFamily L sigma gamma ell 3 3) : LedgerData L sigma gamma ell where
  frameInverse := inverse
  seedInverse := seedInverse
  inverseTransposeDeviation := fun grade => transposeFamily admissible inverse grade -
    transposeFamily admissible (constantFamily L sigma gamma ell referenceFrame) grade
  gaugeDeviation := fun grade => gaugeFamily admissible seed derivative inverse grade -
    gaugeFamily admissible (identityFamily L sigma gamma ell 2) (zeroFamily L sigma gamma ell 2 2)
      (constantFamily L sigma gamma ell referenceFrame) grade
  fluxDeviation := fun grade => fluxFamily admissible frame inverse grade -
    fluxFamily admissible (constantFamily L sigma gamma ell referenceFrame)
      (constantFamily L sigma gamma ell referenceFrame) grade
  traceDeviation := fun grade => traceFamily admissible seedInverse inverse grade -
    traceFamily admissible (identityFamily L sigma gamma ell 2)
      (constantFamily L sigma gamma ell referenceFrame) grade
  rotatedFrame := rotated
  rotatedPlanarProduct := fun grade => rotatedProductFamily admissible planarFrameColumns rotated inverse grade -
    rotatedProductFamily admissible planarFrameColumns (zeroFamily L sigma gamma ell 3 3)
      (constantFamily L sigma gamma ell referenceFrame) grade
  rotatedThirdProduct := fun grade => rotatedProductFamily admissible thirdFrameColumn rotated inverse grade -
    rotatedProductFamily admissible thirdFrameColumn (zeroFamily L sigma gamma ell 3 3)
      (constantFamily L sigma gamma ell referenceFrame) grade

theorem assembleData_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (frame inverse : CoefficientFamily L sigma gamma ell 3 3)
    (seed seedInverse derivative : CoefficientFamily L sigma gamma ell 2 2)
    (rotated : CoefficientFamily L sigma gamma ell 3 3)
    (frameCoherent : FamilyCoherent frame) (inverseCoherent : FamilyCoherent inverse)
    (seedCoherent : FamilyCoherent seed) (seedInverseCoherent : FamilyCoherent seedInverse)
    (derivativeCoherent : FamilyCoherent derivative) (rotatedCoherent : FamilyCoherent rotated) :
    LedgerCoherent (assembleData admissible frame inverse seed seedInverse derivative rotated) := by
  have qCoherent := constantFamily_coherent L sigma gamma ell referenceFrame
  have iCoherent : FamilyCoherent (identityFamily L sigma gamma ell 2) := identityFamily_coherent L sigma gamma ell 2
  have z2Coherent := zeroFamily_coherent L sigma gamma ell 2 2
  have z3Coherent := zeroFamily_coherent L sigma gamma ell 3 3
  exact ⟨inverseCoherent, seedInverseCoherent,
    (transposeFamily_coherent admissible inverse inverseCoherent).sub (transposeFamily_coherent admissible _ qCoherent),
    (gaugeFamily_coherent admissible seed derivative inverse seedCoherent derivativeCoherent inverseCoherent).sub
      (gaugeFamily_coherent admissible _ _ _ iCoherent z2Coherent qCoherent),
    (fluxFamily_coherent admissible frame inverse frameCoherent inverseCoherent).sub
      (fluxFamily_coherent admissible _ _ qCoherent qCoherent),
    (traceFamily_coherent admissible seedInverse inverse seedInverseCoherent inverseCoherent).sub
      (traceFamily_coherent admissible _ _ iCoherent qCoherent), rotatedCoherent,
    (rotatedProductFamily_coherent admissible planarFrameColumns rotated inverse rotatedCoherent inverseCoherent).sub
      (rotatedProductFamily_coherent admissible planarFrameColumns _ _ z3Coherent qCoherent),
    (rotatedProductFamily_coherent admissible thirdFrameColumn rotated inverse rotatedCoherent inverseCoherent).sub
      (rotatedProductFamily_coherent admissible thirdFrameColumn _ _ z3Coherent qCoherent)⟩

theorem assembleData_transpose_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (frame inverse : CoefficientFamily L sigma gamma ell 3 3)
    (seed seedInverse derivative : CoefficientFamily L sigma gamma ell 2 2)
    (rotated : CoefficientFamily L sigma gamma ell 3 3) (inverseCoherent : FamilyCoherent inverse)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (assembleData admissible frame inverse seed seedInverse derivative rotated).inverseTransposeDeviation
      grade angle point = (familyMatrix inverse grade angle point).transpose - (operatorMatrix referenceFrame).transpose := by
  have qCoherent := constantFamily_coherent L sigma gamma ell referenceFrame
  change familyMatrix (fun q => transposeFamily admissible inverse q -
    transposeFamily admissible (constantFamily L sigma gamma ell referenceFrame) q) grade angle point = _
  rw [familyMatrix_sub admissible _ _ (transposeFamily_coherent admissible inverse inverseCoherent)
    (transposeFamily_coherent admissible _ qCoherent), familyMatrix_transpose admissible inverse inverseCoherent,
    familyMatrix_transpose admissible _ qCoherent, familyMatrix_referenceFrame admissible]

theorem assembleData_gauge_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (frame inverse : CoefficientFamily L sigma gamma ell 3 3)
    (seed seedInverse derivative : CoefficientFamily L sigma gamma ell 2 2)
    (rotated : CoefficientFamily L sigma gamma ell 3 3)
    (seedCoherent : FamilyCoherent seed) (derivativeCoherent : FamilyCoherent derivative)
    (inverseCoherent : FamilyCoherent inverse) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (assembleData admissible frame inverse seed seedInverse derivative rotated).gaugeDeviation grade angle point =
      physicalGaugeMatrix (familyMatrix seed grade angle point) (familyMatrix derivative grade angle point)
        (familyMatrix inverse grade angle point).transpose point - 1 := by
  have iCoherent : FamilyCoherent (identityFamily L sigma gamma ell 2) := identityFamily_coherent L sigma gamma ell 2
  have referenceCoherent := gaugeFamily_coherent admissible _ _ _ iCoherent
    (zeroFamily_coherent L sigma gamma ell 2 2) (constantFamily_coherent L sigma gamma ell referenceFrame)
  change familyMatrix (fun q => gaugeFamily admissible seed derivative inverse q -
    gaugeFamily admissible (identityFamily L sigma gamma ell 2) (zeroFamily L sigma gamma ell 2 2)
      (constantFamily L sigma gamma ell referenceFrame) q) grade angle point = _
  rw [familyMatrix_sub admissible _ _
    (gaugeFamily_coherent admissible seed derivative inverse seedCoherent derivativeCoherent inverseCoherent) referenceCoherent,
    gaugeFamily_matrix admissible seed derivative inverse seedCoherent derivativeCoherent inverseCoherent,
    gaugeFamily_circle admissible]

theorem assembleData_flux_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (frame inverse : CoefficientFamily L sigma gamma ell 3 3)
    (seed seedInverse derivative : CoefficientFamily L sigma gamma ell 2 2)
    (rotated : CoefficientFamily L sigma gamma ell 3 3)
    (frameCoherent : FamilyCoherent frame) (inverseCoherent : FamilyCoherent inverse)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (assembleData admissible frame inverse seed seedInverse derivative rotated).fluxDeviation grade angle point =
      (familyMatrix frame grade angle point).det •
        (familyMatrix inverse grade angle point * (familyMatrix inverse grade angle point).transpose) + 1 := by
  have qCoherent := constantFamily_coherent L sigma gamma ell referenceFrame
  change familyMatrix (fun q => fluxFamily admissible frame inverse q -
    fluxFamily admissible (constantFamily L sigma gamma ell referenceFrame)
      (constantFamily L sigma gamma ell referenceFrame) q) grade angle point = _
  rw [familyMatrix_sub admissible _ _ (fluxFamily_coherent admissible frame inverse frameCoherent inverseCoherent)
    (fluxFamily_coherent admissible _ _ qCoherent qCoherent),
    fluxFamily_matrix admissible frame inverse frameCoherent inverseCoherent, fluxFamily_circle admissible, sub_neg_eq_add]

theorem assembleData_trace_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (frame inverse : CoefficientFamily L sigma gamma ell 3 3)
    (seed seedInverse derivative : CoefficientFamily L sigma gamma ell 2 2)
    (rotated : CoefficientFamily L sigma gamma ell 3 3)
    (seedInverseCoherent : FamilyCoherent seedInverse) (inverseCoherent : FamilyCoherent inverse)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (assembleData admissible frame inverse seed seedInverse derivative rotated).traceDeviation grade angle point =
      (spatialColumn point).transpose * familyMatrix seedInverse grade angle point *
        planarPhysicalInclusion.transpose * (familyMatrix inverse grade angle point).transpose - circleTraceCovector point := by
  have iCoherent : FamilyCoherent (identityFamily L sigma gamma ell 2) := identityFamily_coherent L sigma gamma ell 2
  have qCoherent := constantFamily_coherent L sigma gamma ell referenceFrame
  change familyMatrix (fun q => traceFamily admissible seedInverse inverse q -
    traceFamily admissible (identityFamily L sigma gamma ell 2)
      (constantFamily L sigma gamma ell referenceFrame) q) grade angle point = _
  rw [familyMatrix_sub admissible _ _ (traceFamily_coherent admissible seedInverse inverse seedInverseCoherent inverseCoherent)
    (traceFamily_coherent admissible _ _ iCoherent qCoherent),
    traceFamily_matrix admissible seedInverse inverse seedInverseCoherent inverseCoherent, traceFamily_circle admissible]

theorem rotatedProduct_deviation_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {columns : ℕ} (selector : Matrix (Fin 3) (Fin columns) ℂ)
    (rotated inverse : CoefficientFamily L sigma gamma ell 3 3)
    (rotatedCoherent : FamilyCoherent rotated) (inverseCoherent : FamilyCoherent inverse)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (fun q => rotatedProductFamily admissible selector rotated inverse q -
      rotatedProductFamily admissible selector (zeroFamily L sigma gamma ell 3 3)
        (constantFamily L sigma gamma ell referenceFrame) q) grade angle point =
      (familyMatrix rotated grade angle point * selector).transpose * (familyMatrix inverse grade angle point).transpose := by
  rw [familyMatrix_sub admissible _ _
    (rotatedProductFamily_coherent admissible selector rotated inverse rotatedCoherent inverseCoherent)
    (rotatedProductFamily_coherent admissible selector _ _ (zeroFamily_coherent L sigma gamma ell 3 3)
      (constantFamily_coherent L sigma gamma ell referenceFrame)),
    rotatedProductFamily_matrix admissible selector rotated inverse rotatedCoherent inverseCoherent,
    rotatedProductFamily_circle admissible, sub_zero]

end Grad.GaugeCoefficients.Physical.Ledger
