import AJW6HighRestrictionComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped Topology
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularOmegaGraph
open Grad.AnnularGrades Grad.AnnularFluxTrace Grad.AnnularCrossMaps Grad.AnnularOriginalHigh

theorem collarBulkRestriction_diagonal (lower upper : ℝ) (included : lower ≤ upper)
    (coefficient : HighAnnularMode → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ mode, |coefficient mode| ≤ constant) (field : AnnularBulk lower) :
    collarBulkRestriction HighAnnularMode 1 lower upper included
      (realLpDiagonal coefficient constant nonnegative bounded field) =
    realLpDiagonal coefficient constant nonnegative bounded
      (collarBulkRestriction HighAnnularMode 1 lower upper included field) := by
  apply lp.ext
  funext mode
  change collarL2Restriction 1 lower upper included ((coefficient mode : ℂ) • field mode) =
    (coefficient mode : ℂ) • collarL2Restriction 1 lower upper included (field mode)
  exact map_smul _ _ _

variable (lower upper length : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (lengthPositive : 0 < length) (included : lower ≤ upper)

include upperBounded

theorem highEnergyRestriction_diagonal (coefficient : HighAnnularMode → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ mode, |coefficient mode| ≤ constant) (field : annularEnergySpace lower length lowerPositive) :
    highEnergyRestriction lower upper length lowerPositive upperPositive included
      (annularEnergyDiagonal lower length lowerPositive coefficient constant nonnegative bounded field) =
    annularEnergyDiagonal upper length upperPositive coefficient constant nonnegative bounded
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field) := by
  apply annularEnergyValue_injective upper length upperPositive upperBounded
  rw [highEnergyRestriction_value, annularEnergyValue_diagonal, annularEnergyValue_diagonal,
    highEnergyRestriction_value, collarBulkRestriction_diagonal]

theorem highOmegaRestriction_diagonal (coefficient : HighAnnularMode → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ mode, |coefficient mode| ≤ constant) (field : annularOmegaGraph lower length lowerPositive lengthPositive) :
    highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included
      (annularOmegaGraphDiagonal lower length lowerPositive lengthPositive coefficient constant nonnegative bounded field) =
    annularOmegaGraphDiagonal upper length upperPositive lengthPositive coefficient constant nonnegative bounded
      (highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) := by
  apply annularOmegaGraph_value_injective upper length upperPositive upperBounded lengthPositive
  change collarBulkRestriction HighAnnularMode 1 lower upper included
    ((annularOmegaGraphDiagonal lower length lowerPositive lengthPositive coefficient constant nonnegative bounded field).val 0) =
    (annularOmegaGraphDiagonal upper length upperPositive lengthPositive coefficient constant nonnegative bounded
      (highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field)).val 0
  rw [annularOmegaGraphDiagonal_value, annularOmegaGraphDiagonal_value]
  exact collarBulkRestriction_diagonal lower upper included coefficient constant nonnegative bounded (field.val 0)

theorem highEnergyRestriction_decode (angular cell inserted : ℕ) (field : annularEnergySpace lower length lowerPositive) :
    highEnergyRestriction lower upper length lowerPositive upperPositive included
      (annularEnergyDecode lower length lowerPositive angular cell inserted field) =
    annularEnergyDecode upper length upperPositive angular cell inserted
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field) :=
  highEnergyRestriction_diagonal lower upper length lowerPositive upperPositive upperBounded included
    _ _ _ _ field

theorem highOmegaRestriction_decode (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length lowerPositive lengthPositive) :
    highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included
      (annularOmegaGraphDecode lower length lowerPositive lengthPositive angular cell inserted field) =
    annularOmegaGraphDecode upper length upperPositive lengthPositive angular cell inserted
      (highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) :=
  highOmegaRestriction_diagonal lower upper length lowerPositive upperPositive upperBounded lengthPositive included _ _ _ _ field

/-- Every literal energy grade, including the derivative and outer trace, is retained. -/
theorem highEnergyRestriction_hasGrade (angular cell inserted : ℕ) (field : annularEnergySpace lower length lowerPositive)
    (grade : HasAnnularEnergyGrade lower length lowerPositive angular cell inserted field) :
    HasAnnularEnergyGrade upper length upperPositive angular cell inserted
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field) := by
  obtain ⟨weighted, same⟩ := (annularEnergyDecode_range_iff lower length lowerPositive angular cell inserted field).mpr grade
  apply (annularEnergyDecode_range_iff upper length upperPositive angular cell inserted _).mp
  refine ⟨highEnergyRestriction lower upper length lowerPositive upperPositive included weighted, ?_⟩
  exact (highEnergyRestriction_decode lower upper length lowerPositive upperPositive upperBounded included angular cell inserted weighted).symm.trans
    (congrArg (highEnergyRestriction lower upper length lowerPositive upperPositive included) same)

/-- Both omega-normalized radial coordinates retain every original grade. -/
theorem highOmegaRestriction_hasGrade (angular cell inserted : ℕ)
    (field : annularOmegaGraph lower length lowerPositive lengthPositive)
    (grade : HasAnnularOmegaGrade lower angular cell inserted field.val) :
    HasAnnularOmegaGrade upper angular cell inserted
      (highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field).val := by
  obtain ⟨weighted, same⟩ := (annularOmegaGraphGrade_iff lower length lowerPositive lengthPositive angular cell inserted field).mp grade
  apply (annularOmegaGraphGrade_iff upper length upperPositive lengthPositive angular cell inserted _).mpr
  refine ⟨highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included weighted, ?_⟩
  exact (highOmegaRestriction_decode lower upper length lowerPositive upperPositive upperBounded lengthPositive included angular cell inserted weighted).symm.trans
    (congrArg (highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included) same)

end Grad.AnnularRestriction
