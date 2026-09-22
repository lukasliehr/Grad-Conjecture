import AJZ5ExactOriginalSourceRowRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularSourceGraph
open Grad.AnnularVariational Grad.AnnularStrongData Grad.AnnularCurrentSource

section Pair
variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']

def restrictionHilbertPairMap (first : E →L[ℝ] E') (second : F →L[ℝ] F') :
    WithLp 2 (E × F) →L[ℝ] WithLp 2 (E' × F') :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E' F').symm.toContinuousLinearMap.comp
    ((first.prodMap second).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap)

theorem restrictionHilbertPairMap_apply (first : E →L[ℝ] E') (second : F →L[ℝ] F')
    (field : WithLp 2 (E × F)) :
    (restrictionHilbertPairMap first second field).ofLp = (first field.ofLp.1, second field.ofLp.2) := rfl

theorem restrictionHilbertPairMap_bound (first : E →L[ℝ] E') (second : F →L[ℝ] F')
    (firstBound : ∀ field, ‖first field‖ ≤ ‖field‖) (secondBound : ∀ field, ‖second field‖ ≤ ‖field‖)
    (data : WithLp 2 (E × F)) : ‖restrictionHilbertPairMap first second data‖ ≤ ‖data‖ := by
  have source := WithLp.prod_norm_sq_eq_of_L2 (restrictionHilbertPairMap first second data)
  have target := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖restrictionHilbertPairMap first second data‖ ^ 2 = ‖first data.ofLp.1‖ ^ 2 + ‖second data.ofLp.2‖ ^ 2 at source
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at target
  have firstSquare := pow_le_pow_left₀ (norm_nonneg _) (firstBound data.ofLp.1) 2
  have secondSquare := pow_le_pow_left₀ (norm_nonneg _) (secondBound data.ofLp.2) 2
  nlinarith only [source,target,firstSquare,secondSquare,norm_nonneg (restrictionHilbertPairMap first second data),norm_nonneg data]
end Pair

def originalSourceGraphPairRestriction (parameters : PhaseParameters) (lower upper : ℝ) (included : lower ≤ upper) :
    HighKnownGraphHilbert parameters lower →L[ℝ] HighKnownGraphHilbert parameters upper :=
  restrictionHilbertPairMap (sourceGraphRestriction parameters 1 lower upper included 1 0 0)
    (sourceGraphRestriction parameters 1 lower upper included 0 0 0)

theorem originalSourceGraphPairRestriction_bound (parameters : PhaseParameters) (lower upper : ℝ)
    (included : lower ≤ upper) (field : HighKnownGraphHilbert parameters lower) :
    ‖originalSourceGraphPairRestriction parameters lower upper included field‖ ≤ ‖field‖ :=
  restrictionHilbertPairMap_bound _ _
    (sourceGraphRestriction_bound parameters 1 lower upper included 1 0 0)
    (sourceGraphRestriction_bound parameters 1 lower upper included 0 0 0) field

def originalResidualPairRestriction (lower upper : ℝ) (included : lower ≤ upper) :
    WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower) →L[ℝ]
      WithLp 2 (DivisionRow 1 upper × DivisionRow 1 upper) :=
  restrictionHilbertPairMap ((originalBulkRestriction 1 lower upper included).restrictScalars ℝ)
    ((originalBulkRestriction 1 lower upper included).restrictScalars ℝ)

theorem originalResidualPairRestriction_bound (lower upper : ℝ) (included : lower ≤ upper)
    (field : WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower)) :
    ‖originalResidualPairRestriction lower upper included field‖ ≤ ‖field‖ :=
  restrictionHilbertPairMap_bound _ _ (collarBulkRestriction_bound (ℤ × ℤ) 1 lower upper included)
    (collarBulkRestriction_bound (ℤ × ℤ) 1 lower upper included) field

/-- The exact four original source/residual blocks of AK31. F0 and F2 keep
both genuine H1 coordinates; full F1 and strengthened G3 restrict in bulk. -/
def originalFullSourceRestriction (parameters : PhaseParameters) (lower upper : ℝ) (included : lower ≤ upper) :
    WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower)) →L[ℝ]
      WithLp 2 (HighKnownGraphHilbert parameters upper × WithLp 2 (DivisionRow 1 upper × DivisionRow 1 upper)) :=
  restrictionHilbertPairMap (originalSourceGraphPairRestriction parameters lower upper included)
    (originalResidualPairRestriction lower upper included)

theorem originalFullSourceRestriction_bound (parameters : PhaseParameters) (lower upper : ℝ) (included : lower ≤ upper)
    (field : WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))) :
    ‖originalFullSourceRestriction parameters lower upper included field‖ ≤ ‖field‖ :=
  restrictionHilbertPairMap_bound _ _ (originalSourceGraphPairRestriction_bound parameters lower upper included)
    (originalResidualPairRestriction_bound lower upper included) field

theorem originalFullSourceRestriction_coordinates (parameters : PhaseParameters) (lower upper : ℝ) (included : lower ≤ upper)
    (field : WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))) :
    let output := originalFullSourceRestriction parameters lower upper included field
    output.ofLp.1.ofLp.1 = sourceGraphRestriction parameters 1 lower upper included 1 0 0 field.ofLp.1.ofLp.1 ∧
    output.ofLp.1.ofLp.2 = sourceGraphRestriction parameters 1 lower upper included 0 0 0 field.ofLp.1.ofLp.2 ∧
    output.ofLp.2.ofLp.1 = originalBulkRestriction 1 lower upper included field.ofLp.2.ofLp.1 ∧
    output.ofLp.2.ofLp.2 = originalBulkRestriction 1 lower upper included field.ofLp.2.ofLp.2 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem originalFullSourceRestriction_id (parameters : PhaseParameters) (lower : ℝ)
    (field : WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))) :
    originalFullSourceRestriction parameters lower lower le_rfl field = field := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  apply Prod.ext
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    exact Prod.ext (sourceGraphRestriction_id parameters 1 lower 1 0 0 field.ofLp.1.ofLp.1)
      (sourceGraphRestriction_id parameters 1 lower 0 0 0 field.ofLp.1.ofLp.2)
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    exact Prod.ext (collarBulkRestriction_id (ℤ × ℤ) 1 lower field.ofLp.2.ofLp.1)
      (collarBulkRestriction_id (ℤ × ℤ) 1 lower field.ofLp.2.ofLp.2)

theorem originalFullSourceRestriction_comp (parameters : PhaseParameters) (lower middle upper : ℝ)
    (first : lower ≤ middle) (second : middle ≤ upper)
    (field : WithLp 2 (HighKnownGraphHilbert parameters lower × WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))) :
    originalFullSourceRestriction parameters middle upper second
        (originalFullSourceRestriction parameters lower middle first field) =
      originalFullSourceRestriction parameters lower upper (first.trans second) field := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  apply Prod.ext
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    exact Prod.ext (sourceGraphRestriction_comp parameters 1 lower middle upper first second 1 0 0 field.ofLp.1.ofLp.1)
      (sourceGraphRestriction_comp parameters 1 lower middle upper first second 0 0 0 field.ofLp.1.ofLp.2)
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    exact Prod.ext (collarBulkRestriction_comp (ℤ × ℤ) 1 lower middle upper first second field.ofLp.2.ofLp.1)
      (collarBulkRestriction_comp (ℤ × ℤ) 1 lower middle upper first second field.ofLp.2.ofLp.2)

end Grad.AnnularRestriction
