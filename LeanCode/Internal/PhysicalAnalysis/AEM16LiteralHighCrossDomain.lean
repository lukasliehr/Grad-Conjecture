import AEM15ActualLowToHighBulkCross

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularOmegaGraph Grad.AnnularTiltedReference

/-- Literal BF high carrier: the existing b-weighted W coordinate and the
actual closed Domega graph. Flux derivatives are constrained by that graph. -/
abbrev CrossHighSpace (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :=
  WithLp 2 ((annularEnergySpace lower length positive) × (annularOmegaGraph lower length positive lengthPositive))

def crossHighW (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    CrossHighSpace lower length positive lengthPositive →L[ℂ] annularEnergySpace lower length positive :=
  (ContinuousLinearMap.fst ℂ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap

def crossHighFlux (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    CrossHighSpace lower length positive lengthPositive →L[ℂ] annularOmegaGraph lower length positive lengthPositive :=
  (ContinuousLinearMap.snd ℂ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap

theorem crossHighW_bound (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CrossHighSpace lower length positive lengthPositive) : ‖crossHighW lower length positive lengthPositive field‖ ≤ ‖field‖ := by
  have square := WithLp.prod_norm_sq_eq_of_L2 field
  change ‖field‖ ^ 2 = ‖crossHighW lower length positive lengthPositive field‖ ^ 2 +
    ‖crossHighFlux lower length positive lengthPositive field‖ ^ 2 at square
  nlinarith [norm_nonneg (crossHighW lower length positive lengthPositive field), norm_nonneg field,
    sq_nonneg ‖crossHighFlux lower length positive lengthPositive field‖]

def crossHighX (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    CrossHighSpace lower length positive lengthPositive →L[ℂ] AnnularBulk lower :=
  annularOmegaValue lower ∘L (annularOmegaGraph lower length positive lengthPositive).subtypeL ∘L
    crossHighFlux lower length positive lengthPositive

theorem crossHighX_bound (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CrossHighSpace lower length positive lengthPositive) : ‖crossHighX lower length positive lengthPositive field‖ ≤ ‖field‖ := by
  have square := WithLp.prod_norm_sq_eq_of_L2 field
  change ‖field‖ ^ 2 = ‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2‖ ^ 2 at square
  have omega := annularOmegaGraph_norm_sq lower length positive lengthPositive field.ofLp.2
  change ‖field.ofLp.2‖ ^ 2 = ‖crossHighX lower length positive lengthPositive field‖ ^ 2 + ‖field.ofLp.2.val 1‖ ^ 2 at omega
  nlinarith [norm_nonneg (crossHighX lower length positive lengthPositive field), norm_nonneg field,
    sq_nonneg ‖field.ofLp.1‖, sq_nonneg ‖field.ofLp.2.val 1‖]

/-- The free high x coordinate enters slot zero. The remaining homogeneous
physical slots depend on W; no first-row elimination or independent y' is used. -/
def highCrossSevenInput (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    CrossHighSpace lower length positive lengthPositive →L[ℂ] DivisionRow 7 lower :=
  highBulkSlot lower 0 ∘L crossHighX lower length positive lengthPositive +
  highBulkSlot lower 1 ∘L highEnergyAngularRadius lower length positive ∘L bEnergyDecode lower length positive ∘L crossHighW lower length positive lengthPositive +
  highBulkSlot lower 2 ∘L ((length : ℂ) • highEnergyCell lower length positive) ∘L bEnergyDecode lower length positive ∘L crossHighW lower length positive lengthPositive +
  highBulkSlot lower 3 ∘L highEnergyRadius lower length positive ∘L bEnergyDecode lower length positive ∘L crossHighW lower length positive lengthPositive

theorem highCrossSevenInput_bound (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CrossHighSpace lower length positive lengthPositive) :
    ‖highCrossSevenInput lower length positive lengthPositive field‖ ≤ (4 + 2 * |length|) * ‖field‖ := by
  let decoded := bEnergyDecode lower length positive (crossHighW lower length positive lengthPositive field)
  have decodedBound : ‖decoded‖ ≤ ‖field‖ := (physicalEnergyDecode_bound lower length positive _).trans
    (crossHighW_bound lower length positive lengthPositive field)
  have first := (highBulkSlot_bound lower (0 : Fin 7) _).trans (crossHighX_bound lower length positive lengthPositive field)
  have second := (highBulkSlot_bound lower (1 : Fin 7) _).trans
    ((highEnergyAngularRadius_bound lower length positive decoded).trans decodedBound)
  have third := highBulkSlot_bound lower (2 : Fin 7) ((length : ℂ) • highEnergyCell lower length positive decoded)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs] at third
  have cell := (highEnergyCell_bound lower length positive decoded).trans (mul_le_mul_of_nonneg_left decodedBound (by norm_num : (0 : ℝ) ≤ 2))
  have thirdBound := third.trans (mul_le_mul_of_nonneg_left cell (abs_nonneg length))
  have fourth := (highBulkSlot_bound lower (3 : Fin 7) _).trans
    ((highEnergyRadius_bound lower length positive decoded).trans (mul_le_mul_of_nonneg_left decodedBound (by norm_num : (0 : ℝ) ≤ 1 / 3)))
  change ‖highBulkSlot lower (0 : Fin 7) (crossHighX lower length positive lengthPositive field) +
    highBulkSlot lower (1 : Fin 7) (highEnergyAngularRadius lower length positive decoded) +
    highBulkSlot lower (2 : Fin 7) ((length : ℂ) • highEnergyCell lower length positive decoded) +
    highBulkSlot lower (3 : Fin 7) (highEnergyRadius lower length positive decoded)‖ ≤ _
  apply (norm_add_le _ _).trans
  apply (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl).trans
  linarith [norm_nonneg field]

end Grad.AnnularCrossMaps
