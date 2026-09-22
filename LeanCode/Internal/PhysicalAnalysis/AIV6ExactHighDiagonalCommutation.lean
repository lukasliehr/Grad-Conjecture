import AIV5ActualHighPairEquivalence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalHigh
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularHighTilt Grad.AnnularGrades Grad.AnnularCrossMaps

section Diagonal
variable (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
  (lengthPositive : 0 < length) (coefficient : HighAnnularMode → ℝ)
  (constant : ℝ) (nonnegative : 0 ≤ constant) (coefficientBound : ∀ mode, |coefficient mode| ≤ constant)

def originalNuDiagonal : originalNuGraph lower positive →L[ℂ] originalNuGraph lower positive :=
  (originalNuPairEquivalence lower positive).symm.toContinuousLinearMap.comp
    ((annularFluxGraphDiagonal lower positive coefficient constant nonnegative coefficientBound).comp
      (originalNuPairEquivalence lower positive).toContinuousLinearMap)

theorem originalNuDiagonal_value (field : originalNuGraph lower positive) :
    (originalNuDiagonal lower positive coefficient constant nonnegative coefficientBound field).val 0 =
      realLpDiagonal coefficient constant nonnegative coefficientBound (field.val 0) := rfl

theorem highEnergyWeight_diagonal (field : annularEnergySpace lower length positive) :
    highEnergyWeight lower length positive bounded
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative coefficientBound field) =
    annularEnergyDiagonal lower length positive coefficient constant nonnegative coefficientBound
      (highEnergyWeight lower length positive bounded field) := by
  apply Subtype.ext
  apply lp.ext
  funext mode
  change highModeEnergyWeight lower length positive bounded mode ((coefficient mode : ℂ) • field.val mode) =
    (coefficient mode : ℂ) • highModeEnergyWeight lower length positive bounded mode (field.val mode)
  exact map_smul _ _ _

theorem highEnergyUnweight_diagonal (field : annularEnergySpace lower length positive) :
    highEnergyUnweight lower length positive bounded
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative coefficientBound field) =
    annularEnergyDiagonal lower length positive coefficient constant nonnegative coefficientBound
      (highEnergyUnweight lower length positive bounded field) := by
  apply Subtype.ext
  apply lp.ext
  funext mode
  change highModeEnergyUnweight lower length positive bounded mode ((coefficient mode : ℂ) • field.val mode) =
    (coefficient mode : ℂ) • highModeEnergyUnweight lower length positive bounded mode (field.val mode)
  exact map_smul _ _ _

theorem originalFluxTilt_diagonal (strict : lower < 1) (field : originalNuGraph lower positive) :
    originalFluxTiltEquivalence lower length positive bounded lengthPositive
      (originalNuDiagonal lower positive coefficient constant nonnegative coefficientBound field) =
    annularOmegaGraphDiagonal lower length positive lengthPositive coefficient constant nonnegative coefficientBound
      (originalFluxTiltEquivalence lower length positive bounded lengthPositive field) := by
  apply annularOmegaGraph_value_injective lower length positive strict lengthPositive
  dsimp only
  rw [originalFluxTilt_value, originalNuDiagonal_value, annularOmegaGraphDiagonal_value,
    originalFluxTilt_value]
  unfold highBulkWeight annularScalarFamily
  exact (realLpDiagonal_commutes coefficient constant nonnegative coefficientBound _ _ _ _ _).symm

end Diagonal

/-- The scalar b decode commutes with the exact radial tilt; no normalization changes. -/
theorem originalHighTilt_bDecode (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : annularEnergySpace lower length positive) :
    Grad.AnnularTiltedReference.bEnergyDecode lower length positive
      (highEnergyWeight lower length positive bounded field) =
    highEnergyWeight lower length positive bounded
      (Grad.AnnularTiltedReference.bEnergyDecode lower length positive field) :=
  (highEnergyWeight_diagonal lower length positive bounded _ _ _ _ field).symm

end Grad.AnnularOriginalHigh
