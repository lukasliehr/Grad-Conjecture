import AKBT3NativeGaugeCellContinuity
import AKBQ7OriginalPacketScaledGaugeMeans
import AKBK1SameGlobalCellDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped Topology
namespace Grad.ActualScaledNativeCoefficients
open Grad.GenericCarriers Grad.PDEBootstrap
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.ActualSmoothPhysicalField Grad.ActualCartesianDescent Grad.ActualCartesianWeakEquations
open Grad.AnnularRestriction Grad.CartesianStartup Grad.PDEBootstrap

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)


include compatible in
 theorem scaledNativeFamilyRaw_punctured_continuous (ell : ℝ) (ellPositive : 0 < ell) (ellBounded : ell ≤ 1) :
    ContinuousOn (scaledNativeFamilyRaw parameters lower positive bounded cofinal rows curves ell) {pair | pair.2 ∈ openUnitDisk \ {(0 : Spatial)}} := by
  intro point inside
  have pointNonzero : point.2 ≠ 0 := by simpa only [mem_singleton_iff] using inside.2
  have scaledNonzero : ell • point.2 ≠ 0 := smul_ne_zero ellPositive.ne' pointNonzero
  have scaledInside : ‖ell • point.2‖ < 1 := by
    rw [norm_smul,Real.norm_of_nonneg ellPositive.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) ellBounded).trans_lt inside.1
  have smooth := gluedCartesianFamilyField_smoothAt parameters lower positive bounded cofinal decreasing rows curves compatible
    (ell • point.2,point.1) scaledNonzero scaledInside
  exact (smooth.continuousAt.comp (x := point) (f := fun pair : ℝ×Spatial => (ell • pair.2,pair.1)) (by fun_prop)).continuousWithinAt

end Grad.ActualScaledNativeCoefficients
