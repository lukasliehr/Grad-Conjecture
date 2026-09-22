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

 def scaledNativeFamilyRaw (ell : ℝ) (pair : ℝ×Spatial) : PhysicalValue dimension :=
  gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (ell • pair.2,pair.1)

include compatible in
 theorem scaledNativeFamilyRaw_polar (ell radius : ℝ) (physicalPositive : 0 < ell*radius)
    (radiusNonnegative : 0 ≤ radius) (radiusBounded : |radius| ≤ 1)
    (index : ℕ) (inside : ell*radius ∈ Icc (lower index) 1) (polar axial : ℝ) :
    scaledNativeFamilyRaw parameters lower positive bounded cofinal rows curves ell
      (axial,(Grad.Constraints.polarClosedPoint radius radiusBounded polar).val) =
      (curves index).fullField (bounded index) (ell*radius,polar,axial) := by
  have point : (Grad.Constraints.polarClosedPoint radius radiusBounded polar).val = polarPlane (radius,polar) := by
    rw [← divisionPolarPoint_eq_original radius polar radiusNonnegative ((le_abs_self radius).trans radiusBounded)]
    rfl
  unfold scaledNativeFamilyRaw gluedCartesianFamilyField
  rw [point,startupPolar_dilation,cartesianPhysicalField_at_polar _
    (gluedPhysicalFamilyField_periodic parameters lower positive bounded cofinal rows curves) _ physicalPositive]
  exact gluedPhysicalFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible index _ inside _

include compatible in
 theorem scaledNativeFamilyRaw_regular (ell : ℝ) (ellPositive : 0 < ell) (ellBounded : ell ≤ 1) :
    StartupOrbitContinuous (scaledNativeFamilyRaw parameters lower positive bounded cofinal rows curves ell) := by
  apply startupOrbitContinuous_of_punctured
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
