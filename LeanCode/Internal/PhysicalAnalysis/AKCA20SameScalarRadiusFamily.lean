import AKCA19SameScalarRadiusCurves
import AKBL26SameWeightedOperatorFields
import AKBK1SameGlobalCellDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualPhysicalField Grad.AnnularCurrentSource Grad.AnnularCurrentLow
open Grad.ActualCartesianDescent Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.ActualCartesianWeakEquations
open Grad.CartesianCoreRecovery Grad.SourceCollarFullSource Grad.BoundaryTrace

variable (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow 1 (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 1 (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
include compatible

 theorem scalarRadiusFamily_compatible (first second : ℕ) (ordered : first≤second) :
    originalBulkRestriction 1 (lower second) (lower first) (decreasing ordered)
      (radialRadiusRow (lower second) (positive second) (rows second))=
      radialRadiusRow (lower first) (positive first) (rows first) := by
  rw [originalBulkRestriction_radius,compatible first second ordered]

 theorem scalarRadiusFamily_fullField (point : SpatialPlane×ℝ) (inside : ‖point.1‖∈Ioc (0:ℝ) 1) :
    gluedCartesianFamilyField parameters lower positive bounded cofinal
      (fun index => radialRadiusRow (lower index) (positive index) (rows index))
      (fun index => scalarRadiusCurves (curves index)) point=
      ‖point.1‖ • gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves point := by
  let index := selectedInnerCollar lower cofinal ‖point.1‖ inside.1
  have collar : ‖point.1‖∈Icc (lower index) 1 :=
    ⟨(selectedInnerCollar_lt lower cofinal ‖point.1‖ inside.1).le,inside.2⟩
  rw [gluedCartesianFamilyField_same parameters lower positive bounded cofinal decreasing _ _
    (scalarRadiusFamily_compatible lower positive decreasing rows compatible) index point collar,
    gluedCartesianFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible index point collar]
  exact scalarRadiusCurves_cartesianField (curves index) (bounded index) point collar

 theorem scalarRadiusFamily_cell (point : SpatialPlane) (nonzero : point≠0) (inside : ‖point‖<1) (cell : ℤ) :
    gluedCartesianCellField parameters lower positive bounded cofinal
      (fun index => radialRadiusRow (lower index) (positive index) (rows index))
      (fun index => scalarRadiusCurves (curves index)) cell point=
      ‖point‖ • gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point := by
  rw [nativeFamilyCell_actual parameters lower positive bounded cofinal decreasing _ _
      (scalarRadiusFamily_compatible lower positive decreasing rows compatible) cell point nonzero inside,
    nativeFamilyCell_actual parameters lower positive bounded cofinal decreasing rows curves compatible cell point nonzero inside]
  simp_rw [scalarRadiusFamily_fullField parameters lower positive bounded cofinal decreasing rows curves compatible
    (_,_) ⟨norm_pos_iff.mpr nonzero,inside.le⟩]
  have continuousField : Continuous (fun axial => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point,axial)) := by
    let index := selectedInnerCollar lower cofinal ‖point‖ (norm_pos_iff.mpr nonzero)
    have collar : ‖point‖∈Icc (lower index) 1 :=
      ⟨(selectedInnerCollar_lt lower cofinal ‖point‖ (norm_pos_iff.mpr nonzero)).le,inside.le⟩
    have same : (fun axial => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point,axial))=
        fun axial => (curves index).cartesianField (bounded index) (point,axial) :=
      funext (fun axial => gluedCartesianFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible index (point,axial) collar)
    rw [same]
    simp only [SmoothLowPhysicalRow.cartesianField,cartesianPhysicalField,cartesianFromPolar,Grad.BoundaryLift.complexCoordinate_norm]
    exact ((curves index).fullField_continuous_angles (bounded index) ‖point‖ collar).comp
      (continuous_const.prodMk continuous_id)
  simpa only [smul_apply,ContinuousLinearMap.id_apply,Complex.coe_smul] using
    angularCoefficient_valueMap ((‖point‖ : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 1)) _ continuousField cell

end Grad.OriginalCoreRealization
