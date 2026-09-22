import AKAE11SameGlobalCartesianDerivatives
import AKAD6JointPhysicalPairIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianIntegrability
open Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryLift
open Grad.ActualSmoothPhysicalField Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.AnnularCurrentLow
open Grad.AnnularClosedJointRegularity Grad.SourceCollarFullSource Grad.BoundaryTrace

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)

open Grad.ActualCartesianDescent Grad.DiskExtension.Operator Grad.PhysicalAxisEquation
include compatible

theorem samePhysicalCurve_continuous (grade : ℕ) :
    ContinuousOn (gluedPhysicalFamilyCurve parameters lower positive bounded cofinal rows curves grade) (Ioc (0 : ℝ) 1) :=
  gluedClosedSections_continuous lower cofinal
    (physicalFamilySections parameters lower positive bounded rows curves grade) positive
    (fun first second radius one two => physicalFamilyCurve_agree parameters lower positive bounded decreasing rows curves compatible
      first second grade radius one two) (fun index => (bounded index).le)

theorem samePhysicalCurve_original_ae (index : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc (lower index) 1), ∀ mode,
      gluedPhysicalFamilyCurve parameters lower positive bounded cofinal rows curves 0 radius mode =
        lowRhoPhysicalCoefficient parameters (lower index) (positive index) (rows index) radius mode := by
  filter_upwards [(curves index).physicalCurve_actual (bounded index) 0,ae_restrict_mem measurableSet_Icc] with radius same inside
  intro mode
  rw [gluedPhysicalFamilyCurve_same parameters lower positive bounded cofinal decreasing rows curves compatible 0 index radius inside]
  simpa only [pow_zero,one_smul] using same mode

theorem sameCartesianCell_continuousOn (cell : ℤ) :
    ContinuousOn (gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell) (openUnitDisk \ {(0 : SpatialPlane)}) := by
  intro point inside
  exact (gluedCartesianCellField_smoothAt parameters lower positive bounded cofinal decreasing rows curves compatible cell point inside.2 inside.1).continuousAt.continuousWithinAt

theorem sameCartesianCell_aestronglyMeasurable (cell : ℤ) :
    AEStronglyMeasurable (gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell) (volume.restrict openUnitDisk) := by
  have result := (sameCartesianCell_continuousOn parameters lower positive bounded cofinal decreasing rows curves compatible cell).aestronglyMeasurable (μ := volume)
    (openUnitDisk_isOpen.measurableSet.diff (measurableSet_singleton 0))
  simpa only [puncturedDisk_restrict_measure] using result

theorem sameCartesianCell_polar_continuousOn (cell : ℤ) :
    ContinuousOn (fun point : ℝ × ℝ => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell
      (spatialPlaneOfPair (polarCoord.symm point))) ((Ioo (0 : ℝ) 1) ×ˢ (univ : Set ℝ)) := by
  have parametrization : (fun point : ℝ × ℝ => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell
      (spatialPlaneOfPair (polarCoord.symm point))) =
      fun point => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (polarPlane point) := by
    funext point
    exact congrArg (gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell)
      (polarPlane_originalParametrization point.1 point.2)
  rw [parametrization]
  intro point inside
  have pointNorm : ‖polarPlane point‖ = point.1 :=
    (polarPlane_norm point.1 point.2).trans (abs_of_pos inside.1.1)
  have nonzero : polarPlane point ≠ 0 := norm_ne_zero_iff.mp (pointNorm.trans_ne inside.1.1.ne')
  have upper : ‖polarPlane point‖ < 1 := pointNorm.trans_lt inside.1.2
  exact ((gluedCartesianCellField_smoothAt parameters lower positive bounded cofinal decreasing rows curves compatible cell (polarPlane point) nonzero upper).continuousAt.comp
    polarPlane_smooth.continuous.continuousAt).continuousWithinAt

theorem sameCartesianCell_polar_aestronglyMeasurable (cell : ℤ) :
    AEStronglyMeasurable (fun point : ℝ × ℝ => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell
      (spatialPlaneOfPair (polarCoord.symm point)))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (-Real.pi) Real.pi))) := by
  have continuous := (sameCartesianCell_polar_continuousOn parameters lower positive bounded cofinal decreasing rows curves compatible cell).mono
    (Set.prod_mono (Subset.refl _) (subset_univ _ : Ioc (-Real.pi) Real.pi ⊆ univ))
  have result := continuous.aestronglyMeasurable (μ := volume) (measurableSet_Ioo.prod measurableSet_Ioc)
  have radialMeasure : volume.restrict (Ioc (0 : ℝ) 1) = volume.restrict (Ioo (0 : ℝ) 1) :=
    (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
  rw [radialMeasure,Measure.prod_restrict,← Measure.volume_eq_prod]
  exact result

end Grad.ActualCartesianIntegrability
