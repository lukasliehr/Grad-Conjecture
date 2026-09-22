import AKBM1SameSmoothAngularAxialCurves
import AKBD26SameCartesianSignedCofactorFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter
open scoped Topology
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.NonlinearRange
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualCartesianDescent Grad.ActualCartesianEquations
open Grad.ActualDeterminantEquations Grad.DiskExtension.Operator Grad.Constraints Grad.SourceCollar
open Grad.PhysicalFamily Grad.BoundaryTrace

theorem originalPolarPlane_norm_argument (point : SpatialPlane) :
    polarPlane (‖point‖,Complex.arg (signedComplexCoordinate 1 point))=point := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · simp only [polarPlane,collarPlane,sub_sub_cancel]
    change ‖point‖*Real.cos (Complex.arg (signedComplexCoordinate 1 point))=point 0
    rw [← signedComplexCoordinate_one_norm,Complex.norm_mul_cos_arg]
    simp [signedComplexCoordinate]
  · simp only [polarPlane,collarPlane,sub_sub_cancel]
    change ‖point‖*Real.sin (Complex.arg (signedComplexCoordinate 1 point))=point 1
    rw [← signedComplexCoordinate_one_norm,Complex.norm_mul_sin_arg]
    simp [signedComplexCoordinate]

theorem originalAssembledCore_value {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
    (point : SpatialPlane×ℝ) (inside : ‖point.1‖<1) :
    originalCoreCartesianLift parameters field (assembleSpatialCellCLM point)=
      coreValue field ⟨point.1,inside.le⟩ point.2 := by
  have included : assembleSpatialCellCLM point∈openUnitCylinder := by
    change ‖planarPart (assembleSpatialCell point.1 point.2)‖<1
    simpa only [planarPart_assembleSpatialCell] using inside
  rw [originalCoreCartesianLift_value parameters field _ included]
  congr 2
  apply Subtype.ext
  exact planarPart_assembleSpatialCell _ _

theorem originalAssembledBasis :
    assembleSpatialCellCLM (spatialBasis 0,(0:ℝ))=spatialCellBasis 0 ∧
    assembleSpatialCellCLM (spatialBasis 1,(0:ℝ))=spatialCellBasis 1 ∧
    assembleSpatialCellCLM (0,(1:ℝ))=spatialCellBasis 2 := by
  constructor
  · apply PiLp.ext; intro coordinate; fin_cases coordinate <;> simp [assembleSpatialCellCLM_apply,assembleSpatialCell,spatialBasis,spatialCellBasis]
  constructor
  · apply PiLp.ext; intro coordinate; fin_cases coordinate <;> simp [assembleSpatialCellCLM_apply,assembleSpatialCell,spatialBasis,spatialCellBasis]
  · apply PiLp.ext; intro coordinate; fin_cases coordinate <;> simp [assembleSpatialCellCLM_apply,assembleSpatialCell,spatialCellBasis]

variable {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower} {row : DivisionRow 3 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1) (field : ACore parameters 3)
    (same : ∀ radius : Icc lower (1:ℝ),∀ angles,
      curves.fullField bounded (radius.val,angles)=
        coreValue field (polarClosedPoint radius.val angles.1 (positive.le.trans radius.property.1) radius.property.2) angles.2)

include same

theorem originalSmoothCurve_cartesianSame (point : SpatialPlane×ℝ) (inside : ‖point.1‖∈Ioo lower 1) :
    curves.cartesianField bounded point=(fun query => originalCoreCartesianLift parameters field (assembleSpatialCellCLM query)) point := by
  let radius : Icc lower (1:ℝ) := ⟨‖point.1‖,⟨inside.1.le,inside.2.le⟩⟩
  let angle := Complex.arg (signedComplexCoordinate 1 point.1)
  have polar := originalPolarPlane_norm_argument point.1
  have actual := same radius (angle,point.2)
  dsimp only
  rw [originalAssembledCore_value parameters field point inside.2]
  calc
    curves.cartesianField bounded point = curves.fullField bounded (radius.val,angle,point.2) := by
      have pointSame : point=(polarPlane (radius.val,angle),point.2) := Prod.ext polar.symm rfl
      conv_lhs => rw [pointSame]
      exact cartesianPhysicalField_at_polar (curves.fullField bounded)
        (fun radius axial => curves.fullField_angular_periodic bounded radius axial)
        radius.val (positive.trans inside.1) angle point.2
    _ = _ := by
      rw [actual]
      have disk : polarClosedPoint radius.val angle (positive.le.trans radius.property.1) radius.property.2=⟨point.1,inside.2.le⟩ :=
        Subtype.ext polar
      rw [disk]

/-- Actual Cartesian divergence of any SAME original smooth core curve,
with the exact original L,L,1 scaling. -/
theorem originalSmoothCurve_cartesianDivergence (length : ℝ) (point : SpatialPlane×ℝ)
    (inside : ‖point.1‖∈Ioo lower 1) :
    cartesianDeterminantDivergence length (curves.cartesianField bounded) point=
      coreValue (originalCartesianDivergenceCore length field) ⟨point.1,inside.2.le⟩ point.2 0 := by
  have included : assembleSpatialCellCLM point∈openUnitCylinder := by
    change ‖planarPart (assembleSpatialCell point.1 point.2)‖<1
    simpa only [planarPart_assembleSpatialCell] using inside.2
  have equality : curves.cartesianField bounded=ᶠ[𝓝 point]
      (fun query => originalCoreCartesianLift parameters field (assembleSpatialCellCLM query)) := by
    filter_upwards [(isOpen_Ioo.preimage (continuous_norm.comp continuous_fst)).mem_nhds inside] with query member
    exact originalSmoothCurve_cartesianSame curves bounded field same query member
  have derivative := ((originalCoreCartesianLift_hasFDerivAt parameters field _ included).comp point
    assembleSpatialCellCLM.hasFDerivAt).congr_of_eventuallyEq equality
  rw [cartesianDeterminantDivergence,derivative.fderiv]
  simp only [ContinuousLinearMap.comp_apply,originalAssembledBasis.1,originalAssembledBasis.2.1,originalAssembledBasis.2.2]
  rw [← originalCartesianDivergence_value parameters length field _ included]
  change coreValue (originalCartesianDivergenceCore length field)
    (diskCellPoint (assembleSpatialCell point.1 point.2) (openCylinderMembershipClosed _ included)).1 point.2 0=_
  have disk : (diskCellPoint (assembleSpatialCell point.1 point.2) (openCylinderMembershipClosed _ included)).1=
      (⟨point.1,inside.2.le⟩ : ClosedDisk) := Subtype.ext (planarPart_assembleSpatialCell _ _)
  rw [disk]

end Grad.OriginalKernelHomogeneousGraph
