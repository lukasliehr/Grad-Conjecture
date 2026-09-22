import AKBI3ActualCoreCartesianDifferentiation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter
open scoped ContDiff Topology
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.QuotientProjection Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery Grad.SourceCollar Grad.NonlinearProduct

/-- Cartesian Leibniz on the original all-grade core, obtained directly from
its immutable FP17 Fourier reconstruction and the actual product values. -/
theorem originalDot_partial {parameters : PhaseParameters} (direction : Fin 2) (first second : ACore parameters 3) :
    partialCore parameters direction (dotOperation parameters first second)=
      dotOperation parameters (partialCore parameters direction first) second+
        dotOperation parameters first (partialCore parameters direction second) := by
  apply originalCore_ext_interior
  intro point inside angle
  let position : SpatialCell := WithLp.toLp 2 ![point.val 0,point.val 1,angle]
  have planar : planarPart position=point.val := by
    apply PiLp.ext
    intro index
    fin_cases index <;> rfl
  have interior : position∈openUnitCylinder := by
    change ‖planarPart position‖<1
    rw [planar]
    exact inside
  have samePoint : (diskCellPoint position (openCylinderMembershipClosed position interior)).1=point :=
    Subtype.ext planar
  let product := physicalBilinear physicalDotProduct
  let realProduct := (ContinuousLinearMap.restrictScalarsL ℂ (ComplexEuclidean 3) (ComplexEuclidean 1) ℝ ℝ).comp (product.restrictScalars ℝ)
  have mapped := (realProduct.hasFDerivAt).comp position (originalCoreCartesianLift_hasFDerivAt parameters first position interior)
  have derivative := mapped.clm_apply (originalCoreCartesianLift_hasFDerivAt parameters second position interior)
  have same : originalCoreCartesianLift parameters (dotOperation parameters first second)=ᶠ[𝓝 position]
      (fun query => product (originalCoreCartesianLift parameters first query) (originalCoreCartesianLift parameters second query)) := by
    filter_upwards [openUnitCylinder_isOpen.mem_nhds interior] with query included
    rw [originalCoreCartesianLift_value parameters _ query included,originalCoreCartesianLift_value parameters _ query included,
      originalCoreCartesianLift_value parameters _ query included]
    exact (coreValue_pairProduct physicalDotProduct first second _ _).trans (physicalBilinear_apply _ _ _).symm
  have original := originalCoreCartesianLift_hasFDerivAt parameters (dotOperation parameters first second) position interior
  have equality := original.unique (derivative.congr_of_eventuallyEq same)
  have value := congrArg (fun differential : SpatialCell →L[ℝ] ComplexEuclidean 1 =>
    differential (spatialCellBasis (fp17PlanarCoordinate direction))) equality
  change fderiv ℝ (originalCoreCartesianLift parameters (dotOperation parameters first second)) position
      (spatialCellBasis (fp17PlanarCoordinate direction))=
    product (originalCoreCartesianLift parameters first position)
      (fderiv ℝ (originalCoreCartesianLift parameters second) position (spatialCellBasis (fp17PlanarCoordinate direction)))+
    product (fderiv ℝ (originalCoreCartesianLift parameters first) position (spatialCellBasis (fp17PlanarCoordinate direction)))
      (originalCoreCartesianLift parameters second position) at value
  rw [originalCoreCartesianLift_partial parameters _ position interior direction,
    originalCoreCartesianLift_partial parameters _ position interior direction,
    originalCoreCartesianLift_partial parameters _ position interior direction,
    originalCoreCartesianLift_value parameters _ position interior,originalCoreCartesianLift_value parameters _ position interior,
    samePoint] at value
  rw [coreValue_add]
  change _=coreValue (pairProductLinear parameters physicalDotProduct (partialCore parameters direction first) second) point angle+
    coreValue (pairProductLinear parameters physicalDotProduct first (partialCore parameters direction second)) point angle
  rw [coreValue_pairProduct,coreValue_pairProduct]
  simpa only [product,physicalBilinear_apply,position,WithLp.toLp_ofLp,Matrix.cons_val,Matrix.vecHead,Matrix.vecTail,add_comm] using value

theorem originalDot_euler {parameters : PhaseParameters} (first second : ACore parameters 3) :
    eulerCore parameters (dotOperation parameters first second)=
      dotOperation parameters (eulerCore parameters first) second+dotOperation parameters first (eulerCore parameters second) := by
  simp only [eulerCore,LinearMap.add_apply,LinearMap.comp_apply,originalDot_partial,map_add,LinearMap.add_apply,
    dot_coordinate_first,dot_coordinate_second]
  abel

end Grad.OriginalKernelHomogeneousGraph
