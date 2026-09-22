import AKBI13ActualHomogeneousFirstSourceGraph
import AKU55LiteralDeterminantFourierValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter
open scoped BigOperators Topology
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.SourceCollar Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelCovariantRecovery

theorem originalDeterminant_value {parameters : PhaseParameters} (first second third : ACore parameters 3)
    (point : ClosedDisk) (angle : ℝ) :
    coreValue (determinantOperation parameters first second third) point angle=
      determinantMultilinear ![coreValue first point angle,coreValue second point angle,coreValue third point angle] := by
  apply PiLp.ext
  intro coordinate
  have only : coordinate=0 := Subsingleton.elim _ _
  subst coordinate
  exact (coreValue_determinantOperation first second third point angle).trans (determinantMultilinear_value _ _ _).symm

theorem originalDeterminant_partial {parameters : PhaseParameters} (direction : Fin 2) (first second third : ACore parameters 3) :
    partialCore parameters direction (determinantOperation parameters first second third)=
      determinantOperation parameters (partialCore parameters direction first) second third+
      determinantOperation parameters first (partialCore parameters direction second) third+
      determinantOperation parameters first second (partialCore parameters direction third) := by
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
  have samePoint : (diskCellPoint position (openCylinderMembershipClosed position interior)).1=point := Subtype.ext planar
  let fields : Fin 3 → ACore parameters 3 := ![first,second,third]
  let product := determinantMultilinear.restrictScalars ℝ
  have tuple := hasFDerivAt_pi.mpr (fun slot : Fin 3 => originalCoreCartesianLift_hasFDerivAt parameters (fields slot) position interior)
  have derivative := (product.hasFDerivAt _).comp position tuple
  have same : originalCoreCartesianLift parameters (determinantOperation parameters first second third)=ᶠ[𝓝 position]
      (fun query => product (fun slot => originalCoreCartesianLift parameters (fields slot) query)) := by
    filter_upwards [openUnitCylinder_isOpen.mem_nhds interior] with query included
    rw [originalCoreCartesianLift_value parameters _ query included,originalDeterminant_value]
    have components : (fun slot => originalCoreCartesianLift parameters (fields slot) query)=
        ![coreValue first (diskCellPoint query (openCylinderMembershipClosed query included)).1 (query 2),
          coreValue second (diskCellPoint query (openCylinderMembershipClosed query included)).1 (query 2),
          coreValue third (diskCellPoint query (openCylinderMembershipClosed query included)).1 (query 2)] := by
      funext slot
      fin_cases slot <;> exact originalCoreCartesianLift_value parameters _ query included
    rw [components]
    rfl
  have original := originalCoreCartesianLift_hasFDerivAt parameters (determinantOperation parameters first second third) position interior
  have equality := original.unique (derivative.congr_of_eventuallyEq same)
  have value := congrArg (fun differential : SpatialCell →L[ℝ] ComplexEuclidean 1 =>
    differential (spatialCellBasis (fp17PlanarCoordinate direction))) equality
  simp only [ContinuousLinearMap.comp_apply,ContinuousMultilinearMap.linearDeriv_apply,
    ContinuousLinearMap.pi_apply,Fin.sum_univ_three] at value
  rw [originalCoreCartesianLift_partial parameters _ position interior direction] at value
  simp only [fields,Matrix.cons_val] at value
  simp only [originalCoreCartesianLift_partial parameters _ position interior direction,
    originalCoreCartesianLift_value parameters _ position interior,samePoint] at value
  rw [coreValue_add,coreValue_add,originalDeterminant_value,originalDeterminant_value,originalDeterminant_value]
  convert value using 1 <;> rfl

end Grad.OriginalKernelHomogeneousGraph
