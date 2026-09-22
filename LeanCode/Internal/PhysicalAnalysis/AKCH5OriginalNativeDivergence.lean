import AKCH4SameOriginalCofactorCore
import AKBM9ActualProjectedPolarDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped Topology
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.ActualSmoothPhysicalField Grad.AnnularReconstruction
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay Grad.NonlinearRange
open Grad.ActualCurrentPrimitives Grad.ActualCartesianDescent Grad.SourceCollar
open Grad.OriginalKernelHomogeneousGraph Grad.ActualDeterminantEquations Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.ActualCartesianEquations
open Grad.PhysicalFamily Grad.BoundaryTrace Grad.DiskExtension.Operator
open Grad.AnnularOriginalSmoothCore Grad.SourceCollarFullSource Grad.BoundaryKernelAction

/-- The original L,L,1 core divergence in the SAME product coordinates. -/
theorem originalCoreProductLift_divergence (parameters : PhaseParameters) (length : ℝ)
    (core : ACore parameters 3) (point : SpatialPlane×ℝ) (inside : ‖point.1‖<1) :
    coreValue (originalCartesianDivergenceCore length core) ⟨point.1,inside.le⟩ point.2 0=
      cartesianDeterminantDivergence length (originalCoreProductLift parameters core) point := by
  have cylinder : assembleSpatialCell point.1 point.2∈openUnitCylinder := by
    change ‖planarPart (assembleSpatialCell point.1 point.2)‖<1
    simpa only [planarPart_assembleSpatialCell] using inside
  have literal := originalCartesianDivergence_value parameters length core _ cylinder
  rw [cartesianDeterminantDivergence,originalCoreProductLift_fderiv parameters core point inside]
  simp only [ContinuousLinearMap.comp_apply,assembleSpatialCellCLM_apply,
    originalProduct_planarBasis,originalProduct_axialBasis] 
  have closed : (diskCellPoint (assembleSpatialCell point.1 point.2) (openCylinderMembershipClosed _ cylinder)).1=⟨point.1,inside.le⟩ := by
    apply Subtype.ext
    exact planarPart_assembleSpatialCell point.1 point.2
  rw [closed] at literal
  have axial : assembleSpatialCell point.1 point.2 2=point.2 := by simp [assembleSpatialCell]
  rw [axial] at literal
  exact literal

/-- Equality of SAME core/native collar values transfers the genuine full
Frechet divergence, without a derivative premise. -/
theorem originalNative_divergence_same (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) {row : DivisionRow 3 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (core : ACore parameters 3)
    (same : ∀ (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ),
      coreValue core (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) angles.2=
        curves.fullField bounded (radius,angles))
    (point : SpatialPlane×ℝ) (inside : ‖point.1‖∈Ioo lower 1) :
    coreValue (originalCartesianDivergenceCore length core) ⟨point.1,inside.2.le⟩ point.2 0=
      cartesianDeterminantDivergence length (curves.cartesianField bounded) point := by
  rw [originalCoreProductLift_divergence parameters length core point inside.2,cartesianDeterminantDivergence,
    originalCore_same_nativeDerivative parameters lower positive bounded curves core same point inside]
  rfl

/-- Original scalar angular projection, retaining the actual polar coordinate. -/
theorem originalCore_removeAngular_polar (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) (core : ACore parameters 1)
    (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ) :
    coreValue (removeAngularCore parameters core)
      (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) angles.2 0=
    removePolarMean (fun query => coreValue core
      (Grad.SourceCollarDivision.polarClosedPoint radius query.1 (positive.le.trans inside.1) inside.2) query.2 0) angles := by
  let r : Icc lower (1:ℝ) := ⟨radius,inside⟩
  have projected := originalCoreCircle_meanFree parameters lower positive bounded core r angles
  have coordinate := congrArg (fun value : ComplexEuclidean 1 => value 0) projected
  change (removePolarMean (originalCoreCircle parameters core (tupleRadius lower positive r)) angles) 0=_ at coordinate
  rw [removePolarMean_coordinate _ (originalCoreCircle_continuous parameters core (tupleRadius lower positive r)) angles] at coordinate
  exact coordinate.symm

end Grad.OriginalCoreRealization
