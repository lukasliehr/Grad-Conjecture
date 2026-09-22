import AKCH1SameCoreCartesianDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped Topology
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.OriginalKernelHomogeneousGraph Grad.SourceCollar Grad.DiskExtension.Operator Grad.NonlinearRange

 theorem originalProduct_planarBasis (direction : Fin 2) :
    assembleSpatialCell (spatialBasis direction) 0=spatialCellBasis (fp17PlanarCoordinate direction) := by
  ext coordinate
  fin_cases direction <;> fin_cases coordinate <;>
    simp [assembleSpatialCell,spatialBasis,spatialCellBasis,fp17PlanarCoordinate]

 theorem originalProduct_axialBasis : assembleSpatialCell (0:SpatialPlane) 1=spatialCellBasis 2 := by
  ext coordinate
  fin_cases coordinate <;> simp [assembleSpatialCell,spatialCellBasis]

 theorem originalCoreProductLift_partial {dimension : ℕ} (parameters : PhaseParameters) (core : ACore parameters dimension)
    (point : SpatialPlane × ℝ) (inside : ‖point.1‖<1) (direction : Fin 2) :
    fderiv ℝ (originalCoreProductLift parameters core) point (spatialBasis direction,0)=
      coreValue (partialCore parameters direction core) ⟨point.1,inside.le⟩ point.2 := by
  rw [originalCoreProductLift_fderiv parameters core point inside,ContinuousLinearMap.comp_apply,
    assembleSpatialCellCLM_apply,originalProduct_planarBasis,
    originalCoreCartesianLift_partial parameters core _ (by
      change ‖planarPart (assembleSpatialCell point.1 point.2)‖<1
      simpa only [planarPart_assembleSpatialCell] using inside)]
  congr 1
  apply Subtype.ext
  exact planarPart_assembleSpatialCell point.1 point.2

 theorem originalCoreProductLift_axial {dimension : ℕ} (parameters : PhaseParameters) (core : ACore parameters dimension)
    (point : SpatialPlane × ℝ) (inside : ‖point.1‖<1) :
    fderiv ℝ (originalCoreProductLift parameters core) point (0,1)=
      coreValue (timeDerivativeCore parameters core) ⟨point.1,inside.le⟩ point.2 := by
  rw [originalCoreProductLift_fderiv parameters core point inside,ContinuousLinearMap.comp_apply,
    assembleSpatialCellCLM_apply,originalProduct_axialBasis,
    originalCoreCartesianLift_axial parameters core _ (by
      change ‖planarPart (assembleSpatialCell point.1 point.2)‖<1
      simpa only [planarPart_assembleSpatialCell] using inside)]
  congr 1
  apply Subtype.ext
  exact planarPart_assembleSpatialCell point.1 point.2

/-- Exact same-field derivative transport on a fixed native collar. -/
theorem originalCoreProductLift_annular_fderiv {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (lower : ℝ)
    (field : SpatialPlane × ℝ → ComplexEuclidean dimension)
    (same : ∀ (point : SpatialPlane × ℝ) (inside : ‖point.1‖∈Icc lower 1),
      coreValue core ⟨point.1,inside.2⟩ point.2=field point)
    (point : SpatialPlane × ℝ) (inside : ‖point.1‖∈Ioo lower 1) :
    fderiv ℝ (originalCoreProductLift parameters core) point=fderiv ℝ field point := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [((isOpen_Ioo.preimage continuous_norm).prod isOpen_univ).mem_nhds
    (show point∈{query : SpatialPlane | ‖query‖∈Ioo lower 1} ×ˢ (univ : Set ℝ) from ⟨inside,mem_univ _⟩)] with query member
  rw [originalCoreProductLift_value parameters core query member.1.2]
  exact same query ⟨member.1.1.le,member.1.2.le⟩

end Grad.OriginalCoreRealization
