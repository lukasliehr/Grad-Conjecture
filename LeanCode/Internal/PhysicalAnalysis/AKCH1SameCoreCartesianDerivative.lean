import AKCE15ActualNativeOriginalConstraints
import AKBI22ExactOriginalDeterminantConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped Topology
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.OriginalKernelHomogeneousGraph Grad.SourceCollar Grad.DiskExtension.Operator Grad.NonlinearRange

/-- The existing original Fourier realization, expressed in the Cartesian
product coordinates used by the actual native equations. -/
def originalCoreProductLift {dimension : ℕ} (parameters : PhaseParameters) (core : ACore parameters dimension) :
    SpatialPlane × ℝ → ComplexEuclidean dimension :=
  fun point => originalCoreCartesianLift parameters core (assembleSpatialCell point.1 point.2)

theorem originalCoreProductLift_value {dimension : ℕ} (parameters : PhaseParameters) (core : ACore parameters dimension)
    (point : SpatialPlane × ℝ) (inside : ‖point.1‖<1) :
    originalCoreProductLift parameters core point=
      coreValue core ⟨point.1,inside.le⟩ point.2 := by
  rw [originalCoreProductLift,originalCoreCartesianLift_value parameters core _ (by
    change ‖planarPart (assembleSpatialCell point.1 point.2)‖<1
    simpa only [planarPart_assembleSpatialCell] using inside)]
  congr 1
  apply Subtype.ext
  exact planarPart_assembleSpatialCell point.1 point.2

theorem originalCoreProductLift_fderiv {dimension : ℕ} (parameters : PhaseParameters) (core : ACore parameters dimension)
    (point : SpatialPlane × ℝ) (inside : ‖point.1‖<1) :
    fderiv ℝ (originalCoreProductLift parameters core) point=
      (fderiv ℝ (originalCoreCartesianLift parameters core) (assembleSpatialCell point.1 point.2)).comp assembleSpatialCellCLM := by
  exact ((originalCoreCartesianLift_hasFDerivAt parameters core _ (by
    change ‖planarPart (assembleSpatialCell point.1 point.2)‖<1
    simpa only [planarPart_assembleSpatialCell] using inside)).comp point assembleSpatialCellCLM.hasFDerivAt).fderiv

/-- Punctured SAME values suffice for equality of genuine Frechet derivatives;
no derivative matching or regularity premise is added to the native field. -/
theorem originalCoreProductLift_same_fderiv {dimension : ℕ} (parameters : PhaseParameters) (core : ACore parameters dimension)
    (field : SpatialPlane × ℝ → ComplexEuclidean dimension)
    (same : ∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle))=field (point.val,axial))
    (point : SpatialPlane × ℝ) (inside : ‖point.1‖∈Ioo 0 1) :
    fderiv ℝ (originalCoreProductLift parameters core) point=fderiv ℝ field point := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [((isOpen_Ioo.preimage continuous_norm).prod isOpen_univ).mem_nhds
    (show point∈{query : SpatialPlane | ‖query‖∈Ioo 0 1} ×ˢ (univ : Set ℝ) from ⟨inside,mem_univ _⟩)] with query member
  rw [originalCoreProductLift_value parameters core query member.1.2,coreValue_originalPhysical]
  exact same ⟨query.1,member.1.2.le⟩ member.1.1 query.2

end Grad.OriginalCoreRealization
