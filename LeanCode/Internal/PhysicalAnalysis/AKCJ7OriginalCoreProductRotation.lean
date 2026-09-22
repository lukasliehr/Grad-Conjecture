import AKCJ4SameRetainedScalarCore
import AKCH5OriginalNativeDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped Topology
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.NonlinearRange
open Grad.ActualCartesianDescent Grad.PhysicalFamily Grad.SourceCollar Grad.DiskExtension.Operator
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- The original angular generator is the genuine Cartesian derivative in Jy. -/
theorem originalCoreProductLift_rotation {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (point : SpatialPlane×ℝ) (inside : ‖point.1‖<1) :
    coreValue (rotationCore parameters core) ⟨point.1,inside.le⟩ point.2=
      fderiv ℝ (originalCoreProductLift parameters core) point (planeQuarterTurn point.1,0) := by
  have direction : (planeQuarterTurn point.1,(0:ℝ))=
      point.1 0 • (spatialBasis (1 : Fin 2),(0:ℝ))-point.1 1 • (spatialBasis (0 : Fin 2),(0:ℝ)) := by
    apply Prod.ext
    · ext coordinate
      fin_cases coordinate <;> simp [planeQuarterTurn,spatialBasis]
    · simp
  rw [direction,map_sub,map_smul,map_smul,
    originalCoreProductLift_partial parameters core point inside 1,
    originalCoreProductLift_partial parameters core point inside 0]
  simp only [rotationCore,LinearMap.sub_apply,LinearMap.comp_apply,coreValue_subtract,
    coreValue_coordinate]

end Grad.OriginalCoreRealization
