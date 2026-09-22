import ClosedJetSmoothRestriction
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.TangentCone.Real

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Grad.ClosedDiskRegularity
open Grad.ClosedJets Grad.Constraints

/-- The actual closed disk has unique within derivatives, including its boundary. -/
theorem closedDisk_uniqueDiff : UniqueDiffOn ℝ closedUnitDisk := by
  rw [closedUnitDisk_eq_closedBall]
  apply uniqueDiffOn_convex (convex_closedBall (0 : SpatialPlane) 1)
  refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : SpatialPlane) (by norm_num : (0 : ℝ) < 1))
    Metric.ball_subset_closedBall

def withinClosedValue {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) : C(ClosedDisk, ComplexEuclidean dimension) :=
  ⟨fun point => field point.val, continuousOn_iff_continuous_domRestrict.mp smooth.continuousOn⟩

theorem withinClosedValue_lift {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) :
    EqOn (closedDiskLift (withinClosedValue field smooth)) field openUnitDisk := by
  intro point pointIn
  simp only [closedDiskLift, openDiskMembershipClosed point pointIn, dite_true]
  rfl

def withinClosedTensor {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) (order : ℕ) :
    C(ClosedDisk, ContinuousMultilinearMap ℝ (fun _ : Fin order => SpatialPlane) (ComplexEuclidean dimension)) :=
  ⟨fun point => iteratedFDerivWithin ℝ order field closedUnitDisk point.val,
    continuousOn_iff_continuous_domRestrict.mp
      (smooth.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) closedDisk_uniqueDiff)⟩

def withinClosedDerivative {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) (order : ℕ) (word : CartesianWord order) :
    C(ClosedDisk, ComplexEuclidean dimension) :=
  ⟨fun point => withinClosedTensor field smooth order point (fun position => spatialBasis (word position)),
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialPlane)
      (ComplexEuclidean dimension) (fun position => spatialBasis (word position))).continuous.comp
      (withinClosedTensor field smooth order).continuous⟩

theorem withinClosedDerivative_spec {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) (order : ℕ) (word : CartesianWord order) :
    IsCartesianExtension (withinClosedValue field smooth) order word
      (withinClosedDerivative field smooth order word) := by
  intro point pointIn
  have localEquality : closedDiskLift (withinClosedValue field smooth) =ᶠ[𝓝 point.val] field := by
    filter_upwards [openUnitDisk_isOpen.mem_nhds pointIn] with source sourceIn
    exact withinClosedValue_lift field smooth sourceIn
  have smoothAt : ContDiffAt ℝ ∞ field point.val :=
    (smooth.mono openDiskMembershipClosed).contDiffAt (openUnitDisk_isOpen.mem_nhds pointIn)
  change iteratedFDerivWithin ℝ order field closedUnitDisk point.val
    (fun position => spatialBasis (word position)) = _
  rw [iteratedFDerivWithin_eq_iteratedFDeriv closedDisk_uniqueDiff
    (smoothAt.of_le (by exact_mod_cast le_top)) point.property]
  unfold cartesianDerivative
  rw [(localEquality.iteratedFDeriv ℝ order).eq_of_nhds]

/-- A smooth function within the literal closed disk determines every boundary
Cartesian derivative. This construction needs no global smooth extension. -/
def withinClosedJet {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) : ClosedJet dimension where
  value := withinClosedValue field smooth
  smoothInterior := (smooth.mono openDiskMembershipClosed).congr (withinClosedValue_lift field smooth)
  derivativeExists order word :=
    ⟨withinClosedDerivative field smooth order word, withinClosedDerivative_spec field smooth order word⟩

@[simp] theorem withinClosedJet_value {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) (point : ClosedDisk) :
    (withinClosedJet field smooth).value point = field point.val := rfl

theorem withinClosedJet_derivative {dimension order : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) (word : CartesianWord order) (point : ClosedDisk) :
    closedDerivative (withinClosedJet field smooth) order word point =
      iteratedFDerivWithin ℝ order field closedUnitDisk point.val
        (fun position => spatialBasis (word position)) := by
  have equality : closedDerivative (withinClosedJet field smooth) order word =
      withinClosedDerivative field smooth order word :=
    (cartesianExtension_unique _ order word _ (withinClosedDerivative_spec field smooth order word)).symm
  rw [equality]
  rfl

end Grad.ClosedDiskRegularity
