import AKDW30SameCutoffTensorCores
import AKCX59FixedNativeRadialCutoffs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.OriginalMainConsumer
open Grad.CartesianStartup Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.ClosedJets Grad.CartesianState
open Grad.ActualOriginalSourceFirst
open Grad.ActualOriginalSourceMoments Grad.OriginalCoreRealization Grad.OriginalCartesianTameEstimate

/-- The literal fixed radial partition acts as the identity on the same
weighted field; neither the phase nor the axial width is changed. -/
theorem actualNativeCutoff_partition_field (field : StartupL2 3) :
    startupCutoffL2 actualNativeInsideCutoff actualNativeInsideCutoff_smooth actualNativeInsideCutoff_compact field+
      startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact field=field := by
  apply Lp.ext
  filter_upwards [startupCutoffL2_ae actualNativeInsideCutoff actualNativeInsideCutoff_smooth actualNativeInsideCutoff_compact field,
    startupCutoffL2_ae actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact field,
    Lp.coeFn_add (startupCutoffL2 actualNativeInsideCutoff actualNativeInsideCutoff_smooth actualNativeInsideCutoff_compact field)
      (startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact field),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point insideCut annularCut added inside
  rw [added]
  apply lp.ext
  funext cell
  change startupCutoffL2 actualNativeInsideCutoff actualNativeInsideCutoff_smooth actualNativeInsideCutoff_compact field point cell+
    startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact field point cell=field point cell
  rw [insideCut cell,annularCut cell,actualNativeCutoff_partition point inside,Complex.ofReal_sub,Complex.ofReal_one,
    ←add_smul]
  have coefficient : (actualNativeInsideCutoff point : ℂ)+(1-(actualNativeInsideCutoff point : ℂ))=1 := by ring
  rw [coefficient,one_smul]

/-- The original planar norm obeys its genuine graph-norm triangle inequality. -/
theorem originalPlanarNorm_add_le (parameters : PhaseParameters) (grade : ℕ)
    (first second : ACore parameters 3) :
    originalPlanarNorm parameters grade (first+second)≤originalPlanarNorm parameters grade first+originalPlanarNorm parameters grade second := by
  let one := originalSourceSpatialGraph parameters first grade
  let two := originalSourceSpatialGraph parameters second grade
  have firstSame := originalSourceSpatialGraph_base parameters first grade
  have secondSame := originalSourceSpatialGraph_base parameters second grade
  have sumSame : base 3 grade openUnitDisk (fun _ => 0) (one+two)=(originalSourceMoments parameters (first+second)).field := by
    rw [map_add,firstSame,secondSame]
    exact (originalSourceFieldLinear parameters).map_add first second |>.symm
  rw [startupOriginalPlanarNorm_eq_graph parameters (first+second) (one+two) sumSame,
    startupOriginalPlanarNorm_eq_graph parameters first one firstSame,
    startupOriginalPlanarNorm_eq_graph parameters second two secondSame]
  exact norm_add_le one two

/-- The complete SAME original core is controlled by its actual inner and
annular pieces, at every planar rank including zero. -/
theorem actualNativeCutoff_planar_partition (parameters : PhaseParameters) (grade : ℕ)
    (core inner annular : ACore parameters 3)
    (sameInner : originalSourceFieldLinear parameters inner=
      startupCutoffL2 actualNativeInsideCutoff actualNativeInsideCutoff_smooth actualNativeInsideCutoff_compact
        (originalSourceFieldLinear parameters core))
    (sameAnnular : originalSourceFieldLinear parameters annular=
      startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact
        (originalSourceFieldLinear parameters core)) :
    originalPlanarNorm parameters grade core≤originalPlanarNorm parameters grade inner+originalPlanarNorm parameters grade annular := by
  have same : inner+annular=core := by
    apply originalSourceFieldLinear_injective parameters
    rw [map_add,sameInner,sameAnnular]
    exact actualNativeCutoff_partition_field _
  rw [←same]
  exact originalPlanarNorm_add_le parameters grade inner annular

end Grad.OriginalMainConsumer
