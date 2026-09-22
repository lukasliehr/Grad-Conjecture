import AKCX38SameSignedSpatialEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier

variable (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)

def startupCutoffSpatialGraph (order weight : ℕ) :
    GraphGrade 3 order weight openUnitDisk →L[ℂ] GraphGrade 3 order weight openUnitDisk :=
  compactJetMultiplier 3 order openUnitDisk openUnitDisk_isOpen cutoff smooth compact
    (fun _ => weight) (constantExponent_antitone order weight)

theorem startupCutoffSpatialGraph_base (order weight : ℕ) (field : GraphGrade 3 order weight openUnitDisk) :
    base 3 order openUnitDisk (fun _ => weight) (startupCutoffSpatialGraph cutoff smooth compact order weight field) =
      startupCutoffL2 cutoff smooth compact (base 3 order openUnitDisk (fun _ => weight) field) := by
  change base 3 order openUnitDisk (fun _ => weight)
    (jetMultiplier 3 order openUnitDisk openUnitDisk_isOpen (compactSymbol order openUnitDisk cutoff smooth compact)
      (fun _ => weight) (constantExponent_antitone order weight) field) = _
  rw [jetMultiplier_base_apply]
  apply startupField_ae_ext
  filter_upwards [fieldMultiplier_ae 3 openUnitDisk openUnitDisk_isOpen
      (derivativeScalar (compactSymbol order openUnitDisk cutoff smooth compact) (zeroIndex order))
      (base 3 order openUnitDisk (fun _ => weight) field),
    startupCutoffL2_ae cutoff smooth compact (base 3 order openUnitDisk (fun _ => weight) field)] with point one two
  intro cell
  rw [one cell,two cell]
  rfl

theorem startupCutoff_preservesGraph : StartupPreservesGraph (startupCutoffL2 cutoff smooth compact) := by
  intro order weight field
  exact ⟨startupCutoffSpatialGraph cutoff smooth compact order weight field,
    startupCutoffSpatialGraph_base cutoff smooth compact order weight field⟩

def StartupSignedFamily.spatialCutoff {L ell : ℝ} (family : StartupSignedFamily 3 L ell) : StartupSignedFamily 3 L ell where
  field := startupCutoffL2 cutoff smooth compact family.field
  moment power := startupCutoffL2 cutoff smooth compact (family.moment power)
  same power := by
    filter_upwards [startupCutoffL2_ae cutoff smooth compact family.field,
      startupCutoffL2_ae cutoff smooth compact (family.moment power),family.same power] with point one two same
    intro cell
    rw [one cell,two cell,same cell]
    exact smul_comm _ _ _

theorem StartupSignedFamily.HasSpatialGrade.spatialCutoff {L ell : ℝ} {order : ℕ}
    {family : StartupSignedFamily 3 L ell} (regular : family.HasSpatialGrade order) :
    (family.spatialCutoff cutoff smooth compact).HasSpatialGrade order := by
  intro power weight
  obtain ⟨field,same⟩ := regular power weight
  exact ⟨startupCutoffSpatialGraph cutoff smooth compact order weight field,
    (startupCutoffSpatialGraph_base cutoff smooth compact order weight field).trans
      (congrArg (startupCutoffL2 cutoff smooth compact) same)⟩

end Grad.CartesianStartup
