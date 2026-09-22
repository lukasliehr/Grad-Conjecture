import AKBS5ActualNormalizedSourceFirst
import COR16Consumer
import SD1Consumer
import CellFieldExchange
import AXI1FaithfulL2

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.WeightedJets Grad.CompatibleCompletion Grad.Constraints.Multipliers

/-- The original unordered multi-index and the existing weak jet index are the same finite index. -/
def originalJetIndexEquiv (grade : ℕ) : GradeMultiIndex grade ≃ JetIndex grade :=
  gradeMultiIndexEquiv grade

theorem originalJetIndexEquiv_degree (grade : ℕ) (index : GradeMultiIndex grade) :
    degree (originalJetIndexEquiv grade index) = cartesianOrder index.toCartesian := rfl

theorem originalJetIndexEquiv_word (grade : ℕ) (index : GradeMultiIndex grade) :
    derivativeWord (originalJetIndexEquiv grade index) = cartesianMultiIndexWord index.toCartesian := rfl

/-- Exact original grade norm from the SAME complete mixed-jet coordinates, using the accepted full-cell energy exchange. -/
theorem originalCore_norm_eq_mixed {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (jet : Mixed dimension grade openUnitDisk)
    (same : ∀ (cell : ℤ) (index : GradeMultiIndex grade),
      cartesianGradeCoordinates parameters grade field cell index =
        fieldCellProjection dimension openUnitDisk cell (jet.val (originalJetIndexEquiv grade index))) :
    ‖GradeCore.ofCoreLinear (grade := grade) field‖ = ‖jet‖ := by
  rw [Grad.Constraints.Gauges.ofCoreLinear_norm_coordinates]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Grad.TensorCellExchange.target_norm_sq]
  simp_rw [same,← Grad.CellEnergy.field_norm_sq_eq_tsum]
  rw [jet_norm_sq]
  exact Equiv.sum_comp (originalJetIndexEquiv grade) (fun index => ‖jet.val index‖^2)

/-- The exact norm identity also controls differences of arbitrary matched original fields and mixed jets. -/
theorem originalCore_dist_eq_mixed {dimension grade : ℕ} (parameters : PhaseParameters)
    (first second : ACore parameters dimension) (firstJet secondJet : Mixed dimension grade openUnitDisk)
    (firstSame : ∀ cell index, cartesianGradeCoordinates parameters grade first cell index =
      fieldCellProjection dimension openUnitDisk cell (firstJet.val (originalJetIndexEquiv grade index)))
    (secondSame : ∀ cell index, cartesianGradeCoordinates parameters grade second cell index =
      fieldCellProjection dimension openUnitDisk cell (secondJet.val (originalJetIndexEquiv grade index))) :
    dist (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) first))
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) second)) = dist firstJet secondJet := by
  rw [dist_eq_norm,dist_eq_norm,← map_sub,← map_sub,aGradeEta_norm]
  apply originalCore_norm_eq_mixed parameters (first-second) (firstJet-secondJet)
  intro cell index
  rw [map_sub,lp.coeFn_sub,Pi.sub_apply,PiLp.sub_apply,firstSame cell index,secondSame cell index]
  exact (map_sub (fieldCellProjection dimension openUnitDisk cell) _ _).symm

end Grad.CartesianCoreRecovery
