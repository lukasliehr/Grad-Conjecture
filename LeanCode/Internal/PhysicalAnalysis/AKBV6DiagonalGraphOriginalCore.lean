import AKBV5SameAllGradeOriginalCore
import JetInclusionsProof

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.WeightedJets Grad.CartesianStartup Grad.ActualOriginalSourceMoments
open Grad.WeightedJets.Inclusions Grad.CellWeights

/-- Only the diagonal all-order graph is needed: its unused cell powers are removed separately in each derivative coordinate. -/
def diagonalGraphToMixed {dimension grade : ℕ} {domain : Set Spatial}
    (jet : GraphGrade dimension grade grade domain) : Mixed dimension grade domain :=
  ofCoordinates dimension grade domain (fun index => grade - degree index)
    (fun index => inverseFieldCLM dimension domain (degree index) (jet.val index)) (by
      intro index cell vector test
      have zero : inverseFieldCLM dimension domain (grade - degree (zeroIndex grade))
          (inverseFieldCLM dimension domain (degree (zeroIndex grade)) (jet.val (zeroIndex grade))) =
          base dimension grade domain (fun _ => grade) jet := by
        simp only [degree_zero, Nat.sub_zero, inverseFieldCLM_zero, ContinuousLinearMap.id_apply]
        rfl
      rw [zero, testPairing_inverse, jet_identity]
      have power : grade - degree index + degree index = grade := Nat.sub_add_cancel (degree_le index)
      have factors := inverseFactor_positiveFactor (grade - degree index) (degree index) cell
      rw [power] at factors
      change inverseFactor (degree index) cell *
          (((-1 : ℂ) ^ degree index * positiveFactor grade cell) * _) = _
      calc
        _ = ((-1 : ℂ) ^ degree index *
            (inverseFactor (degree index) cell * positiveFactor grade cell)) *
              derivativeTestPairing dimension grade domain index cell vector test
                (base dimension grade domain (fun _ => grade) jet) := by ring
        _ = _ := by rw [factors])

theorem diagonalGraphToMixed_base {dimension grade : ℕ} {domain : Set Spatial}
    (jet : GraphGrade dimension grade grade domain) :
    base dimension grade domain (fun index => grade - degree index) (diagonalGraphToMixed jet) =
      base dimension grade domain (fun _ => grade) jet := by
  change inverseFieldCLM dimension domain (grade - degree (zeroIndex grade))
    (inverseFieldCLM dimension domain (degree (zeroIndex grade)) (jet.val (zeroIndex grade))) = _
  simp only [degree_zero, Nat.sub_zero, inverseFieldCLM_zero, ContinuousLinearMap.id_apply]
  rfl

theorem diagonalGraphToMixed_norm {dimension grade : ℕ} {domain : Set Spatial}
    (jet : GraphGrade dimension grade grade domain) : ‖diagonalGraphToMixed jet‖ ≤ ‖jet‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [jet_norm_sq, jet_norm_sq]
  apply Finset.sum_le_sum
  intro index _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (inverse_norm_le dimension domain (degree index) (jet.val index))

/-- Standard all-order/all-cell Sobolev regularity recovers the original analytic core without any new smoothness premise or loss of width. -/
theorem allDiagonalGraphs_sameOriginalCore {dimension : ℕ} (parameters : PhaseParameters)
    (field : StartupL2 dimension)
    (jets : ∀ grade, GraphGrade dimension grade grade openUnitDisk)
    (sameBase : ∀ grade, base dimension grade openUnitDisk (fun _ => grade) (jets grade) = field) :
    ∃ core : ACore parameters dimension,
      (originalSourceMoments parameters core).field = field ∧
      ∀ grade, ‖aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) core)‖ ≤ ‖jets grade‖ := by
  obtain ⟨core,same,norms⟩ := allMixed_sameOriginalCore parameters field
    (fun grade => diagonalGraphToMixed (jets grade))
    (fun grade => (diagonalGraphToMixed_base (jets grade)).trans (sameBase grade))
  exact ⟨core,same,fun grade => (norms grade).le.trans (diagonalGraphToMixed_norm (jets grade))⟩

end Grad.CartesianCoreRecovery
