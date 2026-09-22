import GQC48GaugeActionBounds
import GQC49SmoothCoreEquivalence

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem compensatedNorm_remove_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (data : CompensatedData L sigma gamma ell)
    (removed : APSmooth L sigma gamma ell 3)
    (member : apSmoothGrade L sigma gamma ell 3 (grade + 1) removed ∈
      apComplementRange L sigma gamma ell (grade + 1)) :
    compensatedNorm admissible grade ((data.1, data.2 - removed) - data) ≤
      Real.sqrt 5 * removedGraphConstant * ‖apSmoothGrade L sigma gamma ell 3 (grade + 1) removed‖ := by
  have difference : (data.1, data.2 - removed) - data = -(0, removed) := by
    apply Prod.ext
    · change data.1 - data.1 = -(0 : APSmooth L sigma gamma ell 1)
      simp only [sub_self, neg_zero]
    · change (data.2 - removed) - data.2 = -removed
      abel
  exact (congrArg (compensatedNorm admissible grade) difference).trans_le
    ((compensatedNorm_neg admissible grade (0, removed)).trans_le
      (compensatedRemovedGraph_bound admissible grade removed member))

def transferDifferenceConstant {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) : ℝ :=
  Real.sqrt 5 * removedGraphConstant * extensionActionConstant admissible gauge (grade + 1) *
    gaugeActionConstant gauge (grade + 1) * reconstructionBoundConstant L gamma grade

theorem compensatedForward_difference_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible gauge))
    (laws : ∀ grade, ActualProjectionLaws admissible gauge grade)
    (grade : ℕ) (data : CompensatedData L sigma gamma ell) :
    compensatedNorm admissible grade (compensatedForward admissible gauge coherent inverseCoherent data - data) ≤
      transferDifferenceConstant admissible gauge grade * compensatedNorm admissible grade data := by
  let removed := apSmoothExtension admissible gauge coherent inverseCoherent
    (apSmoothGauge admissible gauge coherent (compensatedReconstruct admissible data))
  have member : apSmoothGrade L sigma gamma ell 3 (grade + 1) removed ∈
      apComplementRange L sigma gamma ell (grade + 1) := by
    have result := apSmoothCurrent_removed_mem admissible gauge coherent inverseCoherent laws
      (compensatedReconstruct admissible data) (grade + 1)
    change apSmoothGrade L sigma gamma ell 3 (grade + 1)
      (compensatedReconstruct admissible data - (compensatedReconstruct admissible data - removed)) ∈ _ at result
    simpa only [sub_sub_cancel] using result
  have removedBound : ‖apSmoothGrade L sigma gamma ell 3 (grade + 1) removed‖ ≤
      extensionActionConstant admissible gauge (grade + 1) *
        (gaugeActionConstant gauge (grade + 1) *
          (reconstructionBoundConstant L gamma grade * compensatedNorm admissible grade data)) := by
    exact (apExtensionMap_bound admissible gauge (grade + 1) _).trans
      (mul_le_mul_of_nonneg_left ((apGaugeMap_bound admissible gauge (grade + 1) _).trans
        (mul_le_mul_of_nonneg_left (compensatedReconstruct_bound admissible grade data)
          (gaugeActionConstant_nonnegative admissible gauge (grade + 1))))
        (extensionActionConstant_nonnegative admissible gauge (grade + 1)))
  exact (compensatedNorm_remove_bound admissible grade data removed member).trans
    ((mul_le_mul_of_nonneg_left removedBound
      (mul_nonneg (Real.sqrt_nonneg _) removedGraphConstant_nonnegative)).trans_eq (by
        unfold transferDifferenceConstant
        ring))

def backwardDifferenceConstant (grade : ℕ) : ℝ :=
  Real.sqrt 5 * removedGraphConstant * apComplementConstant (grade + 1) * remainderBoundConstant

theorem compensatedBackward_difference_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (data : CompensatedData L sigma gamma ell) :
    compensatedNorm admissible grade (compensatedBackward L sigma gamma ell data - data) ≤
      backwardDifferenceConstant grade * compensatedNorm admissible grade data := by
  let removed := apSmoothComplement L sigma gamma ell data.2
  have member : apSmoothGrade L sigma gamma ell 3 (grade + 1) removed ∈
      apComplementRange L sigma gamma ell (grade + 1) := ⟨data.2.val (grade + 1), rfl⟩
  have removedBound : ‖apSmoothGrade L sigma gamma ell 3 (grade + 1) removed‖ ≤
      apComplementConstant (grade + 1) * (remainderBoundConstant * compensatedNorm admissible grade data) :=
    (apComplement_bound L sigma gamma ell (grade + 1) _).trans
      (mul_le_mul_of_nonneg_left (compensatedRemainder_bound admissible grade data)
        (apComplementConstant_nonnegative (grade + 1)))
  exact (compensatedNorm_remove_bound admissible grade data removed member).trans
    ((mul_le_mul_of_nonneg_left removedBound
      (mul_nonneg (Real.sqrt_nonneg _) removedGraphConstant_nonnegative)).trans_eq (by
        unfold backwardDifferenceConstant
        ring))

end Grad.GaugeCoefficients.Physical.Compensated
