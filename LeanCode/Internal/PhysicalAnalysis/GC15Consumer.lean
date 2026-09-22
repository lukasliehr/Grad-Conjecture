import GC15ExpressionProof

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Allocation

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Frame

theorem finiteCoefficientBlock : BlockGoal := blockGoal

/-- The actual AP21 frame of one original all-grade physical state. -/
def actualFrameFamily (parameters : PhaseParameters) (L ell epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3 :=
  fun grade => actualFrameDeviationCoefficient parameters L ell epsilon
    (GradeCore.ofCoreLinear (grade := grade + 4) field)

theorem actualFrameFamily_coherent {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) :
    FamilyCoherent (actualFrameFamily parameters L ell epsilon field) := by
  intro grade other index otherIndex same cell point
  simp only [actualFrameFamily, actualFrameDeviationCoefficient_derivative parameters admissible]
  have orderSame : derivativeOrder index = derivativeOrder otherIndex := congrArg cartesianOrder same
  rw [orderSame]
  unfold frameDeviationMultiDerivative
  simp only [GradeCore.toCore_ofCore]
  rw [same]

theorem actualFrameFamily_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon rho : ℝ) (epsilonSmall : |epsilon| ≤ 1) (field : ACore parameters 3) (grade : ℕ) :
    ‖actualFrameFamily parameters L ell epsilon field grade‖ ≤
      frameConstant parameters L grade * physicalBudget parameters field rho epsilon (4 + grade) := by
  have bound := actualFrameDeviationCoefficient_norm_bound parameters admissible epsilon epsilonSmall
    (GradeCore.ofCoreLinear (grade := grade + 4) field)
  apply bound.trans
  apply mul_le_mul_of_nonneg_left _ (frameConstant_nonnegative parameters admissible.1 grade)
  unfold physicalBudget originalGradeNorm
  rw [Nat.add_comm 4 grade]
  linarith [abs_nonneg rho]

def zeroFamily (L sigma gamma ell : ℝ) (input output : ℕ) :
    CoefficientFamily L sigma gamma ell input output := fun _ => 0

theorem zeroFamily_coherent (L sigma gamma ell : ℝ) (input output : ℕ) :
    FamilyCoherent (zeroFamily L sigma gamma ell input output) := by
  intro grade other index otherIndex _same cell point
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      (0 : OperatorValue input output) =
    ((coefficientScale L sigma gamma ell other cell otherIndex point : ℂ)⁻¹) •
      (0 : OperatorValue input output)
  apply ContinuousLinearMap.ext
  intro vector
  simp only [smul_apply, zero_apply, smul_zero]

theorem zeroFamily_norm (L sigma gamma ell : ℝ) (input output grade : ℕ) :
    ‖zeroFamily L sigma gamma ell input output grade‖ ≤ 0 := by
  change ‖(0 : WeightedAmbient grade input output)‖ ≤ 0
  simp only [norm_zero, le_refl]

def actualFrameProductConstant (parameters : PhaseParameters) (L lowBound : ℝ) (grade : ℕ) : ℝ :=
  productDeviationConstant 4 lowBound (fun _ => 0) (fun _ => 0)
    (frameConstant parameters L) (frameConstant parameters L) grade

theorem actualFrameProductConstant_nonnegative (parameters : PhaseParameters) {L lowBound : ℝ}
    (positive : 0 < L) (lowNonnegative : 0 ≤ lowBound) (grade : ℕ) :
    0 ≤ actualFrameProductConstant parameters L lowBound grade :=
  productDeviationConstant_nonnegative 4 lowBound lowNonnegative _ _ _ _
    (fun _ => le_refl 0) (fun _ => le_refl 0)
    (frameConstant_nonnegative parameters positive) (frameConstant_nonnegative parameters positive) grade

/-- Immediate genuine physical consumer: the square of the actual AP21
frame deviation has only one unrestricted high original state norm. A B10
bound supplies the fixed low B4 bound; no high-grade smallness is imposed. -/
theorem actual_frame_product_one_high {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lowBound : ℝ) (lowNonnegative : 0 ≤ lowBound)
    (epsilon rho : ℝ) (epsilonSmall : |epsilon| ≤ 1) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 10 ≤ lowBound) (grade : ℕ) :
    ‖coefficientComposition admissible grade
        (actualFrameFamily parameters L ell epsilon field grade)
        (actualFrameFamily parameters L ell epsilon field grade)‖ ≤
      actualFrameProductConstant parameters L lowBound grade *
        physicalBudget parameters field rho epsilon (grade + 4) := by
  have lowFour := (physicalBudget_monotone parameters field rho epsilon (by norm_num : 4 ≤ 10)).trans low
  have coherent := actualFrameFamily_coherent parameters admissible epsilon field
  have zeroCoherent := zeroFamily_coherent L parameters.sigma0 parameters.gamma ell 3 3
  have zeroBound := zeroFamily_norm L parameters.sigma0 parameters.gamma ell 3 3
  have deviationBound (order : ℕ) :
      ‖actualFrameFamily parameters L ell epsilon field order -
        zeroFamily L parameters.sigma0 parameters.gamma ell 3 3 order‖ ≤
      frameConstant parameters L order * physicalBudget parameters field rho epsilon (4 + order) := by
    change ‖actualFrameFamily parameters L ell epsilon field order - 0‖ ≤ _
    rw [sub_zero]
    exact actualFrameFamily_bound parameters admissible epsilon rho epsilonSmall field order
  have bound := composition_deviation_bound parameters admissible 4 lowBound lowNonnegative field rho epsilon lowFour
    (actualFrameFamily parameters L ell epsilon field)
    (zeroFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (actualFrameFamily parameters L ell epsilon field)
    (zeroFamily L parameters.sigma0 parameters.gamma ell 3 3)
    coherent zeroCoherent coherent zeroCoherent
    (fun _ => 0) (fun _ => 0) (frameConstant parameters L) (frameConstant parameters L)
    (fun _ => le_refl 0) (fun _ => le_refl 0)
    (frameConstant_nonnegative parameters admissible.1) (frameConstant_nonnegative parameters admissible.1)
    zeroBound zeroBound deviationBound deviationBound grade
  have zeroComposition : coefficientComposition admissible grade
      (zeroFamily L parameters.sigma0 parameters.gamma ell 3 3 grade)
      (zeroFamily L parameters.sigma0 parameters.gamma ell 3 3 grade) = 0 :=
    (compositionRightLinear admissible grade (0 : Coefficient L parameters.sigma0 parameters.gamma ell grade 3 3)).map_zero
  rw [zeroComposition, sub_zero] at bound
  simpa only [actualFrameProductConstant, Nat.add_comm 4 grade] using bound

end Grad.GaugeCoefficients.Physical.Allocation
