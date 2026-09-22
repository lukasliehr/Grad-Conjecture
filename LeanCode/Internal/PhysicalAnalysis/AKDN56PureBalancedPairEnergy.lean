import AKDN55FiniteTerminalSquareEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.AnnularSmoothCore
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalTerminalAllocation

/-- Joint terminal allocation acts on the SAME balanced pair. Its product
norm is controlled without multiplying independent high coefficient factors. -/
theorem purePair_jointAllocation (parameters : PhaseParameters) (field : ACore parameters 3)
    (rho epsilon : ℝ) (total extra power : ℕ) (positive : 0 < total) (paid : extra+power≤total)
    (small : physicalBudget parameters field rho epsilon 10≤1)
    (base middle high : PhysicalHilbertPair)
    (middleSame : ∀ mode : ℤ × ℤ, hilbertPairCoefficient mode middle=
      (annularFrequency mode.1 mode.2 : ℂ)^power • hilbertPairCoefficient mode base)
    (highSame : ∀ mode : ℤ × ℤ, hilbertPairCoefficient mode high=
      (annularFrequency mode.1 mode.2 : ℂ)^total • hilbertPairCoefficient mode base) :
    ‖(1+physicalBudget parameters field rho epsilon (10+extra)) • middle‖ ≤
      2*(1+physicalInterpolationConstant 10 total)*
        (‖high‖+(1+physicalBudget parameters field rho epsilon (10+total))*‖base‖) := by
  let constant := 2*(1+physicalInterpolationConstant 10 total)
  let budget := 1+physicalBudget parameters field rho epsilon (10+total)
  have constant0 : 0 ≤ constant := by
    have one := physicalInterpolationConstant_one_le 10 total
    dsimp only [constant]
    positivity
  have budget0 : 0 ≤ budget := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have first := pureCell_jointAllocation parameters field rho epsilon 10 total extra power positive paid small
    base.1 middle.1 high.1 (fun mode => congrArg Prod.fst (middleSame mode)) (fun mode => congrArg Prod.fst (highSame mode))
  have second := pureCell_jointAllocation parameters field rho epsilon 10 total extra power positive paid small
    base.2 middle.2 high.2 (fun mode => congrArg Prod.snd (middleSame mode)) (fun mode => congrArg Prod.snd (highSame mode))
  rw [Prod.norm_def]
  apply max_le
  · apply first.trans
    exact mul_le_mul_of_nonneg_left (add_le_add (norm_fst_le high)
      (mul_le_mul_of_nonneg_left (norm_fst_le base) budget0)) constant0
  · apply second.trans
    exact mul_le_mul_of_nonneg_left (add_le_add (norm_snd_le high)
      (mul_le_mul_of_nonneg_left (norm_snd_le base) budget0)) constant0

theorem purePair_jointEnergy (parameters : PhaseParameters) (field : ACore parameters 3)
    (rho epsilon : ℝ) (total extra power : ℕ) (positive : 0 < total) (paid : extra+power≤total)
    (small : physicalBudget parameters field rho epsilon 10≤1)
    (measure : Measure ℝ) (base middle high : ℝ → PhysicalHilbertPair)
    (baseMeasurable : AEStronglyMeasurable base measure) (highMeasurable : AEStronglyMeasurable high measure)
    (middleSame : ∀ᵐ radius ∂measure, ∀ mode : ℤ × ℤ, hilbertPairCoefficient mode (middle radius)=
      (annularFrequency mode.1 mode.2 : ℂ)^power • hilbertPairCoefficient mode (base radius))
    (highSame : ∀ᵐ radius ∂measure, ∀ mode : ℤ × ℤ, hilbertPairCoefficient mode (high radius)=
      (annularFrequency mode.1 mode.2 : ℂ)^total • hilbertPairCoefficient mode (base radius))
    (highPayment basePayment : ℝ) (high0 : 0≤highPayment) (base0 : 0≤basePayment)
    (highEnergy : (∫⁻ radius, ENNReal.ofReal (‖high radius‖^2) ∂measure) ≤ ENNReal.ofReal (highPayment^2))
    (baseEnergy : (∫⁻ radius, ENNReal.ofReal (‖base radius‖^2) ∂measure) ≤ ENNReal.ofReal (basePayment^2)) :
    (∫⁻ radius, ENNReal.ofReal
      (‖(1+physicalBudget parameters field rho epsilon (10+extra)) • middle radius‖^2) ∂measure) ≤
      ENNReal.ofReal ((4*(1+physicalInterpolationConstant 10 total)*
        (highPayment+(1+physicalBudget parameters field rho epsilon (10+total))*basePayment))^2) := by
  have bound : ∀ᵐ radius ∂measure,
      ‖(1+physicalBudget parameters field rho epsilon (10+extra)) • middle radius‖ ≤
        (2*(1+physicalInterpolationConstant 10 total))*
          (‖high radius‖+(1+physicalBudget parameters field rho epsilon (10+total))*‖base radius‖) := by
    filter_upwards [middleSame,highSame] with radius one two
    exact purePair_jointAllocation parameters field rho epsilon total extra power positive paid small
      (base radius) (middle radius) (high radius) one two
  have actual := twoInput_squareEnergy measure
    (fun radius => (1+physicalBudget parameters field rho epsilon (10+extra)) • middle radius) high base
    highMeasurable baseMeasurable (2*(1+physicalInterpolationConstant 10 total))
    (1+physicalBudget parameters field rho epsilon (10+total)) highPayment basePayment
    (mul_nonneg (by norm_num) (add_nonneg zero_le_one (zero_le_one.trans (physicalInterpolationConstant_one_le 10 total))))
    (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) high0 base0 bound highEnergy baseEnergy
  exact actual.trans_eq (by congr 1; ring)

end Grad.OriginalCartesianTameEstimate
