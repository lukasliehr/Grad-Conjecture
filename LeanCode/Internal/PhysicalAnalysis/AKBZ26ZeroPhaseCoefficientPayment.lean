import AKBZ25RestoredOriginalKernelOneHigh

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers

/-- The complementary allocation a=0,b>0 for the SAME original full-cell
coefficient action. It costs coefficient order b and unknown order c. -/
theorem zeroPhasePositiveCoefficient_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset inputRank : ℕ) (phaseWord : Fin 0 → Fin 2) (index : CartesianMultiIndex)
    (coefficientPositive : 0<cartesianOrder index) (inputWord : CartesianWord inputRank)
    (profile : EstimateProfile) (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧
      ∀ (inputDimension outputDimension : ℕ) (base : ACore parameters 3) (rho curvature : ℝ)
        (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell inputDimension outputDimension)
        (_estimate : FamilyEstimate parameters base rho curvature offset profile family reference)
        (field : ACore parameters inputDimension),
      physicalBudget parameters base rho curvature offset≤1 →
      ‖startupAllocatedKernel admissible (family (cartesianOrder index+0)) 0 phaseWord
        (sharpCoefficientIndex index 0) (sharpCoefficientIndex_allocation 0 index)
        (originalMixedDerivativeCarrier parameters admissible field inputRank 0 inputWord)‖≤
      epsilon*originalGradeNorm (cartesianOrder index+inputRank) field+
        remainder*((1+physicalBudget parameters base rho curvature (offset+(cartesianOrder index+inputRank)))*
          originalGradeNorm 0 field) := by
  let grade := cartesianOrder index+inputRank
  let order := cartesianOrder index
  let constant := apRatioConstant L parameters.sigma0 parameters.gamma 0*
    (profile.fixed order+profile.deviation order)
  have constantNonnegative : 0≤constant := mul_nonneg (apRatioConstant_nonnegative admissible 0)
    (add_nonneg (fixedNonnegative order) (deviationNonnegative order))
  have totalPositive : 0<grade := by dsimp [grade]; omega
  have orderPositive : 0<order := by dsimp [order]; omega
  have orderLe : order≤grade := by dsimp [order,grade]; omega
  have allocated : inputRank+0=grade-order := by dsimp [grade,order]; omega
  have adjustedPositive : 0<epsilon/(constant+1) := div_pos epsilonPositive (by linarith)
  obtain ⟨payment,paymentNonnegative,pays⟩ := originalPositiveOrder_oneHigh offset grade order totalPositive
    orderPositive orderLe (epsilon/(constant+1)) adjustedPositive
  refine ⟨constant*payment,mul_nonneg constantNonnegative paymentNonnegative,?_⟩
  intro inputDimension outputDimension base rho curvature family reference estimate field low
  have operator := startupAllocatedKernel_norm admissible (family (cartesianOrder index+0)) 0 phaseWord
    (sharpCoefficientIndex index 0) (sharpCoefficientIndex_allocation 0 index)
  have inputBound := originalMixedDerivativeCarrier_norm parameters admissible field inputRank 0 inputWord
  have kernel := ((startupAllocatedKernel admissible (family (cartesianOrder index+0)) 0 phaseWord
      (sharpCoefficientIndex index 0) (sharpCoefficientIndex_allocation 0 index)).le_opNorm
        (originalMixedDerivativeCarrier parameters admissible field inputRank 0 inputWord)).trans
    (mul_le_mul operator inputBound (norm_nonneg _) (mul_nonneg (apRatioConstant_nonnegative admissible 0) (norm_nonneg _)))
  have coefficient := estimatedFamily_norm_le estimate order
  have paid := pays inputDimension parameters base rho curvature field low
  have less : constant*(epsilon/(constant+1))≤epsilon := by
    have ratio : constant/(constant+1)≤1 := (div_le_one (by linarith : 0<constant+1)).mpr (by linarith)
    calc
      _ = epsilon*(constant/(constant+1)) := by ring
      _ ≤ epsilon*1 := mul_le_mul_of_nonneg_left ratio epsilonPositive.le
      _ = _ := mul_one _
  have inputNonnegative := originalGradeNorm_nonnegative (grade-order) field
  have paymentBound := mul_le_mul_of_nonneg_left paid constantNonnegative
  have leading := mul_le_mul_of_nonneg_right less (originalGradeNorm_nonnegative grade field)
  rw [allocated] at kernel
  have coefficientBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left coefficient (apRatioConstant_nonnegative admissible 0)) inputNonnegative
  change ‖startupAllocatedKernel admissible (family (cartesianOrder index+0)) 0 phaseWord
        (sharpCoefficientIndex index 0) (sharpCoefficientIndex_allocation 0 index)
      (originalMixedDerivativeCarrier parameters admissible field inputRank 0 inputWord)‖≤
    epsilon*originalGradeNorm grade field+(constant*payment)*
      ((1+physicalBudget parameters base rho curvature (offset+grade))*originalGradeNorm 0 field)
  dsimp only [constant] at paymentBound leading
  simp only [Nat.add_zero] at kernel ⊢
  nlinarith only [kernel,coefficientBound,paymentBound,leading]

end Grad.OriginalCartesianTameEstimate
