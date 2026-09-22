import AKBZ26ZeroPhaseCoefficientPayment

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers

/-- Every positive derivative allocation: phase a>0 or raw coefficient b>0.
The total unknown/output grade is a+b+c, including the exact zero-phase case. -/
theorem everyPositiveAllocation_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset phaseRank inputRank : ℕ) (phaseWord : Fin phaseRank → Fin 2) (index : CartesianMultiIndex)
    (positive : 0<phaseRank+cartesianOrder index) (inputWord : CartesianWord inputRank)
    (profile : EstimateProfile) (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧
      ∀ (inputDimension outputDimension : ℕ) (base : ACore parameters 3) (rho curvature : ℝ)
        (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell inputDimension outputDimension)
        (_estimate : FamilyEstimate parameters base rho curvature offset profile family reference)
        (field : ACore parameters inputDimension),
      physicalBudget parameters base rho curvature offset≤1 →
      ‖startupAllocatedKernel admissible (family (cartesianOrder index+phaseRank)) phaseRank phaseWord
        (sharpCoefficientIndex index phaseRank) (sharpCoefficientIndex_allocation phaseRank index)
        (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseRank-1) inputWord)‖≤
      epsilon*originalGradeNorm (phaseRank+cartesianOrder index+inputRank) field+
        remainder*((1+physicalBudget parameters base rho curvature (offset+(phaseRank+cartesianOrder index+inputRank)))*
          originalGradeNorm 0 field) := by
  by_cases zero : phaseRank=0
  · subst phaseRank
    simpa only [Nat.zero_sub,Nat.zero_add] using
      zeroPhasePositiveCoefficient_oneHigh parameters admissible offset inputRank phaseWord index
        (by simpa only [Nat.zero_add] using positive) inputWord profile fixedNonnegative deviationNonnegative epsilon epsilonPositive
  · exact restoredOriginalKernel_oneHigh parameters admissible offset phaseRank inputRank (by omega)
      phaseWord index inputWord profile fixedNonnegative deviationNonnegative epsilon epsilonPositive

end Grad.OriginalCartesianTameEstimate
