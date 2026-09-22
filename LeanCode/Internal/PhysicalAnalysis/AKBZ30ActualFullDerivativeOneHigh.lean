import AKBZ29FullOriginalDerivativeDecomposition

noncomputable section
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers

/-- Whole actual full-cell conjugated coefficient derivative. Every phase,
raw coefficient and displacement allocation is included; the original input
and fixed profile produce one adjustable high norm plus one high coefficient
multiplying the independent base norm. -/
theorem actualFullDerivative_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset inputRank : ℕ) {grade : ℕ} (index : DerivativeIndex grade)
    (positive : 0<derivativeOrder index) (inputWord : CartesianWord inputRank)
    (profile : EstimateProfile) (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧
      ∀ (inputDimension outputDimension : ℕ) (base : ACore parameters 3) (rho curvature : ℝ)
        (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell inputDimension outputDimension)
        (estimate : FamilyEstimate parameters base rho curvature offset profile family reference)
        (field : ACore parameters inputDimension),
      physicalBudget parameters base rho curvature offset≤1 →
      ‖startupDerivativeKernel admissible family estimate.actualCoherent index
        (originalMixedDerivativeCarrier parameters admissible field inputRank (derivativeOrder index-1) inputWord)‖≤
      epsilon*originalGradeNorm (derivativeOrder index+inputRank) field+
        remainder*((1+physicalBudget parameters base rho curvature (offset+(derivativeOrder index+inputRank)))*
          originalGradeNorm 0 field) := by
  classical
  let multiplicity : ℝ := ∑ split : DerivativeSplit index,(splitMultiplicity index split:ℝ)
  have multiplicityNonnegative : 0≤multiplicity := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  let delta := epsilon/(multiplicity+1)
  have deltaPositive : 0<delta := div_pos epsilonPositive (by linarith)
  have perTerm (split : DerivativeSplit index) := everyPositiveAllocation_oneHigh parameters admissible offset
    (phaseSplitOrder index split) inputRank (phaseSplitWord index split) (rawSplitIndex index split)
    (by rw [phaseSplit_total]; exact positive) inputWord profile fixedNonnegative deviationNonnegative delta deltaPositive
  choose constants nonnegative estimates using perTerm
  refine ⟨∑ split,(splitMultiplicity index split:ℝ)*constants split,
    Finset.sum_nonneg (fun split _ => mul_nonneg (Nat.cast_nonneg _) (nonnegative split)),?_⟩
  intro inputDimension outputDimension base rho curvature family reference estimate field low
  have each (split : DerivativeSplit index) :=
    estimates split inputDimension outputDimension base rho curvature family reference estimate field low
  simp_rw [phaseSplit_total] at each
  have leading : multiplicity*delta≤epsilon := by
    have ratio : multiplicity/(multiplicity+1)≤1 := (div_le_one (by linarith : 0<multiplicity+1)).mpr (by linarith)
    calc
      _ = epsilon*(multiplicity/(multiplicity+1)) := by dsimp [delta]; ring
      _ ≤ epsilon*1 := mul_le_mul_of_nonneg_left ratio epsilonPositive.le
      _ = _ := mul_one _
  rw [originalFullDerivative_eq_allocations admissible family estimate.actualCoherent index parameters field inputRank inputWord]
  calc
    _≤∑ split : DerivativeSplit index,(splitMultiplicity index split:ℝ)*
      ‖originalLeibnizKernel admissible family index split
        (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseSplitOrder index split-1) inputWord)‖ := by
      simpa only [norm_smul,Complex.norm_natCast] using norm_sum_le Finset.univ
        (fun split : DerivativeSplit index => (splitMultiplicity index split:ℂ) •
          originalLeibnizKernel admissible family index split
            (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseSplitOrder index split-1) inputWord))
    _≤∑ split : DerivativeSplit index,(splitMultiplicity index split:ℝ)*
      (delta*originalGradeNorm (derivativeOrder index+inputRank) field+
        constants split*((1+physicalBudget parameters base rho curvature (offset+(derivativeOrder index+inputRank)))*originalGradeNorm 0 field)) :=
      Finset.sum_le_sum (fun split _ => mul_le_mul_of_nonneg_left (each split) (Nat.cast_nonneg _))
    _=(multiplicity*delta)*originalGradeNorm (derivativeOrder index+inputRank) field+
      (∑ split : DerivativeSplit index,(splitMultiplicity index split:ℝ)*constants split)*
        ((1+physicalBudget parameters base rho curvature (offset+(derivativeOrder index+inputRank)))*originalGradeNorm 0 field) := by
      dsimp only [multiplicity]
      simp only [Finset.sum_mul,mul_add,Finset.sum_add_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro split membership <;> ring
    _≤_ := by
      exact add_le_add (mul_le_mul_of_nonneg_right leading (originalGradeNorm_nonnegative _ field)) le_rfl

end Grad.OriginalCartesianTameEstimate
