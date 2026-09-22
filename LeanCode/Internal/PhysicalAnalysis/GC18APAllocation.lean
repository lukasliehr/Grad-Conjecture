import GC18APShift

noncomputable section

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

abbrev APAllocation (grade : ℕ) :=
  (index : DerivativeIndex grade) × (split : DerivativeSplit index) ×
    DerivativeSplit (upperDerivativeIndex index split)

def apOutputIndex {grade : ℕ} (allocation : APAllocation grade) : DerivativeIndex grade := allocation.1

def apPhaseIndex {grade : ℕ} (allocation : APAllocation grade) : DerivativeIndex grade :=
  lowerDerivativeIndex allocation.1 allocation.2.1

def apCoefficientIndex {grade : ℕ} (allocation : APAllocation grade) : DerivativeIndex grade :=
  lowerDerivativeIndex (upperDerivativeIndex allocation.1 allocation.2.1) allocation.2.2

def apInputIndex {grade : ℕ} (allocation : APAllocation grade) : DerivativeIndex grade :=
  upperDerivativeIndex (upperDerivativeIndex allocation.1 allocation.2.1) allocation.2.2

def apPhaseWord {grade : ℕ} (allocation : APAllocation grade) :
    Fin (derivativeOrder (apPhaseIndex allocation)) → Fin 2 :=
  cartesianMultiIndexWord (derivativeMultiIndex (apPhaseIndex allocation))

def apMultiplicity {grade : ℕ} (allocation : APAllocation grade) : ℕ :=
  splitMultiplicity allocation.1 allocation.2.1 *
    splitMultiplicity (upperDerivativeIndex allocation.1 allocation.2.1) allocation.2.2

theorem apAllocation_order {grade : ℕ} (allocation : APAllocation grade) :
    derivativeOrder (apPhaseIndex allocation) + derivativeOrder (apCoefficientIndex allocation) +
      derivativeOrder (apInputIndex allocation) = derivativeOrder (apOutputIndex allocation) := by
  have first := derivative_split_order allocation.1 allocation.2.1
  have second := derivative_split_order (upperDerivativeIndex allocation.1 allocation.2.1) allocation.2.2
  dsimp [apPhaseIndex, apCoefficientIndex, apInputIndex, apOutputIndex]
  omega

theorem apAllocation_order_le {grade : ℕ} (allocation : APAllocation grade) :
    derivativeOrder (apPhaseIndex allocation) + derivativeOrder (apCoefficientIndex allocation) +
      derivativeOrder (apInputIndex allocation) ≤ grade := by
  rw [apAllocation_order]
  exact allocation.1.property

def apAllocationConstant {grade : ℕ} (L sigma gamma : ℝ) (allocation : APAllocation grade) : ℝ :=
  apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) * (Real.sqrt 2) ^ grade

def apMultiplierConstant (L sigma gamma : ℝ) (grade : ℕ) : ℝ :=
  ∑ allocation : APAllocation grade, (apMultiplicity allocation : ℝ) * apAllocationConstant L sigma gamma allocation

theorem apAllocationConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade : ℕ} (allocation : APAllocation grade) :
    0 ≤ apAllocationConstant L sigma gamma allocation :=
  mul_nonneg (apRatioConstant_nonnegative admissible _) (pow_nonneg (Real.sqrt_nonneg _) _)

theorem apMultiplierConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ apMultiplierConstant L sigma gamma grade :=
  Finset.sum_nonneg (fun allocation _ => mul_nonneg (Nat.cast_nonneg _) (apAllocationConstant_nonnegative admissible allocation))

end Grad.GaugeCoefficients.Physical.RadialLedger
