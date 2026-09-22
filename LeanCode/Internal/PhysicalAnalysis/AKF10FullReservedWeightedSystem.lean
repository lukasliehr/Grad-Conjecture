import AKF9FullPairPhaseSlope

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- The complete genuine weighted evolution, with a finite input reserve
allowed to depend on the requested derivative order. -/
def fullReservedWeightedSystemOperator (grade reserve : ℕ) (radius : ℝ) :
    PhysicalHilbertPair →L[ℂ] PhysicalHilbertPair :=
  phaseSlopePair parameters (reserve + 2) radius +
    (physicalPairMeanFree parameters).comp
      (reservedConjugatedRadialSystemOperator parameters length compact lower state positive
        (lowerHalf.trans_lt (by norm_num)) grade reserve radius)

def fullWeightedSystemSource (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  physicalPairMeanFree parameters
    (conjugatedRadialSystemSource parameters length compact lower positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade radius)

theorem fullReservedWeightedSystemOperator_smooth (grade reserve order : ℕ)
    (enough : order + 5 ≤ reserve + 2)
    (rowsSmooth : ∀ index : Fin 3, ContDiffOn ℝ order
      (radialConjugatedAction parameters lower positive (lowerHalf.trans (by norm_num))
        (lowPhysicalRowKernel parameters length compact state index) (grade + 1) reserve) (Icc lower 1)) :
    ContDiffOn ℝ order
      (fullReservedWeightedSystemOperator parameters length compact lower positive lowerHalf state grade reserve)
      (Icc lower 1) :=
  (phaseSlopePair_smooth parameters (reserve + 2) order enough lower
    (lowerHalf.trans_lt (by norm_num))).add
    (finiteOrderOperatorComposition
      (show ContDiffOn ℝ order (fun _ : ℝ => physicalPairMeanFree parameters) (Icc lower 1) from contDiffOn_const)
      (reservedConjugatedRadialSystemOperator_smooth parameters length compact lower state positive
        (lowerHalf.trans_lt (by norm_num)) grade reserve order rowsSmooth))

theorem fullReservedWeightedSystemOperator_same (grade reserve : ℕ)
    (enough : 5 ≤ reserve + 2) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode
      (fullReservedWeightedSystemOperator parameters length compact lower positive lowerHalf state grade reserve radius
        (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small core (grade + 2 + reserve) radius) +
        fullWeightedSystemSource parameters length compact lower positive lowerHalf lengthPositive state core grade radius) =
      annularPhaseSlope parameters mode.2 radius •
        hilbertPairCoefficient mode
          (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
            widthHalf widthLength state small core grade radius) +
        hilbertPairCoefficient mode
          (conjugatedMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive
            widthHalf widthLength state small core grade radius) := by
  have phaseSame := phaseSlopePair_same parameters (reserve + 2) enough radius
    (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core (grade + 2 + reserve) radius)
    (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade radius)
    (by intro query
        convert conjugatedSmoothResponsePairCurve_shift parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small core grade (reserve + 2) radius inside query using 1
        congr 2
        omega) mode
  have inputSame := conjugatedSmoothResponsePairCurve_reserve parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small core (grade + 2) reserve radius inside
  unfold fullReservedWeightedSystemOperator fullWeightedSystemSource conjugatedMeanFreeSystemRHS
  rw [add_apply, ContinuousLinearMap.comp_apply,
    reservedConjugatedRadialSystemOperator_same, inputSame]
  rw [(hilbertPairCoefficient mode).map_add, (hilbertPairCoefficient mode).map_add, phaseSame,
    (physicalPairMeanFree parameters).map_add, (hilbertPairCoefficient mode).map_add]
  exact add_assoc _ _ _

end Grad.AnnularWeightedSystem
