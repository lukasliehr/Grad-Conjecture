import AKI11ExactFullResidualRHS

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore
open Grad.AnnularStrongOrbit Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularCurrentLow Grad.AnnularKnownLow Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularWeightedSmoothCore Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)
    (weightedSmooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade) (Icc lower 1))

/-- AH24's computed first residual of the SAME four fields equals the
original source, with its literal mean-free multiplier still visible. -/
theorem sameResponseOriginalTuple_F1_projected :
    ∀ᵐ location ∂volume.restrict (Icc lower 1), ∀ inside : location ∈ Icc lower 1, ∀ mode,
      originalTupleF1 parameters length compact lower positive state
        (sameResponseOriginalTuple parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small core weightedSmooth) ⟨location, inside⟩ mode =
        (if mode.1 = 0 then (0 : ℂ) else 1) • actualOriginalIndependentF parameters length lower positive
          (lowerHalf.trans_lt (by norm_num)) lengthPositive core location mode := by
  filter_upwards [sameResponseOriginalTuple_rows parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core weightedSmooth 0,
    originalSmoothSourceRHS_actual parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core 0,
    actualOriginalFullRHS_fullRows parameters length compact lower positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive state (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core) core] with location row rhs full
  intro inside mode
  have sameRow := row inside mode
  rw [tuplePhysicalRowTrace_first] at sameRow
  have sameRHS : (hilbertPairCoefficient mode (originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0 location)).2 =
      (actualOriginalFullRHS parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
        (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
        core location mode).2 := by
    exact (congrArg Prod.snd (rhs mode)).trans (by simp only [pow_zero, Complex.ofReal_one, one_smul])
  unfold originalTupleF1
  change derivWithin (fun point => originalPhysicalCoefficient
    (originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      point mode) (Icc lower 1) location - _ = _
  rw [originalPhysicalXi_derivWithin parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core
    location inside mode, sameRHS, full mode, sameRow]
  change (if mode.1 = 0 then (0 : ℂ) else 1) • ((if mode.1 = 0 then (0 : ℂ) else 1) • (_ + _)) -
    angularMeanFreeMultiplier mode • _ = _
  by_cases zero : mode.1 = 0 <;> simp [angularMeanFreeMultiplier, zero, actualOriginalFullRow]

end Grad.AnnularOriginalSmoothCore
