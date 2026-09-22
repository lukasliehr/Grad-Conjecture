import AKI13OriginalFluxResidualAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
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

/-- The computed AH24 pressure residual uses the SAME covariant, b3 and
Vb and equals the original independent source after its literal P. -/
theorem sameResponseOriginalTuple_G3_projected :
    ∀ᵐ location ∂volume.restrict (Icc lower 1), ∀ inside : location ∈ Icc lower 1, ∀ mode,
      originalTupleG3 parameters length compact lower positive state
        (sameResponseOriginalTuple parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small core weightedSmooth) ⟨location, inside⟩ mode =
        (if mode.1 = 0 then (0 : ℂ) else 1) • actualOriginalIndependentG parameters length lower positive
          (lowerHalf.trans_lt (by norm_num)) lengthPositive core location mode := by
  let tuple := sameResponseOriginalTuple parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small core weightedSmooth
  filter_upwards [sameResponseOriginalTuple_rows parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core weightedSmooth 1,
    sameResponseOriginalTuple_rows parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core weightedSmooth 2,
    originalSmoothSourceRHS_actual parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core 0,
    actualOriginalFullRHS_fullRows parameters length compact lower positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive state (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core) core] with location rowC rowV rhs full
  intro inside mode
  have sameC := (rowC inside mode).symm.trans
    (tuplePhysicalRowTrace_c_coefficient parameters length compact lower positive state tuple ⟨location, inside⟩ mode)
  have sameV := (rowV inside mode).symm.trans
    (tuplePhysicalRowTrace_rV_coefficient parameters length compact lower positive state tuple ⟨location, inside⟩ mode)
  have sameRHS : (hilbertPairCoefficient mode (originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0 location)).1 =
      (actualOriginalFullRHS parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
        (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
        core location mode).1 := by
    exact (congrArg Prod.fst (rhs mode)).trans (by simp only [pow_zero, Complex.ofReal_one, one_smul])
  have sameP := originalSmoothResponsePhysicalP_raw_coefficient parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core ⟨location, inside⟩ mode
  change originalPhysicalCoefficient
    (originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    location mode = _ at sameP
  unfold originalTupleG3
  change derivWithin (fun point => originalPhysicalCoefficient
    (originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      point mode) (Icc lower 1) location + (location : ℂ)⁻¹ • originalPhysicalCoefficient
    (originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      location mode + _ + _ = _
  rw [originalPhysicalP_derivWithin parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core
    location inside mode, sameRHS, full mode, sameP]
  change angularInverseMultiplier mode • ((if mode.1 = 0 then (0 : ℂ) else 1) •
    ((-((location : ℂ)⁻¹)) • _ - (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode •
      lowRhoPhysicalCoefficient _ _ _ _ location mode) - (location : ℂ)⁻¹ • (frequencyNumerator (some false) mode •
      lowRhoPhysicalCoefficient _ _ _ _ location mode) + _)) + _ + _ + _ = _
  rw [sameC, sameV, radialClamp_eq lower (lowerHalf.trans (by norm_num)) location inside]
  exact originalFluxResidual_algebra length location lengthPositive.ne' (positive.trans_le inside.1).ne' mode _ _ _ _
    (tupleVTrace_fixed parameters length compact lower positive state tuple ⟨location, inside⟩ mode)

end Grad.AnnularOriginalSmoothCore
