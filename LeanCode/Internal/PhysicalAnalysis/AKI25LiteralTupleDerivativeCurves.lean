import AKI24GenuineLowStoredConverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularSourceGraph Grad.AnnularSmoothCore Grad.AnnularReconstruction
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.AnnularLowEnergy Grad.AnnularLowClassical Grad.AnnularHighRadial

/-- Continuous extension of a genuinely closed-collar continuous function. -/
def originalClosedCurve (lower : ℝ) (bounded : lower ≤ 1) (value : ℝ → ComplexEuclidean 1)
    (continuous : ContinuousOn value (Icc lower 1)) : C(ℝ, ComplexEuclidean 1) :=
  radialSectionExtension 1 lower bounded ⟨fun radius => value radius.val, continuousOn_iff_continuous_domRestrict.mp continuous⟩

theorem originalClosedCurve_same (lower : ℝ) (bounded : lower ≤ 1) (value : ℝ → ComplexEuclidean 1)
    (continuous : ContinuousOn value (Icc lower 1)) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    originalClosedCurve lower bounded value continuous radius = value radius := by
  change value (radialClamp lower bounded radius).val = _
  rw [radialClamp_eq lower bounded radius inside]

variable (parameters : PhaseParameters) (lower : ℝ) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower)

/-- The original tuple has actual smooth scalar Fourier coefficients. -/
theorem originalTuple_coefficient_smooth (slot : Fin 4) (mode : ℤ × ℤ) :
    ContDiffOn ℝ ∞ (fun radius => originalPhysicalCoefficient (tuple.val slot) radius mode) (Icc lower 1) :=
  (tuple.property.1 slot).2.coefficient_smooth mode

/-- This is the computed radial derivative, continuously extended from the
same closed collar. It is not an independently supplied source slope. -/
def originalTupleSlopeCurve (slot : Fin 4) (mode : ℤ × ℤ) : C(ℝ, ComplexEuclidean 1) :=
  originalClosedCurve lower bounded.le
    (derivWithin (fun radius => originalPhysicalCoefficient (tuple.val slot) radius mode) (Icc lower 1))
    ((originalTuple_coefficient_smooth parameters lower tuple slot mode).continuousOn_derivWithin
      (uniqueDiffOn_Icc bounded) (by simp))

theorem originalTupleSlopeCurve_same (slot : Fin 4) (mode : ℤ × ℤ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    originalTupleSlopeCurve parameters lower bounded tuple slot mode radius =
      derivWithin (fun location => originalPhysicalCoefficient (tuple.val slot) location mode) (Icc lower 1) radius :=
  originalClosedCurve_same lower bounded.le _ _ radius inside

theorem originalTuple_coefficient_derivative (slot : Fin 4) (mode : ℤ × ℤ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (fun location => originalPhysicalCoefficient (tuple.val slot) location mode)
      (originalTupleSlopeCurve parameters lower bounded tuple slot mode radius) (Icc lower 1) radius := by
  rw [originalTupleSlopeCurve_same parameters lower bounded tuple slot mode radius inside]
  exact ((originalTuple_coefficient_smooth parameters lower tuple slot mode).differentiableOn (by simp) radius inside).hasDerivWithinAt

variable (length compact : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive)
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple
      (originalFiveBlockObservation parameters lower length positive (data,candidate)))

private abbrev derivativeCandidate := originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive candidate

/-- The same tuple's two actual low physical derivative curves. -/
def originalTupleLowSlope (index : LowAnnularIndex) : C(ℝ, ComplexEuclidean 1) :=
  if index.1 = 0 then originalTupleSlopeCurve parameters lower bounded tuple 1 index.2.val
  else frequencyNumerator (some false) index.2.val • originalTupleSlopeCurve parameters lower bounded tuple 0 index.2.val

include represented

theorem OriginalTupleObservation.lowSection (index : LowAnnularIndex) (radius : Icc lower (1 : ℝ)) :
    lowPhysicalSection parameters lower length positive bounded
      (derivativeCandidate parameters lower bounded length positive lengthPositive candidate).ofLp.2 index radius =
      if index.1 = 0 then originalPhysicalCoefficient (tuple.val 1) radius.val index.2.val
      else frequencyNumerator (some false) index.2.val • originalPhysicalCoefficient (tuple.val 0) radius.val index.2.val := by
  have notHigh : ¬ 3 ≤ |index.2.val.1| := by have small := index.2.property; omega
  rcases index with ⟨entry,mode⟩
  fin_cases entry
  · change lowPhysicalSection parameters lower length positive bounded
      (derivativeCandidate parameters lower bounded length positive lengthPositive candidate).ofLp.2 (0,mode) radius = _
    change _ = originalPhysicalCoefficient (tuple.val 1) radius.val mode.val
    have same : originalPhysicalCoefficient (tuple.val 1) radius.val mode.val =
        sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive
          (derivativeCandidate parameters lower bounded length positive lengthPositive candidate) 0 radius mode.val :=
      represented.scalar radius mode.val
    simpa only [sameCoupledXiCoefficient,dif_neg notHigh,dif_pos mode.property,pow_zero,Complex.ofReal_one,one_smul,if_pos rfl] using same.symm
  · change lowPhysicalSection parameters lower length positive bounded
      (derivativeCandidate parameters lower bounded length positive lengthPositive candidate).ofLp.2 (1,mode) radius = _
    change _ = frequencyNumerator (some false) mode.val • originalPhysicalCoefficient (tuple.val 0) radius.val mode.val
    have same := represented.pressure_R parameters length compact lower positive bounded lengthPositive state data candidate tuple radius mode.val
    simpa only [sameCoupledXCoefficient,dif_neg notHigh,dif_pos mode.property,pow_zero,Complex.ofReal_one,one_smul,show (1 : Fin 2) ≠ 0 by decide,if_false] using same.symm

/-- Genuine arbitrary represented low-coordinate derivatives, before any
weak PDE or inverse statement is inferred. -/
theorem OriginalTupleObservation.low_derivative (index : LowAnnularIndex)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
      (lowPhysicalSection parameters lower length positive bounded
        (derivativeCandidate parameters lower bounded length positive lengthPositive candidate).ofLp.2 index))
      (originalTupleLowSlope parameters lower bounded tuple index radius) (Icc lower 1) radius := by
  have same (location : ℝ) (member : location ∈ Icc lower 1) :=
    (lowSectionExtension_eval lower bounded.le _ location member).trans
      (represented.lowSection parameters lower bounded tuple length compact positive lengthPositive state data candidate index ⟨location,member⟩)
  by_cases entry : index.1 = 0
  · rw [originalTupleLowSlope,if_pos entry]
    simp only [entry,if_true] at same
    exact (originalTuple_coefficient_derivative parameters lower bounded tuple 1 index.2.val radius inside).congr same (same radius inside)
  · rw [originalTupleLowSlope,if_neg entry]
    simp only [entry,if_false] at same
    have differentiated := (originalTuple_coefficient_derivative parameters lower bounded tuple 0 index.2.val radius inside).const_smul
      (frequencyNumerator (some false) index.2.val)
    exact differentiated.congr same (same radius inside)

end Grad.AnnularOriginalSmoothCore
