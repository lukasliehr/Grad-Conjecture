import AKR15ExactOriginalRetainedHighFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (lengthPositive : 0 < length)

theorem tupleWeightedRetained_AJSection (index : LowAnnularIndex) :
    originalLowAJSection parameters lower length positive bounded
      (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive).ofLp.2 index =
      tupleAJCoefficient parameters lower length index.1 0 index.2 •
        tupleConjugatedJetSection parameters lower bounded tuple (if index.1 = 0 then 1 else 0) 0 index.2.val := by
  apply radialSectionL2_faithful lower positive bounded
  rw [originalLowBF6_section_bulk]
  change ((originalLowGraphEquivalence parameters lower length positive lengthPositive bounded.le).symm
    (originalLowGraphEquivalence parameters lower length positive lengthPositive bounded.le
      (tupleOriginalAJ parameters lower length positive bounded tuple))).val 0 index = _
  rw [(originalLowGraphEquivalence parameters lower length positive lengthPositive bounded.le).symm_apply_apply]
  change tupleAJCoordinate parameters lower length positive bounded tuple 0 index = _
  rw [tupleAJCoordinate_apply,radialSectionL2_complex_smul]
  rfl

theorem tupleWeightedRetained_lowXi (mode : LowAnnularMode) (radius : Icc lower (1 : ℝ)) :
    lowPhysicalSection parameters lower length positive bounded
      (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive).ofLp.2 (0,mode) radius =
      originalPhysicalCoefficient (tuple.val 1) radius.val mode.val := by
  have same := congrArg (fun sectionValue : RadialContinuousSection 1 lower => sectionValue radius)
    (tupleWeightedRetained_AJSection parameters lower length positive bounded tuple lengthPositive (0,mode))
  rw [originalLowAJSection_physical] at same
  change (Real.exp (radialPhase parameters radius.val mode.val.2) *
    (originalLowScale parameters lower length mode * cellFrequency mode.val.2)) •
      lowPhysicalSection parameters lower length positive bounded
        (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive).ofLp.2 (0,mode) radius =
      ((originalLowScale parameters lower length mode * cellFrequency mode.val.2 : ℝ) : ℂ) •
        tupleConjugatedJetSection parameters lower bounded tuple 1 0 mode.val radius at same
  rw [tupleConjugatedJetSection_value] at same
  have nonzero : ((Real.exp (radialPhase parameters radius.val mode.val.2) *
      (originalLowScale parameters lower length mode * cellFrequency mode.val.2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos (Real.exp_pos _) (mul_pos
      (originalLowScale_positive parameters lower length positive lengthPositive mode) (cellFrequency_pos _))).ne'
  apply smul_right_injective (ComplexEuclidean 1) nonzero
  change ((Real.exp (radialPhase parameters radius.val mode.val.2) *
    (originalLowScale parameters lower length mode * cellFrequency mode.val.2) : ℝ) : ℂ) •
      lowPhysicalSection parameters lower length positive bounded
        (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive).ofLp.2 (0,mode) radius = _ at same
  exact same.trans (by
    rw [smul_smul,← Complex.ofReal_mul,mul_comm (originalLowScale parameters lower length mode * cellFrequency mode.val.2)])

theorem tupleWeightedRetained_lowX (mode : LowAnnularMode) (radius : Icc lower (1 : ℝ)) :
    lowPhysicalSection parameters lower length positive bounded
      (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive).ofLp.2 (1,mode) radius =
      (Complex.I * (mode.val.1 : ℂ)) • originalPhysicalCoefficient (tuple.val 0) radius.val mode.val := by
  have same := congrArg (fun sectionValue : RadialContinuousSection 1 lower => sectionValue radius)
    (tupleWeightedRetained_AJSection parameters lower length positive bounded tuple lengthPositive (1,mode))
  rw [originalLowAJSection_physical] at same
  change (Real.exp (radialPhase parameters radius.val mode.val.2) * 1) •
      lowPhysicalSection parameters lower length positive bounded
        (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive).ofLp.2 (1,mode) radius =
      (Complex.I * (mode.val.1 : ℂ)) • tupleConjugatedJetSection parameters lower bounded tuple 0 0 mode.val radius at same
  rw [mul_one,tupleConjugatedJetSection_value] at same
  apply smul_right_injective (ComplexEuclidean 1)
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos (radialPhase parameters radius.val mode.val.2)).ne')
  change (Real.exp (radialPhase parameters radius.val mode.val.2) : ℂ) •
      lowPhysicalSection parameters lower length positive bounded
        (tupleWeightedRetained parameters lower length positive bounded tuple lengthPositive).ofLp.2 (1,mode) radius = _ at same
  exact same.trans (smul_comm _ _ _)

end Grad.AnnularOriginalCoreRealization
