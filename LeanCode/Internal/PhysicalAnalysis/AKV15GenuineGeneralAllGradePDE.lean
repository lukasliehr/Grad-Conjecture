import AKV14GenuineGeneralWeightedBasePDE

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularGeneralSourceRegularity
open Grad.AnnularVariational
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularHighRadial Grad.CircularHighRegularity Grad.AnnularLowClassical Grad.AnnularLowEnergy

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)


variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
  CoupledInsertedGrade lower length positive lengthPositive grade (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted)
include allGrades curves



theorem generalShared_weightedRHS_grade (grade : ℕ) (mode : ℤ × ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    hilbertPairCoefficient mode ((generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves) grade radius) =
      (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade • hilbertPairCoefficient mode ((generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves) 0 radius) := by
  have continuous (level : ℕ) := (hilbertPairCoefficient mode).continuous.comp_continuousOn
    (generalConjugatedSystemRHS_continuous parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades level)
  apply collarCurve_eq_of_ae lower (lowerHalf.trans_lt (by norm_num))
    (fun point => hilbertPairCoefficient mode ((generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves) grade point))
    (fun point => (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade • hilbertPairCoefficient mode ((generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves) 0 point))
    (continuous grade) ((continuous 0).const_smul ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade)) ?_ inside
  filter_upwards [generalConjugatedSystemRHS_actual parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades grade,
    generalConjugatedSystemRHS_actual parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades 0]
    with point high low
  rw [high mode,low mode]
  simp only [pow_zero,Complex.ofReal_one,one_smul,Complex.ofReal_pow]
  exact smul_comm (if mode.1 = 0 then (0 : ℂ) else 1) ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade) _

/-- Genuine all-grade coordinate PDE for the same actual source (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data). -/
theorem generalShared_weighted_derivative (grade : ℕ) (mode : ℤ × ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (fun point => hilbertPairCoefficient mode ((conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) grade point))
      (Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius • hilbertPairCoefficient mode ((conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) grade radius) +
        hilbertPairCoefficient mode ((generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves) grade radius)) (Icc lower 1) radius := by
  have same := conjugatedOriginalPairCurve_grade parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) allGrades grade
  rw [same radius inside mode,
    generalShared_weightedRHS_grade parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades grade mode radius inside]
  rw [smul_comm (Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius)
    ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade), ← smul_add]
  exact ((generalShared_weighted_baseDerivative parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades mode radius inside).const_smul
    ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade)).congr
    (fun point member => same point member mode) (same radius inside mode)

end Grad.AnnularGeneralSourceRegularity
