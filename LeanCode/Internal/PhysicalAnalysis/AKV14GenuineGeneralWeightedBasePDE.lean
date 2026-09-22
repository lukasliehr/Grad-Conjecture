import AKV13GenuineGeneralSharedDerivatives

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

private theorem pairCoefficient_literal (mode : ℤ × ℤ) (value : PhysicalHilbertPair) :
    hilbertPairCoefficient mode value = (value.1 mode,value.2 mode) := rfl

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


theorem generalShared_physical_derivative (mode : ℤ × ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (fun point => hilbertPairCoefficient mode ((originalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) 0 point))
      ((generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) mode radius) (Icc lower 1) radius := by
  by_cases zero : mode.1 = 0
  · have modeSame : mode = (0,mode.2) := Prod.ext zero rfl
    rw [modeSame]
    have rhsZero : (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades) (0,mode.2) radius = 0 := by
      simp only [generalPhysicalRHSCurve,ContinuousMap.coe_mk,generalConjugatedSystemRHS,
        physicalPairMeanFree_coefficient_zero,smul_zero]
    rw [rhsZero]
    exact (hasDerivWithinAt_const radius (Icc lower 1) (0 : ComplexEuclidean 1 × ComplexEuclidean 1)).congr
      (fun point _ => originalPairCurve_meanZero parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) allGrades _ point)
      (originalPairCurve_meanZero parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) allGrades _ radius)
  · by_cases large : 3 ≤ |mode.1|
    · exact generalShared_high_derivative parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades ⟨mode,large⟩ radius inside
    · have low : |mode.1| = 1 ∨ |mode.1| = 2 := by
        have pos := abs_pos.mpr zero
        omega
      have dx := generalShared_low_derivative parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades (1,⟨mode,low⟩) radius inside
      have dxi := generalShared_low_derivative parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades (0,⟨mode,low⟩) radius inside
      simp only [pairCoefficient_literal]
      simpa only [lowPhysicalPairCoefficient,Prod.fst,Prod.snd,show (1 : Fin 2) ≠ 0 by decide,
        if_false,if_true,Prod.mk.eta] using dx.prodMk dxi


theorem generalShared_weighted_baseDerivative (mode : ℤ × ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (fun point => hilbertPairCoefficient mode ((conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) 0 point))
      (Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius • hilbertPairCoefficient mode ((conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) 0 radius) +
        hilbertPairCoefficient mode ((generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves) 0 radius)) (Icc lower 1) radius := by
  have physical := generalShared_physical_derivative parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades mode radius inside
  have phase := (Grad.AnnularVariational.radialPhase_hasDerivAt parameters mode.2 radius).exp.hasDerivWithinAt (s := Icc lower 1)
  have product := phase.smul physical
  have equality := conjugatedOriginalPairCurve_physical parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) allGrades 0
  have same := product.congr (fun point member => equality point member mode) (equality radius inside mode)
  rw [generalPhysicalRHSCurve_same parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades mode radius inside] at same
  rw [equality radius inside mode]
  have cancel : Real.exp (radialPhase parameters radius mode.2) * Real.exp (-radialPhase parameters radius mode.2) = 1 := by
    rw [Real.exp_neg,mul_inv_cancel₀ (Real.exp_pos _).ne']
  simpa only [smul_add,smul_smul,Function.comp_apply,mul_comm,add_comm,cancel,one_smul] using same

end Grad.AnnularGeneralSourceRegularity
