import AKV10GeneralLowRawRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)

/-- Continuous representative of the original unweighted RHS, obtained by
undoing the original phase on the actual weighted RHS at the same radius. -/
def generalPhysicalRHSCurve (mode : ℤ × ℤ) : C(ℝ, ComplexEuclidean 1 × ComplexEuclidean 1) where
  toFun radius :=
    Real.exp (-radialPhase parameters (radialClamp lower (lowerHalf.trans (by norm_num)) radius).val mode.2) •
      hilbertPairCoefficient mode
        (generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data field curves 0
          (radialClamp lower (lowerHalf.trans (by norm_num)) radius).val)
  continuous_toFun := by
    have clamp := continuous_clampedCurve lower (lowerHalf.trans (by norm_num)) _
      (generalConjugatedSystemRHS_continuous parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades 0)
    have phase := continuous_clampedCurve lower (lowerHalf.trans (by norm_num))
      (fun radius => Real.exp (-radialPhase parameters radius mode.2))
      (Real.continuous_exp.comp (Grad.AnnularSourceGraph.radialPhase_smooth parameters mode.2).continuous.neg).continuousOn
    exact phase.smul ((hilbertPairCoefficient mode).continuous.comp clamp)

theorem generalPhysicalRHSCurve_same (mode : ℤ × ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades mode radius =
      Real.exp (-radialPhase parameters radius mode.2) • hilbertPairCoefficient mode
        (generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data field curves 0 radius) := by
  simp only [generalPhysicalRHSCurve, ContinuousMap.coe_mk,
    radialClamp_eq lower (lowerHalf.trans (by norm_num)) radius inside]

theorem generalPhysicalRHSCurve_actual (mode : ℤ × ℤ) :
    generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades mode
      =ᵐ[volume.restrict (Icc lower 1)] fun radius =>
        (if mode.1 = 0 then (0 : ℂ) else 1) •
          generalOriginalFullRHS parameters length compact lower positive lowerHalf lengthPositive state data field radius mode := by
  filter_upwards [generalConjugatedSystemRHS_actual parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades 0,
    ae_restrict_mem measurableSet_Icc] with radius same inside
  rw [generalPhysicalRHSCurve_same parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades mode radius inside,
    same mode]
  simp only [pow_zero,Complex.ofReal_one,one_smul]
  rw [smul_comm (Real.exp (-radialPhase parameters radius mode.2))]
  congr 1
  change (Real.exp (-radialPhase parameters radius mode.2) : ℂ) •
    ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
      generalOriginalFullRHS parameters length compact lower positive lowerHalf lengthPositive state data field radius mode) =
      generalOriginalFullRHS parameters length compact lower positive lowerHalf lengthPositive state data field radius mode
  rw [Real.exp_neg,Complex.ofReal_inv,inv_smul_smul₀
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]

end Grad.AnnularGeneralSourceRegularity
