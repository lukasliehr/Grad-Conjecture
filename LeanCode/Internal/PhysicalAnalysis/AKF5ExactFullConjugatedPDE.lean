import AKF4ExactConjugatedHomogeneousRHS
import AKD8SameConjugatedFullSourceRHS

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
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

theorem conjugatedRadialSystemSource_physical (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      hilbertPairCoefficient mode
        (conjugatedRadialSystemSource parameters length compact lower positive
          (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade radius) =
        (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          hilbertPairCoefficient mode
            (originalRadialSystemSource parameters length compact lower positive
              (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade radius) := by
  filter_upwards [conjugatedRadialSystemSource_actual parameters length compact lower positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade,
    originalRadialSystemSource_actual parameters length compact lower positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade] with radius weighted physical
  intro mode
  have scaled := congrArg (fun value : ComplexEuclidean 1 × ComplexEuclidean 1 =>
    (Real.exp (radialPhase parameters radius mode.2) : ℂ) • value) (physical mode)
  exact (weighted mode).trans ((smul_comm _ _ _).trans scaled.symm)

/-- The full actual weighted system, restricted to both original nonzero
angular components. Independent sources, P and positive Rg remain present. -/
def conjugatedMeanFreeSystemRHS (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  physicalPairMeanFree parameters
    (conjugatedRadialSystemOperator parameters length compact lower state positive
      (lowerHalf.trans_lt (by norm_num)) grade radius
      (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core (grade + 2) radius) +
      conjugatedRadialSystemSource parameters length compact lower positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade radius)

theorem conjugatedMeanFreeSystemRHS_physical (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      hilbertPairCoefficient mode
        (conjugatedMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small core grade radius) =
        (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          hilbertPairCoefficient mode
            (originalMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive
              widthHalf widthLength state small core grade radius) := by
  filter_upwards [conjugatedRadialSystemOperator_physical parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade,
    conjugatedRadialSystemSource_physical parameters length compact lower positive lowerHalf lengthPositive state core grade]
    with radius unknown source
  intro mode
  unfold conjugatedMeanFreeSystemRHS originalMeanFreeSystemRHS originalSmoothResponseSystemRHS
  rw [physicalPairMeanFree_coefficient, physicalPairMeanFree_coefficient,
    (hilbertPairCoefficient mode).map_add, (hilbertPairCoefficient mode).map_add,
    unknown mode, source mode, ← smul_add]
  exact smul_comm _ _ _

/-- Once continuity of the actual conjugated operator/source is available,
the AE physical identity gives the genuine derivative at both endpoints too. -/
theorem conjugatedCoordinateDerivative_of_continuousRHS (grade : ℕ)
    (rhsContinuous : ContinuousOn
      (conjugatedMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade) (Icc lower 1))
    (mode : ℤ × ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (fun point => hilbertPairCoefficient mode
        (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small core grade point))
      (annularPhaseSlope parameters mode.2 radius • hilbertPairCoefficient mode
        (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small core grade radius) +
        hilbertPairCoefficient mode
          (conjugatedMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive
            widthHalf widthLength state small core grade radius)) (Icc lower 1) radius := by
  have phaseContinuous : ContinuousOn (fun point => Real.exp (radialPhase parameters point mode.2)) (Icc lower 1) :=
    (Real.continuous_exp.comp (radialPhase_smooth parameters mode.2).continuous).continuousOn
  have same := collarCurve_eq_of_ae lower (lowerHalf.trans_lt (by norm_num))
    (fun point => hilbertPairCoefficient mode
      (conjugatedMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade point))
    (fun point => Real.exp (radialPhase parameters point mode.2) • hilbertPairCoefficient mode
      (originalMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade point))
    ((hilbertPairCoefficient mode).continuous.comp_continuousOn rhsContinuous)
    (phaseContinuous.smul ((hilbertPairCoefficient mode).continuous.comp_continuousOn
      (originalMeanFreeSystemRHS_continuousOn parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade)))
    (by filter_upwards [conjugatedMeanFreeSystemRHS_physical parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small core grade] with point actual
        exact actual mode)
  have sameAt := same inside
  dsimp only at sameAt
  rw [sameAt, conjugatedSmoothResponsePairCurve_physical parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small core grade mode radius inside, smul_comm (annularPhaseSlope parameters mode.2 radius), ← smul_add]
  exact conjugatedSmoothResponsePairCurve_coordinateDerivative parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small core grade mode radius inside

end Grad.AnnularWeightedSystem
