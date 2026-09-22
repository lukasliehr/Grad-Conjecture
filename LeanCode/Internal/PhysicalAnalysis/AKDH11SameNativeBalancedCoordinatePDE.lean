import AKDH10LiteralConjugatedEulerKernel
import AKV16GeneralActualSourceRadialBootstrap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalCartesianTameEstimate

section Normalization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact SR14 change of variables, applied to the actual derivative. -/
theorem balancedCoordinate_hasDerivWithinAt (domain : Set ℝ) (radius slope : ℝ) (nonzero : radius ≠ 0)
    (first second : ℝ → E) (firstRHS secondRHS : E)
    (firstDerivative : HasDerivWithinAt first (slope • first radius+firstRHS) domain radius)
    (secondDerivative : HasDerivWithinAt second (slope • second radius+secondRHS) domain radius) :
    HasDerivWithinAt (fun point => (point⁻¹ • first point,second point))
      (radius⁻¹ • (((radius*slope-1) • (radius⁻¹ • first radius)+firstRHS),
        (radius*slope) • second radius+radius • secondRHS)) domain radius := by
  have inverse := ((hasDerivAt_id radius).inv nonzero).hasDerivWithinAt (s := domain)
  have result := (inverse.smul firstDerivative).prodMk secondDerivative
  apply result.congr_deriv
  apply Prod.ext
  · change radius⁻¹ • (slope • first radius+firstRHS)+(-1 / radius^2) • first radius =
      radius⁻¹ • ((radius*slope-1) • (radius⁻¹ • first radius)+firstRHS)
    rw [neg_div,add_comm]
    simp only [smul_add,smul_smul]
    have scalar : -(1/radius^2)+radius⁻¹*slope = radius⁻¹*((radius*slope-1)*radius⁻¹) := by field_simp; ring
    rw [← add_assoc,← add_smul,scalar]
  · change slope • second radius+secondRHS = radius⁻¹ • ((radius*slope) • second radius+radius • secondRHS)
    rw [smul_add,smul_smul,smul_smul,← mul_assoc,inv_mul_cancel₀ nonzero,one_mul,one_smul]

end Normalization

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularGeneralSourceRegularity Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

def balancedOriginalPairCurve (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  (radius⁻¹ • (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius).2,
    (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius).1)

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted)

local notation "response" => sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
local notation "bounded" => lowerHalf.trans_lt (by norm_num : (1:ℝ)/2<1)
local notation "balanced" => balancedOriginalPairCurve parameters lower length positive bounded lengthPositive response
local notation "rhs" => generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data response curves

include allGrades

/-- The SAME full-cell native solution satisfies the balanced radial
coordinate equation. Source and homogeneous terms still refer to the
already proved original RHS, without a replacement equation premise. -/
theorem sameNativeBalanced_coordinateDerivative (grade : ℕ) (mode : ℤ × ℤ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (fun point => hilbertPairCoefficient mode (balanced grade point))
      (radius⁻¹ •
        (((radius*Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius-1) •
            (balanced grade radius).1 mode+(rhs (grade+1) radius).2 mode),
          (radius*Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius) •
            (balanced grade radius).2 mode+radius • (rhs grade radius).1 mode)) (Icc lower 1) radius := by
  have first := (generalShared_weighted_derivative parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small data curves allGrades (grade+1) mode radius inside).snd
  have second := (generalShared_weighted_derivative parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small data curves allGrades grade mode radius inside).fst
  exact balancedCoordinate_hasDerivWithinAt (Icc lower 1) radius (Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius)
    (positive.trans_le inside.1).ne' _ _ _ _ first second

end Grad.OriginalCartesianTameEstimate
