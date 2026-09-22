import AKDH17ActualPhysicalOperatorEuler
import AKCI6ActualBalancedSystemOneOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularStrongOrbit Grad.AnnularSourceGraph Grad.AnnularCoupledInverse
open Grad.AnnularHighGenerators Grad.PhaseAlgebra
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.GaugeCoefficients.Physical.Allocation

theorem physicalPair_hasDerivWithinAt_of_coefficients (domain : Set ℝ) (radius : ℝ)
    (unique : UniqueDiffWithinAt ℝ domain radius) (curve : ℝ → PhysicalHilbertPair) (slope : PhysicalHilbertPair)
    (differentiable : DifferentiableWithinAt ℝ curve domain radius)
    (coefficients : ∀ mode : ℤ × ℤ, HasDerivWithinAt (fun point => hilbertPairCoefficient mode (curve point))
      (hilbertPairCoefficient mode slope) domain radius) :
    HasDerivWithinAt curve slope domain radius := by
  have derivative := differentiable.hasDerivWithinAt
  apply derivative.congr_deriv
  apply Prod.ext
  · apply lp.ext
    funext mode
    have observed := ((hilbertPairCoefficient mode).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt radius derivative
    have typed : HasDerivWithinAt (fun point => hilbertPairCoefficient mode (curve point))
        (hilbertPairCoefficient mode (derivWithin curve domain radius)) domain radius := by
      simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars'] using observed
    exact congrArg Prod.fst ((typed.derivWithin unique).symm.trans ((coefficients mode).derivWithin unique))
  · apply lp.ext
    funext mode
    have observed := ((hilbertPairCoefficient mode).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt radius derivative
    have typed : HasDerivWithinAt (fun point => hilbertPairCoefficient mode (curve point))
        (hilbertPairCoefficient mode (derivWithin curve domain radius)) domain radius := by
      simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars'] using observed
    exact congrArg Prod.snd ((typed.derivWithin unique).symm.trans ((coefficients mode).derivWithin unique))

/-- The balanced packet retains exact original nu-grade relations. -/
theorem balancedOriginalPairCurve_shift (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (grade reserve : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode (balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+reserve) radius) =
      (annularFrequency mode.1 mode.2 : ℂ)^reserve •
        hilbertPairCoefficient mode (balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius) := by
  have first := congrArg Prod.snd (conjugatedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive field allGrades
    (grade+1) reserve radius inside mode)
  have second := congrArg Prod.fst (conjugatedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive field allGrades
    grade reserve radius inside mode)
  change (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1+reserve) radius).2 mode =
    (annularFrequency mode.1 mode.2 : ℂ)^reserve •
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius).2 mode at first
  apply Prod.ext
  · change radius⁻¹ • (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+reserve+1) radius).2 mode =
      (annularFrequency mode.1 mode.2 : ℂ)^reserve •
        (radius⁻¹ • (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius).2 mode)
    rw [show grade+reserve+1=grade+1+reserve by omega,first]
    exact smul_comm _ _ _
  · exact second

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

include allGrades curves

theorem sameNativeBalanced_smooth (grade : ℕ) : ContDiffOn ℝ ∞ (balanced grade) (Icc lower 1) := by
  have regular := generalShared_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small data curves allGrades
  have inverse : ContDiffOn ℝ ∞ (fun point : ℝ => point⁻¹) (Icc lower 1) :=
    contDiffOn_id.inv (fun point member => (positive.trans_le member.1).ne')
  exact (inverse.smul (regular (grade+1)).snd).prodMk (regular grade).fst

/-- The actual balanced Hilbert RHS, with its diagonal order paid by the
same next nu grade. The remaining RHS is exactly the accepted native one. -/
def sameNativeBalancedHilbertRHS (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  let point := collarRadius lower positive (bounded).le radius
  (balancedPhaseAction parameters 1 point (balanced (grade+1) radius).1+(rhs (grade+1) radius).2,
    balancedPhaseAction parameters 1 point (balanced (grade+1) radius).2+(balanced grade radius).2+radius • (rhs grade radius).1)

theorem sameNativeBalanced_hilbertDerivative (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (balanced grade)
      (radius⁻¹ • sameNativeBalancedHilbertRHS parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data curves grade radius) (Icc lower 1) radius := by
  apply physicalPair_hasDerivWithinAt_of_coefficients (Icc lower 1) radius (uniqueDiffOn_Icc bounded radius inside) _ _
    ((sameNativeBalanced_smooth parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state small data curves allGrades grade).differentiableOn (by simp) radius inside)
  intro mode
  have derivative := sameNativeBalanced_coordinateDerivative parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small data curves allGrades grade mode radius inside
  apply derivative.congr_deriv
  have same := balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive response allGrades grade 1 radius inside
  have first : ∀ query, (balanced (grade+1) radius).1 query = (annularFrequency query.1 query.2 : ℂ) • (balanced grade radius).1 query := by
    intro query
    have actual := congrArg Prod.fst (same query)
    change (balanced (grade+1) radius).1 query = (annularFrequency query.1 query.2 : ℂ)^1 • (balanced grade radius).1 query at actual
    simpa only [pow_one] using actual
  have second : ∀ query, (balanced (grade+1) radius).2 query = (annularFrequency query.1 query.2 : ℂ) • (balanced grade radius).2 query := by
    intro query
    have actual := congrArg Prod.snd (same query)
    change (balanced (grade+1) radius).2 query = (annularFrequency query.1 query.2 : ℂ)^1 • (balanced grade radius).2 query at actual
    simpa only [pow_one] using actual
  rw [(hilbertPairCoefficient mode).map_smul_of_tower]
  congr 1
  dsimp only [sameNativeBalancedHilbertRHS]
  change _ =
    (balancedPhaseAction parameters 1 (collarRadius lower positive (bounded).le radius) (balanced (grade+1) radius).1 mode+(rhs (grade+1) radius).2 mode,
      balancedPhaseAction parameters 1 (collarRadius lower positive (bounded).le radius) (balanced (grade+1) radius).2 mode+
        (balanced grade radius).2 mode+radius • (rhs grade radius).1 mode)
  rw [balancedPhaseAction_same parameters 1 _ _ _ first mode,balancedPhaseAction_same parameters 1 _ _ _ second mode,
    collarRadius_literal lower positive (bounded).le radius inside]
  apply Prod.ext
  · change (((radius*Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius-1 : ℝ) : ℂ)) • (balanced grade radius).1 mode+_ = _
    rw [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_one]
  · change (((radius*Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius : ℝ) : ℂ)) • (balanced grade radius).2 mode+_ =
      ((radius : ℂ)*(Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius : ℂ)-1) • (balanced grade radius).2 mode+
        (balanced grade radius).2 mode+_
    rw [Complex.ofReal_mul,sub_smul,one_smul,sub_add_cancel]

end Grad.OriginalCartesianTameEstimate
