import AKDN5ActualProjectedBalancedEquation
import AKCK11LiteralKnownRowConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularWeightedSystem Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.GaugeCoefficients.Physical.Allocation

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
local notation "pair" => conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive response
local notation "unknownRow" => balancedUnknownPhysicalRow parameters length compact lower positive bounded lengthPositive state response
local notation "knownRow" => generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves
local notation "rhs" => generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data response curves

include allGrades

/-- The SAME native Hilbert RHS is the actual previously estimated balanced
homogeneous/source operator, retaining its original outer mean-free projection. -/
theorem sameNativeBalancedHilbertRHS_actual (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    sameNativeBalancedHilbertRHS parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves grade radius =
      physicalPairMeanFree parameters
        (balancedHomogeneousSystem parameters length compact state grade
          (collarRadius lower positive (bounded).le radius) (balanced (grade+1) radius)+
         balancedActualSource parameters length compact lower positive bounded state data curves grade
          (collarRadius lower positive (bounded).le radius)) := by
  have coefficients (mode : ℤ × ℤ) :
      hilbertPairCoefficient mode (sameNativeBalancedHilbertRHS parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data curves grade radius) =
      hilbertPairCoefficient mode (physicalPairMeanFree parameters
        (balancedHomogeneousSystem parameters length compact state grade
          (collarRadius lower positive (bounded).le radius) (balanced (grade+1) radius)+
         balancedActualSource parameters length compact lower positive bounded state data curves grade
          (collarRadius lower positive (bounded).le radius))) := by
    have same (query : ℤ × ℤ) : hilbertPairCoefficient query (balanced (grade+1) radius) =
        (annularFrequency query.1 query.2 : ℂ) • hilbertPairCoefficient query (balanced grade radius) := by
      simpa only [pow_one] using balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive
        response allGrades grade 1 radius inside query
    rw [sameNativeBalancedHilbertRHS_coefficient parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades grade radius inside mode,
      physicalPairMeanFree_coefficient,(hilbertPairCoefficient mode).map_add,
      balancedHomogeneousSystem_coefficient parameters length compact state grade _ _ _ same mode,
      balancedActualSource_sameKnownCurves parameters length compact lower positive bounded state data curves grade radius inside,
      balancedFluxOutput_actual]
    dsimp only
    rw [collarRadius_literal lower positive (bounded).le radius inside]
    change _ = (if mode.1=0 then (0 : ℂ) else 1) •
      ((((radius : ℂ)*(Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius : ℂ)-1) • (balanced grade radius).1 mode+
          (if mode.1=0 then (0 : ℂ) else 1) • unknownRow 0 grade radius mode,
        ((radius : ℂ)*(Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius : ℂ)-1) • (balanced grade radius).2 mode-
          ((radius : ℂ)*(length : ℂ)⁻¹) • (frequencyRatioSymbol (some true) mode • unknownRow 1 grade radius mode)-
          frequencyRatioSymbol (some false) mode • unknownRow 2 grade radius mode)+
       ((if mode.1=0 then (0 : ℂ) else 1) • knownRow 0 (grade+1) radius mode+
          (if mode.1=0 then (0 : ℂ) else 1) • curves.force (grade+1) radius mode,
        -((radius : ℂ)*(length : ℂ)⁻¹) • (frequencyRatioSymbol (some true) mode • knownRow 1 (grade+1) radius mode)-
          frequencyRatioSymbol (some false) mode • knownRow 2 (grade+1) radius mode+
          frequencyRatioSymbol (some false) mode • curves.third (grade+1) radius mode))
    by_cases zero : mode.1=0
    · simp only [zero,ite_true,zero_smul]
    · simp only [zero,ite_false,one_smul]
      apply Prod.ext <;> apply PiLp.ext <;> intro coordinate
      · simp only [Prod.fst_add,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
        ring
      · simp only [Prod.snd_add,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
        ring
  apply Prod.ext
  · apply lp.ext
    funext mode
    exact congrArg Prod.fst (coefficients mode)
  · apply lp.ext
    funext mode
    exact congrArg Prod.snd (coefficients mode)

theorem sameNativeBalanced_actualDerivative (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (balanced grade)
      (radius⁻¹ • physicalPairMeanFree parameters
        (balancedHomogeneousSystem parameters length compact state grade
          (collarRadius lower positive (bounded).le radius) (balanced (grade+1) radius)+
         balancedActualSource parameters length compact lower positive bounded state data curves grade
          (collarRadius lower positive (bounded).le radius))) (Icc lower 1) radius := by
  have actual := sameNativeBalanced_hilbertDerivative parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades grade radius inside
  rwa [sameNativeBalancedHilbertRHS_actual parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades grade radius inside] at actual

end Grad.OriginalCartesianTameEstimate
