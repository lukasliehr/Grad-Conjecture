import AKDN21ActualBalancedOperatorCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularWeightedSystem Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularOriginalCoreRealization

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

def sameNativeBalancedPhaseCurve (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  (balancedPhaseAction parameters 1 (collarRadius lower positive (bounded).le radius) (balanced (grade+1) radius).1,
   balancedPhaseAction parameters 1 (collarRadius lower positive (bounded).le radius) (balanced (grade+1) radius).2)

def sameNativeBalancedFluxCurve (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  balancedFluxOutput parameters length radius
    (unknownRow 0 grade radius,(unknownRow 1 grade radius,unknownRow 2 grade radius))

include curves

theorem balancedUnknownPhysicalRow_nativeSmooth (row : Fin 3) (grade : ℕ) :
    ContDiffOn ℝ ∞ (unknownRow row grade) (Icc lower 1) := by
  have same : unknownRow row grade = fun point => radialConjugatedAction parameters lower positive (bounded).le
      (lowPhysicalRowKernel parameters length compact state row) (grade+1) 0 point
      (sameNativeBalancedInput parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data (grade+1) point) := by
    funext point
    exact balancedUnknownPhysicalRow_sameNativeInput parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data row grade point
  rw [same]
  exact coherentConjugatedKernelCurve_smooth parameters lower positive (bounded).le
    (lowPhysicalRowKernel parameters length compact state row) _
    (sameNativeBalancedInput_smooth parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades)
    (sameNativeBalancedInput_shift parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data allGrades) (grade+1)
    (originalPhysicalRowKernel_finiteOrder parameters length compact state lower positive bounded row (grade+1))

theorem sameNativeBalancedPhaseCurve_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (sameNativeBalancedPhaseCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data grade) (Icc lower 1) := by
  have regular := sameNativeBalanced_smooth parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades
  have firstSame (power reserve : ℕ) (point : ℝ) (member : point ∈ Icc lower 1) (mode : ℤ × ℤ) :
      (balanced (power+reserve) point).1 mode = (annularFrequency mode.1 mode.2 : ℂ)^reserve • (balanced power point).1 mode := by
    exact congrArg Prod.fst (balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive response allGrades
      power reserve point member mode)
  have secondSame (power reserve : ℕ) (point : ℝ) (member : point ∈ Icc lower 1) (mode : ℤ × ℤ) :
      (balanced (power+reserve) point).2 mode = (annularFrequency mode.1 mode.2 : ℂ)^reserve • (balanced power point).2 mode := by
    exact congrArg Prod.snd (balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive response allGrades
      power reserve point member mode)
  exact (actualPhaseCurve_smooth parameters lower positive bounded (fun power point => (balanced power point).1)
    (fun power => (regular power).fst) firstSame grade).prodMk
    (actualPhaseCurve_smooth parameters lower positive bounded (fun power point => (balanced power point).2)
      (fun power => (regular power).snd) secondSame grade)

theorem sameNativeBalancedFluxCurve_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (sameNativeBalancedFluxCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data grade) (Icc lower 1) :=
  balancedFluxCurve_smooth parameters length (Icc lower 1) _
    ((balancedUnknownPhysicalRow_nativeSmooth parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades 0 grade).prodMk
     ((balancedUnknownPhysicalRow_nativeSmooth parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data curves allGrades 1 grade).prodMk
      (balancedUnknownPhysicalRow_nativeSmooth parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data curves allGrades 2 grade)))

omit allGrades curves in
theorem balancedHomogeneousSystem_nativeSplit (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    balancedHomogeneousSystem parameters length compact state grade (collarRadius lower positive (bounded).le radius)
      (balanced (grade+1) radius) =
      sameNativeBalancedPhaseCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data grade radius+
      sameNativeBalancedFluxCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data grade radius := by
  unfold balancedHomogeneousSystem sameNativeBalancedPhaseCurve sameNativeBalancedFluxCurve balancedUnknownPhysicalRow
  rw [collarRadius_literal lower positive (bounded).le radius inside]

omit allGrades in
theorem balancedActualSourceCurve_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (fun radius => balancedActualSource parameters length compact lower positive bounded state data curves grade
      (collarRadius lower positive (bounded).le radius)) (Icc lower 1) := by
  have rowRegular := generalConjugatedKnownRowCurve_smooth parameters length compact lower positive bounded state data curves
  have flux := balancedFluxCurve_smooth parameters length (Icc lower 1) _
    ((rowRegular 0 (grade+1)).prodMk ((rowRegular 1 (grade+1)).prodMk (rowRegular 2 (grade+1))))
  have force := ((hilbertMeanFree parameters).restrictScalars ℝ).contDiff.comp_contDiffOn (curves.forceSmooth (grade+1))
  have third := ((hilbertFrequencyOperator parameters 1 (some false)).restrictScalars ℝ).contDiff.comp_contDiffOn (curves.thirdSmooth (grade+1))
  apply (flux.add (force.prodMk third)).congr
  intro radius inside
  exact balancedActualSource_sameKnownCurves parameters length compact lower positive bounded state data curves grade radius inside

end Grad.OriginalCartesianTameEstimate
