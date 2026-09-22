import AKDN22SameActualBalancedDecomposition

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

local notation "phaseCurve" => sameNativeBalancedPhaseCurve parameters length compact lower positive lowerHalf lengthPositive
  widthHalf widthLength state small data
local notation "fluxCurve" => sameNativeBalancedFluxCurve parameters length compact lower positive lowerHalf lengthPositive
  widthHalf widthLength state small data
local notation "knownCurve" => fun grade radius => balancedActualSource parameters length compact lower positive bounded state data curves grade
  (collarRadius lower positive (le_of_lt bounded) radius)

include curves

/-- Genuine first Euler derivative of the same native solution, with the
literal phase, homogeneous physical rows and prescribed source separated. -/
theorem sameNativeBalanced_firstEuler (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    vectorEulerWithinIteratedDerivative (Icc lower 1) 1 (balanced grade) radius =
      physicalPairMeanFree parameters ((phaseCurve grade radius+fluxCurve grade radius)+knownCurve grade radius) := by
  have derivative := sameNativeBalanced_actualDerivative parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades grade radius inside
  change radius • derivWithin (balanced grade) (Icc lower 1) radius = _
  rw [derivative.derivWithin (uniqueDiffOn_Icc bounded radius inside),smul_inv_smul₀ (positive.trans_le inside.1).ne',
    balancedHomogeneousSystem_nativeSplit parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data grade radius inside]

/-- The actual SR19 higher-Euler equation. Every derivative is a genuine
closed-collar derivative of the same native solution and same source.
Only the fixed angular projection is commuted with differentiation. -/
theorem sameNativeBalanced_higherEuler (grade rank : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    vectorEulerWithinIteratedDerivative (Icc lower 1) (rank+1) (balanced grade) radius =
      physicalPairMeanFree parameters
        ((vectorEulerWithinIteratedDerivative (Icc lower 1) rank (phaseCurve grade) radius+
          vectorEulerWithinIteratedDerivative (Icc lower 1) rank (fluxCurve grade) radius)+
         vectorEulerWithinIteratedDerivative (Icc lower 1) rank (knownCurve grade) radius) := by
  have phaseSmooth : ContDiffOn ℝ rank (phaseCurve grade) (Icc lower 1) :=
    contDiffOn_infty.mp (sameNativeBalancedPhaseCurve_smooth parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades grade) rank
  have fluxSmooth : ContDiffOn ℝ rank (fluxCurve grade) (Icc lower 1) :=
    contDiffOn_infty.mp (sameNativeBalancedFluxCurve_smooth parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades grade) rank
  have knownSmooth : ContDiffOn ℝ rank (knownCurve grade) (Icc lower 1) :=
    contDiffOn_infty.mp (balancedActualSourceCurve_smooth parameters length compact lower positive lowerHalf
      state data curves grade) rank
  have first : EqOn (vectorEulerWithinIteratedDerivative (Icc lower 1) 1 (balanced grade))
      (fun point => physicalPairMeanFree parameters ((phaseCurve grade point+fluxCurve grade point)+knownCurve grade point)) (Icc lower 1) := by
    intro point member
    exact sameNativeBalanced_firstEuler parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades grade point member
  rw [←vectorEulerWithin_right (Icc lower 1) (balanced grade) rank,
    vectorEulerWithin_congr (Icc lower 1) rank _ _ first inside]
  let observe := (physicalPairMeanFree parameters).restrictScalars ℝ
  have observed := vectorEulerWithin_observation (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun point => (phaseCurve grade point+fluxCurve grade point)+knownCurve grade point) observe rank
    ((phaseSmooth.add fluxSmooth).add knownSmooth) inside
  change _ = observe _ at observed
  rw [vectorEulerWithin_add (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun point => phaseCurve grade point+fluxCurve grade point) (knownCurve grade) rank (phaseSmooth.add fluxSmooth) knownSmooth radius inside,
    vectorEulerWithin_add (Icc lower 1) (uniqueDiffOn_Icc bounded)
      (phaseCurve grade) (fluxCurve grade) rank phaseSmooth fluxSmooth radius inside] at observed
  exact observed

end Grad.OriginalCartesianTameEstimate
