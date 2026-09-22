import AKV6GeneralActualConjugatedSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSystem Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)

def generalOriginalFullRHS (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 × ComplexEuclidean 1 :=
  actualOriginalUnknownRHS parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state field radius mode +
    generalOriginalSourceRHS parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state data radius mode

def generalConjugatedSystemRHS (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  physicalPairMeanFree parameters
    (conjugatedRadialSystemOperator parameters length compact lower state positive (lowerHalf.trans_lt (by norm_num))
      grade radius (conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field (grade+2) radius) +
    generalConjugatedSystemSource parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state data curves grade radius)

def generalWeightedSystemSource (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  physicalPairMeanFree parameters
    (generalConjugatedSystemSource parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state data curves grade radius)

theorem generalWeightedSystemSource_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (generalWeightedSystemSource parameters length compact lower positive lowerHalf state data curves grade) (Icc lower 1) :=
  ((physicalPairMeanFree parameters).restrictScalars ℝ).contDiff.comp_contDiffOn
    (generalConjugatedSystemSource_smooth parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state data curves grade)

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
  CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
include allGrades

theorem generalConjugatedSystemRHS_continuous (grade : ℕ) :
    ContinuousOn (generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data field curves grade)
      (Icc lower 1) := by
  obtain ⟨reserve, _, rowsSmooth⟩ := originalRows_commonReserve parameters length compact lower positive
    (lowerHalf.trans (by norm_num)) state (grade+1) 0 0
    (fun row => originalPhysicalRowKernel_finiteOrder parameters length compact state lower positive
      (lowerHalf.trans_lt (by norm_num)) row (grade+1) 0)
  have homogeneous := (reservedConjugatedRadialSystemOperator_smooth parameters length compact lower state positive
    (lowerHalf.trans_lt (by norm_num)) grade reserve 0 rowsSmooth).continuousOn.clm_apply
      (conjugatedOriginalPairCurve_continuous parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field allGrades
        (grade+2+reserve)).continuousOn
  have combined := (physicalPairMeanFree parameters).continuous.comp_continuousOn
    (homogeneous.add (generalConjugatedSystemSource_smooth parameters length compact lower positive
      (lowerHalf.trans_lt (by norm_num)) state data curves grade).continuousOn)
  apply combined.congr
  intro radius inside
  change physicalPairMeanFree parameters _ = physicalPairMeanFree parameters _
  dsimp only [Pi.add_apply]
  rw [reservedConjugatedRadialSystemOperator_same,
    conjugatedOriginalPairCurve_reserve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field allGrades
      (grade+2) reserve radius inside]

theorem generalConjugatedSystemRHS_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      hilbertPairCoefficient mode
        (generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data field curves grade radius) =
      (if mode.1 = 0 then (0 : ℂ) else 1) •
        (((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            generalOriginalFullRHS parameters length compact lower positive lowerHalf lengthPositive state data field radius mode)) := by
  filter_upwards [generalConjugatedRadialSystemOperator_physical parameters length compact lower positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive state field allGrades grade,
    originalRadialSystemOperator_actual parameters length compact lower positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive state field allGrades grade,
    generalConjugatedSystemSource_actual parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state data curves grade]
    with radius phase unknown source
  intro mode
  unfold generalConjugatedSystemRHS
  rw [physicalPairMeanFree_coefficient, (hilbertPairCoefficient mode).map_add, phase mode]
  have unknownMode := unknown mode
  change hilbertPairCoefficient mode
    (originalRadialSystemOperator parameters length compact lower state positive (lowerHalf.trans_lt (by norm_num)) grade radius
      (originalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field (grade+2) radius)) = _ at unknownMode
  have sourceMode := source mode
  change hilbertPairCoefficient mode
    (generalConjugatedSystemSource parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state data curves grade radius) = _ at sourceMode
  rw [unknownMode, sourceMode]
  rw [smul_comm (Real.exp (radialPhase parameters radius mode.2) : ℂ), ← smul_add, ← smul_add]
  rfl

theorem generalReservedWeightedSystem_same (grade reserve : ℕ) (enough : 5 ≤ reserve+2)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode
      (fullReservedWeightedSystemOperator parameters length compact lower positive lowerHalf state grade reserve radius
        (conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field (grade+2+reserve) radius) +
        generalWeightedSystemSource parameters length compact lower positive lowerHalf state data curves grade radius) =
      Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius • hilbertPairCoefficient mode
        (conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field grade radius) +
        hilbertPairCoefficient mode
          (generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data field curves grade radius) := by
  have phaseSame := phaseSlopePair_same parameters (reserve+2) enough radius
    (conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field (grade+2+reserve) radius)
    (conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field grade radius)
    (by intro query
        convert conjugatedOriginalPairCurve_shift parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
          field allGrades grade (reserve+2) radius inside query using 1
        congr 2
        omega) mode
  have inputSame := conjugatedOriginalPairCurve_reserve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field allGrades
    (grade+2) reserve radius inside
  unfold fullReservedWeightedSystemOperator generalWeightedSystemSource generalConjugatedSystemRHS
  rw [add_apply, ContinuousLinearMap.comp_apply, reservedConjugatedRadialSystemOperator_same, inputSame]
  rw [(hilbertPairCoefficient mode).map_add, (hilbertPairCoefficient mode).map_add, phaseSame,
    (physicalPairMeanFree parameters).map_add, (hilbertPairCoefficient mode).map_add]
  exact add_assoc _ _ _

end Grad.AnnularGeneralSourceRegularity
