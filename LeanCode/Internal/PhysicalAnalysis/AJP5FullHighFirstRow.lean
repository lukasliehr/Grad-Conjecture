import AJP4SameHighCoefficientSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularHighRadial Grad.AnnularCurrentLow Grad.AnnularReconstruction Grad.CircularHighRegularity
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothSources Grad.AnnularStrongOrbit Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy
open Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

def originalSmoothHighXiRHS (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  sharedRawHighXiRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    ((strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core) mode

def originalSmoothHighXRHS (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  sharedRawHighXRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    ((strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core) mode

/-- The high first weak row is exactly P(j_unknown+j_source+f) of the same solve. -/
theorem originalSmoothHighXiRHS_actual (mode : HighAnnularMode) :
    originalSmoothHighXiRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core mode
      =ᵐ[volume.restrict (Icc lower 1)] fun radius =>
        (actualOriginalFullRHS parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
          (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
          core radius mode.val).2 := by
  let data := (strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core
  let field := originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core
  let row := lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 0
    (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)
  let bulk := strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data
  change collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
    (radialOrdinary 1 lower positive ((row + highSourceF lower bulk) mode.val)) =ᵐ[_] _
  filter_upwards [rawHighPhase_radialOrdinary_ae parameters lower positive (row + highSourceF lower bulk) mode.val,
    lowRhoPhysicalCoefficient_add_ae parameters lower positive row (highSourceF lower bulk),
    fullStrongPhysicalCoefficient_split parameters length compact lower lengthPositive positive
      (lowerHalf.trans (by norm_num)) state data field 0] with radius decoded added split
  rw [decoded, added mode.val]
  rw [show lowRhoPhysicalCoefficient parameters lower positive row radius mode.val = _ from split mode.val]
  have nonzero : mode.val.1 ≠ 0 := by have large := mode.property; intro zero; simp [zero] at large
  simp only [actualOriginalFullRHS, actualOriginalUnknownRHS, actualOriginalSourceRHS,
    rawOriginalUnknownRHS, rawOriginalSourceRHS, Prod.snd_add, if_neg nonzero, one_smul]
  change (_ + _) + _ = _ + (_ + _)
  exact add_assoc _ _ _

end Grad.AnnularSmoothCore
