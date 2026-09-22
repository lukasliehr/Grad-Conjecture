import AKG15OriginalNormalizedSourceLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularVariational Grad.AnnularCurrentGreen Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularKnownLow Grad.AnnularCurrentLow Grad.AnnularLowEnergy
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse

private theorem lowRestriction_fourSum {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (restriction : E →L[ℂ] F) (a b c d : E) :
    restriction (a + b + c + d) = restriction a + restriction b + restriction c + restriction d := by
  rw [map_add,map_add,map_add]

variable (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (state : RetainedInverseState parameters length compact)

/-- The full low stored row is local when the SAME full seven packet,
independent f and decoded g are restricted. All three premises are exact
source/retained identities, discharged by the original-data consumer below. -/
theorem strongLowPhysicalRHS_restriction
    (data : StrongDataCarrier parameters lower lowerPositive (included.trans upperBounded.le) 0 0)
    (target : StrongDataCarrier parameters upper upperPositive upperBounded.le 0 0)
    (candidate : CoupledSpace lower length lowerPositive lengthPositive)
    (sameSeven : originalBulkRestriction 7 lower upper included
      (fullStrongSevenInput parameters length lower lengthPositive lowerPositive (included.trans upperBounded.le) data candidate) =
      fullStrongSevenInput parameters length upper lengthPositive upperPositive upperBounded.le target
        (coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included candidate))
    (sameF : highSourceF upper (strongKnownBulk parameters upper upperPositive upperBounded.le target) =
      originalBulkRestriction 1 lower upper included (highSourceF lower
        (strongKnownBulk parameters lower lowerPositive (included.trans upperBounded.le) data)))
    (sameG : (strongToLow parameters upper upperPositive upperBounded.le 0 0 target).ofLp.1.ofLp.2 =
      originalBulkRestriction 1 lower upper included
        (strongToLow parameters lower lowerPositive (included.trans upperBounded.le) 0 0 data).ofLp.1.ofLp.2) :
    collarBulkRestriction LowAnnularIndex 1 lower upper included
      (strongLowPhysicalRHS parameters length compact lower lowerPositive (included.trans upperBounded.le) lengthPositive state data candidate) =
    strongLowPhysicalRHS parameters length compact upper upperPositive upperBounded.le lengthPositive state target
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included candidate) := by
  let input := fullStrongSevenInput parameters length lower lengthPositive lowerPositive (included.trans upperBounded.le) data candidate
  let next := fullStrongSevenInput parameters length upper lengthPositive upperPositive upperBounded.le target
    (coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included candidate)
  let restriction := originalBulkRestriction 1 lower upper included
  let bulk := collarBulkRestriction LowAnnularIndex 1 lower upper included
  let first := lowPhysicalRowAction parameters length compact lower lowerPositive (included.trans upperBounded.le) state
  let second := lowPhysicalRowAction parameters length compact upper upperPositive upperBounded.le state
  have row (slot : Fin 3) : restriction (first slot input) = second slot next :=
    (originalBulkRestriction_regularRadialBulkAction parameters 0 lower upper included lowerPositive upperPositive upperBounded.le
      (lowPhysicalRowKernel parameters length compact state slot) (lowPhysicalRowKernel_regular parameters length compact state slot) input).trans
      (congrArg (second slot) sameSeven)
  have j : restriction (first 0 input + highSourceF lower (strongKnownBulk parameters lower lowerPositive (included.trans upperBounded.le) data)) =
      second 0 next + highSourceF upper (strongKnownBulk parameters upper upperPositive upperBounded.le target) :=
    (map_add restriction _ _).trans (congrArg₂ (fun a b : DivisionRow 1 upper => a + b) (row 0) sameF.symm)
  have v : restriction (first 2 input - radialRadiusRow lower lowerPositive
      (strongToLow parameters lower lowerPositive (included.trans upperBounded.le) 0 0 data).ofLp.1.ofLp.2) =
      second 2 next - radialRadiusRow upper upperPositive (strongToLow parameters upper upperPositive upperBounded.le 0 0 target).ofLp.1.ofLp.2 :=
    (map_sub restriction _ _).trans (congrArg₂ (fun a b : DivisionRow 1 upper => a - b) (row 2)
      ((originalBulkRestriction_radius lower upper lowerPositive upperPositive included _).trans
        (congrArg (radialRadiusRow upper upperPositive) sameG.symm)))
  have diagonal := lowCommonDiagonal_restriction lower upper length lowerPositive upperPositive included parameters lengthPositive (candidate.ofLp.2.val 0)
  have firstOutput := (lowFirstOutput_restriction lower upper length included parameters _).trans
    (congrArg (lowFirstOutput parameters upper length) j)
  have cellOutput := (lowCellOutput_restriction lower upper length lowerPositive upperPositive included _).trans
    (congrArg (lowCellOutput upper length upperPositive) (row 1))
  have angularOutput := (lowAngularOutput_restriction lower upper length lowerPositive upperPositive included _).trans
    (congrArg (lowAngularOutput upper length upperPositive) v)
  exact (lowRestriction_fourSum bulk _ _ _ _).trans
    (congrArg₂ (fun a b : LowEnergyBulk upper => a + b)
      (congrArg₂ (fun a b : LowEnergyBulk upper => a + b)
        (congrArg₂ (fun a b : LowEnergyBulk upper => a + b) diagonal firstOutput) cellOutput) angularOutput)

/-- Actual full low stored-row locality for arbitrary ORIGINAL datum and
retained candidate, with every copied graph/residual fixed by restriction. -/
theorem originalStrongLowPhysicalRHS_restriction
    (data : OriginalStrongCarrier parameters lower 0 0) (target : OriginalStrongCarrier parameters upper 0 0)
    (sameSources : target.val.ofLp.1 = originalFullSourceRestriction parameters lower upper included data.val.ofLp.1)
    (candidate : OriginalCoupledSpace lower length lowerPositive) :
    collarBulkRestriction LowAnnularIndex 1 lower upper included
      (strongLowPhysicalRHS parameters length compact lower lowerPositive (included.trans upperBounded.le) lengthPositive state
        (originalStrongWeightEquivalence parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive 0 0 data)
        (originalCoupledEquivalence parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive candidate)) =
    strongLowPhysicalRHS parameters length compact upper upperPositive upperBounded.le lengthPositive state
      (originalStrongWeightEquivalence parameters upper length upperPositive upperBounded.le lengthPositive 0 0 target)
      (originalCoupledEquivalence parameters upper length upperPositive upperBounded.le lengthPositive
        (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included candidate)) := by
  have weighted := originalRetainedRestriction_weighted parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included candidate
  have seven := (originalSevenPacket_restriction_of_sources parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included data target sameSources candidate).trans
    (congrArg (fullStrongSevenInput parameters length upper lengthPositive upperPositive upperBounded.le
      (originalStrongWeightEquivalence parameters upper length upperPositive upperBounded.le lengthPositive 0 0 target)) weighted)
  have locality := strongLowPhysicalRHS_restriction parameters length compact lower upper lowerPositive upperPositive upperBounded lengthPositive included state
    (originalStrongWeightEquivalence parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive 0 0 data)
    (originalStrongWeightEquivalence parameters upper length upperPositive upperBounded.le lengthPositive 0 0 target)
    (originalCoupledEquivalence parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive candidate) seven
    (originalStrongWeight_f_restriction parameters lower upper length lowerPositive upperPositive upperBounded.le lengthPositive included data target sameSources)
    (originalStrongWeight_g_restriction parameters lower upper length lowerPositive upperPositive upperBounded.le lengthPositive included data target sameSources)
  exact locality.trans (congrArg (strongLowPhysicalRHS parameters length compact upper upperPositive upperBounded.le lengthPositive state
    (originalStrongWeightEquivalence parameters upper length upperPositive upperBounded.le lengthPositive 0 0 target)) weighted.symm)

end Grad.AnnularRestriction
