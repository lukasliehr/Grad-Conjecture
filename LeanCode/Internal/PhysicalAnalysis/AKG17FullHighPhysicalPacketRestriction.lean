import AKG16FullStoredLowRowRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularVariational Grad.AnnularCurrentGreen Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularKnownLow Grad.AnnularCurrentLow Grad.AnnularLowEnergy
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularCrossMaps

private theorem highRestriction_threeSum {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (restriction : E →L[ℂ] F) (a b c : E) :
    restriction (a + b + c) = restriction a + restriction b + restriction c := by
  rw [map_add,map_add]

variable (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (state : RetainedInverseState parameters length compact)

theorem fullStrongHighPacket_restriction
    (data : StrongDataCarrier parameters lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) 0 0)
    (target : StrongDataCarrier parameters upper upperPositive (upperHalf.trans (by norm_num)) 0 0)
    (candidate : CoupledSpace lower length lowerPositive lengthPositive)
    (sameSeven : originalBulkRestriction 7 lower upper included
      (fullStrongSevenInput parameters length lower lengthPositive lowerPositive ((included.trans upperHalf).trans (by norm_num)) data candidate) =
      fullStrongSevenInput parameters length upper lengthPositive upperPositive (upperHalf.trans (by norm_num)) target
        (coupledEndpointRestriction lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate))
    (sameG : (strongToLow parameters upper upperPositive (upperHalf.trans (by norm_num)) 0 0 target).ofLp.1.ofLp.2 =
      originalBulkRestriction 1 lower upper included
        (strongToLow parameters lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2) :
    originalBulkRestriction 3 lower upper included
      (fullStrongHighPacket parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state data candidate) =
    fullStrongHighPacket parameters length compact upper upperPositive upperHalf lengthPositive state target
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate) := by
  let input := fullStrongSevenInput parameters length lower lengthPositive lowerPositive ((included.trans upperHalf).trans (by norm_num)) data candidate
  let next := fullStrongSevenInput parameters length upper lengthPositive upperPositive (upperHalf.trans (by norm_num)) target
    (coupledEndpointRestriction lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate)
  let restriction := originalBulkRestriction 1 lower upper included
  let first := lowPhysicalRowAction parameters length compact lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) state
  let second := lowPhysicalRowAction parameters length compact upper upperPositive (upperHalf.trans (by norm_num)) state
  have row (slot : Fin 3) : restriction (first slot input) = second slot next :=
    (originalBulkRestriction_regularRadialBulkAction parameters 0 lower upper included lowerPositive upperPositive (upperHalf.trans (by norm_num))
      (lowPhysicalRowKernel parameters length compact state slot) (lowPhysicalRowKernel_regular parameters length compact state slot) input).trans
      (congrArg (second slot) sameSeven)
  have v : restriction (first 2 input - radialRadiusRow lower lowerPositive
      (strongToLow parameters lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2) =
      second 2 next - radialRadiusRow upper upperPositive (strongToLow parameters upper upperPositive (upperHalf.trans (by norm_num)) 0 0 target).ofLp.1.ofLp.2 :=
    (map_sub restriction _ _).trans (congrArg₂ (fun a b : DivisionRow 1 upper => a - b) (row 2)
      ((originalBulkRestriction_radius lower upper lowerPositive upperPositive included _).trans
        (congrArg (radialRadiusRow upper upperPositive) sameG.symm)))
  have x := (bulkMatrixUnit_restriction lower upper included (0 : Fin 3) (0 : Fin 1) _).trans
    (congrArg (bulkMatrixUnit upper (0 : Fin 3) (0 : Fin 1))
      (highBulkIntoFull_restriction lower upper included (crossHighX lower length lowerPositive lengthPositive candidate.ofLp.1)))
  have c := (bulkMatrixUnit_restriction lower upper included (1 : Fin 3) (0 : Fin 1) _).trans
    (congrArg (bulkMatrixUnit upper (1 : Fin 3) (0 : Fin 1))
      ((highRowProjection_restriction lower upper included (first 1 input)).trans
        (congrArg (highRowProjection upper) (row 1))))
  have rv := (bulkMatrixUnit_restriction lower upper included (2 : Fin 3) (0 : Fin 1) _).trans
    (congrArg (bulkMatrixUnit upper (2 : Fin 3) (0 : Fin 1))
      ((highRowProjection_restriction lower upper included _).trans (congrArg (highRowProjection upper) v)))
  exact (highRestriction_threeSum (originalBulkRestriction 3 lower upper included) _ _ _).trans
    (congrArg₂ (fun a b : DivisionRow 3 upper => a + b)
      (congrArg₂ (fun a b : DivisionRow 3 upper => a + b) x c) rv)

/-- Literal original x/c/(rV-rg) high packet at arbitrary equation
candidates; source identity is the exact four-block restriction. -/
theorem originalFullStrongHighPacket_restriction
    (data : OriginalStrongCarrier parameters lower 0 0) (target : OriginalStrongCarrier parameters upper 0 0)
    (sameSources : target.val.ofLp.1 = originalFullSourceRestriction parameters lower upper included data.val.ofLp.1)
    (candidate : OriginalCoupledSpace lower length lowerPositive) :
    originalBulkRestriction 3 lower upper included
      (fullStrongHighPacket parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state
        (originalStrongWeightEquivalence parameters lower length lowerPositive ((included.trans upperHalf).trans (by norm_num)) lengthPositive 0 0 data)
        (originalCoupledEquivalence parameters lower length lowerPositive ((included.trans upperHalf).trans (by norm_num)) lengthPositive candidate)) =
    fullStrongHighPacket parameters length compact upper upperPositive upperHalf lengthPositive state
      (originalStrongWeightEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive 0 0 target)
      (originalCoupledEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive
        (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate)) := by
  have weighted := originalRetainedRestriction_weighted parameters lower upper length lowerPositive upperPositive
    (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate
  have seven := (originalSevenPacket_restriction_of_sources parameters lower upper length lowerPositive upperPositive
    (upperHalf.trans_lt (by norm_num)) lengthPositive included data target sameSources candidate).trans
      (congrArg (fullStrongSevenInput parameters length upper lengthPositive upperPositive (upperHalf.trans (by norm_num))
        (originalStrongWeightEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive 0 0 target)) weighted)
  have locality := fullStrongHighPacket_restriction parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
    (originalStrongWeightEquivalence parameters lower length lowerPositive ((included.trans upperHalf).trans (by norm_num)) lengthPositive 0 0 data)
    (originalStrongWeightEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive 0 0 target)
    (originalCoupledEquivalence parameters lower length lowerPositive ((included.trans upperHalf).trans (by norm_num)) lengthPositive candidate) seven
    (originalStrongWeight_g_restriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans (by norm_num)) lengthPositive included data target sameSources)
  exact locality.trans (congrArg (fullStrongHighPacket parameters length compact upper upperPositive upperHalf lengthPositive state
    (originalStrongWeightEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive 0 0 target)) weighted.symm)

end Grad.AnnularRestriction
