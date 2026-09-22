import AKI5SameCopiedSourceSmoothCore
import AKB11SameConjugatedResponse
import AJY2SamePhysicalPressure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff Topology
namespace Grad.AnnularOriginalSmoothCore
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.PhaseAlgebra Grad.AnnularPhysicalFourier Grad.AnnularSmoothSources Grad.AnnularSmoothCore
open Grad.AnnularStrongOrbit Grad.AnnularWeightedSmoothCore Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse Grad.AnnularClosedJointRegularity

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)
    (weightedSmooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade) (Icc lower 1))

include weightedSmooth

theorem originalResponseXi_weightedSmooth :
    OriginalWeightedPhysicalSmooth parameters lower
      (originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core) := by
  refine ⟨⟨originalSmoothResponsePhysicalXi_smooth_closed parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core,
    originalSmoothResponsePhysicalXi_angular_periodic parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core,
    originalSmoothResponsePhysicalXi_cell_periodic parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core⟩,
    (fun grade radius => (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade radius).2), (fun grade => (weightedSmooth grade).snd), ?_⟩
  intro grade radius inside mode
  have phase := congrArg Prod.snd (conjugatedSmoothResponsePairCurve_physical parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core grade mode radius inside)
  have frequency := congrArg Prod.snd (originalSmoothResponsePairCurve_coefficient_grade parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core grade radius mode)
  change _ = ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
    ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
      angularCoefficient (fun axial => angularCoefficient (fun polar => originalSmoothResponsePhysicalXi parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core (radius, polar, axial)) mode.1) mode.2)
  rw [originalSmoothResponsePhysicalXi_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius inside mode]
  change (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).2 mode =
    Real.exp (radialPhase parameters radius mode.2) •
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).2 mode at phase
  change (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).2 mode =
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius).2 mode at frequency
  rw [phase, frequency, smul_comm]
  exact congrArg (fun value => ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • value)
    (RCLike.real_smul_eq_coe_smul _ _)

theorem originalResponseP_weightedSmooth :
    OriginalWeightedPhysicalSmooth parameters lower
      (originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core) := by
  refine ⟨⟨originalSmoothResponsePhysicalP_smooth_closed parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core,
    originalSmoothResponsePhysicalP_angular_periodic parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core,
    originalSmoothResponsePhysicalP_cell_periodic parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core⟩,
    (fun grade radius => physicalAngularPrimitive parameters (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade radius).1),
      (fun grade => physicalAngularPrimitive_smooth parameters lower _ (weightedSmooth grade).fst), ?_⟩
  intro grade radius inside mode
  rw [physicalAngularPrimitive_apply]
  have phase := congrArg Prod.fst (conjugatedSmoothResponsePairCurve_physical parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core grade mode radius inside)
  have frequency := congrArg Prod.fst (originalSmoothResponsePairCurve_coefficient_grade parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core grade radius mode)
  change _ = ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
    ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
      angularCoefficient (fun axial => angularCoefficient (fun polar => originalSmoothResponsePhysicalP parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core (radius, polar, axial)) mode.1) mode.2)
  rw [originalSmoothResponsePhysicalP_coefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core radius inside mode,
    physicalAngularPrimitive_apply]
  change (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).1 mode =
    Real.exp (radialPhase parameters radius mode.2) •
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).1 mode at phase
  change (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius).1 mode =
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius).1 mode at frequency
  rw [phase, frequency, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [smul_comm (angularInverseMultiplier mode), smul_comm (angularInverseMultiplier mode)]
  exact smul_comm _ _ _

/-- Four actual fields of the SAME inverse. The only temporary hypothesis
is the exact weighted radial C∞ provider discharged by the actual bootstrap. -/
def sameResponseOriginalTuple : OriginalSmoothTuple parameters lower := by
  refine ⟨![originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core,
    originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core,
    originalSmoothSourcePhysicalF0 parameters lower positive (lowerHalf.trans_lt (by norm_num)) core,
    originalSmoothSourcePhysicalF2 parameters lower positive (lowerHalf.trans_lt (by norm_num)) core], ?_, ?_⟩
  · intro slot
    fin_cases slot
    · exact originalResponseP_weightedSmooth parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core weightedSmooth
    · exact originalResponseXi_weightedSmooth parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core weightedSmooth
    · exact originalCopiedF0_weightedSmooth parameters lower positive (lowerHalf.trans_lt (by norm_num)) core
    · exact originalCopiedF2_weightedSmooth parameters lower positive (lowerHalf.trans_lt (by norm_num)) core
  · intro slot meanFree radius inside cell
    fin_cases slot
    · exact originalSmoothResponsePhysicalP_zeroAngularCoefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core ⟨radius, inside⟩ cell
    · exact originalSmoothResponsePhysicalXi_zeroAngularCoefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core ⟨radius, inside⟩ cell
    · exact (meanFree rfl).elim
    · exact originalCopiedF2_meanFree parameters lower positive (lowerHalf.trans_lt (by norm_num)) core radius inside cell

end Grad.AnnularOriginalSmoothCore
