import AKI18LiteralOriginalCoreImage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore
open Grad.AnnularStrongOrbit Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularCurrentLow Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularFullGraph Grad.AnnularSolvedGraphDensity Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

theorem originalCoreResponse_equivalence :
    originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
      (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core)) =
      originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core := by
  rw [originalSmoothSolve_same, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Every observed coordinate comes from the literal four-field tuple:
retained pressure/scalar, copied genuine source graphs, and computed AH24
full residuals. There is no core-membership or residual-equality premise. -/
theorem originalSmoothResponseCoreTuple_observation :
    OriginalTupleObservation parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
      (originalSmoothResponseCoreTuple parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      (originalFiveBlockObservation parameters lower length positive
        (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core,
          originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
            (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core))) := by
  constructor
  · intro radius mode
    change originalPhysicalCoefficient
      (originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      radius.val mode = angularInverseMultiplier mode • sameCoupledXCoefficient parameters lower length positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
          (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
            (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core))) 0 radius mode
    rw [originalCoreResponse_equivalence]
    exact originalSmoothResponsePhysicalP_raw_coefficient parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core radius mode
  · intro radius mode
    change originalPhysicalCoefficient
      (originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      radius.val mode = sameCoupledXiCoefficient parameters lower length positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
          (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
            (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core))) 0 radius mode
    rw [originalCoreResponse_equivalence]
    exact originalSmoothResponsePhysicalXi_raw_coefficient parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core radius mode
  · exact originalSmoothSourcePhysicalF0_actual parameters lower positive (lowerHalf.trans_lt (by norm_num)) core
  · exact originalSmoothSourcePhysicalF2_actual parameters lower positive (lowerHalf.trans_lt (by norm_num)) core
  · exact originalSmoothResponseCoreTuple_F1 parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core
  · exact originalSmoothResponseCoreTuple_G3 parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core

/-- SAME smooth-source response membership in the literal original core
image, on its exact original annular endpoint domain. -/
theorem originalSmoothResponse_coreAnn (domain : lower ≤ min (1 / 2) length) :
    originalFiveBlockObservation parameters lower length positive
      (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core,
        originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core)) ∈
      CoreAnn parameters length compact lower positive domain lengthPositive state :=
  ⟨originalSmoothResponseCoreTuple parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core,
    originalSmoothResponseCoreTuple_observation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core⟩

theorem originalSmoothResponse_coreAnnClosure (domain : lower ≤ min (1 / 2) length) :
    originalFiveBlockObservation parameters lower length positive
      (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core,
        originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (originalSmoothStrongData parameters lower positive (lowerHalf.trans (by norm_num)) core)) ∈
      CoreAnnClosure parameters length compact lower positive domain lengthPositive state :=
  subset_closure (originalSmoothResponse_coreAnn parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core domain)

end Grad.AnnularOriginalSmoothCore
