import AIQ14CompleteHighCrossResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCurrentGreen Grad.AnnularOmegaGraph Grad.AnnularTiltedReference Grad.AnnularCurrentBoundary

/-- The high response bound is fixed before the collar and coefficient state. -/
def actualHighCrossResponseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  32 * crossKnownConstant parameters L compact + 4 * crossOutputConstant parameters L compact

theorem actualHighCrossResponseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) :
    0 ≤ actualHighCrossResponseConstant parameters L compact :=
  add_nonneg (mul_nonneg (by norm_num) (crossKnownConstant_nonnegative parameters L compact))
    (mul_nonneg (by norm_num) (crossOutputConstant_nonnegative parameters L compact))

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- Uniform actual BF high response, with no loss in the original analytic width or Domega norm. -/
theorem actualHighCrossResponse_bound (data : CrossHighData parameters lower) :
    ‖actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ ≤
      actualHighCrossResponseConstant parameters L compact * ‖data‖ := by
  let response := actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have square := WithLp.prod_norm_sq_eq_of_L2 response
  change ‖response‖ ^ 2 = ‖response.ofLp.1‖ ^ 2 + ‖response.ofLp.2‖ ^ 2 at square
  have triangle : ‖response‖ ≤ ‖response.ofLp.1‖ + ‖response.ofLp.2‖ := by
    nlinarith [norm_nonneg response, norm_nonneg response.ofLp.1, norm_nonneg response.ofLp.2,
      mul_nonneg (norm_nonneg response.ofLp.1) (norm_nonneg response.ofLp.2)]
  have energy : ‖response.ofLp.1‖ ≤ (32 * crossKnownConstant parameters L compact) * ‖data‖ :=
    crossEnergyValue_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have graph : ‖response.ofLp.2‖ ≤ 4 * ‖crossPhysicalOutputValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ :=
    physicalOmegaCoordinates_bound parameters lower L positive lengthPositive widthHalf widthLength
      (crossPhysicalOutputValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
  have output := crossPhysicalOutputValue_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  change ‖response‖ ≤ _
  unfold actualHighCrossResponseConstant
  nlinarith

theorem actualHighCrossResponse_opNorm :
    ‖actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small‖ ≤
      actualHighCrossResponseConstant parameters L compact := by
  apply ContinuousLinearMap.opNorm_le_bound _ (actualHighCrossResponseConstant_nonnegative parameters L compact)
  exact actualHighCrossResponse_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small

theorem actualHighCrossResponse_physical_inner (data : CrossHighData parameters lower) :
    annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive
        (actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.1) = 0 :=
  crossEnergyValue_inner parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data

/-- Actual recovered x solves the completed physical first row for precisely the same high response. -/
theorem actualHighCrossResponse_firstRow (data : CrossHighData parameters lower) :
    let field := (actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.1
    retainedAAction parameters 0 lower positive (lowerHalf.trans (by norm_num)) L compact state
      (bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3)
        (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field
          (crossKnownWeighted parameters lower data) (crossKnownAuxiliary parameters lower data))) =
      eliminationRightHandAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, crossKnownWeighted parameters lower data)) := by
  dsimp only
  rw [actualFullHighOutput_first]
  exact congrArg (fun action : DivisionRow 8 lower →L[ℂ] DivisionRow 1 lower => action
    (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength
      ((actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.1,
        crossKnownWeighted parameters lower data)))
    (eliminatedXAction_solves parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0)

theorem actualHighCrossResponse_physical_boundary (data : CrossHighData parameters lower) :
    graphNativePhysicalBoundary state.outerInverseState 0 0
      (graphDataPhysicalOuter parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small (data.toGraphKnown parameters lower))
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0
        (actualHighCrossResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).ofLp.1)
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 (data.toGraphKnown parameters lower).graphs) = data.ofLp.2 :=
  graphDataPhysicalBoundary_eq_datum parameters L compact lower positive lowerHalf lengthPositive state widthHalf widthLength small
    (data.toGraphKnown parameters lower)

end Grad.AnnularPhysicalSolution
