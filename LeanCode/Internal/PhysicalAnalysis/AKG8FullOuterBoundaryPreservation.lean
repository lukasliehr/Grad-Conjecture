import AKG7GenuineOuterTraceLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularCurrentSource Grad.AnnularCurrentBoundary Grad.AnnularCrossMaps Grad.AnnularLowEnergy
open Grad.AnnularTiltedReference Grad.AnnularForwardTraces Grad.BoundaryKernelAction Grad.AnnularCoupledInverse
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularForwardDatum Grad.AnnularReconstruction
open Grad.AnnularPhysicalSolution Grad.ActualBoundaryPrimitives
open Grad.GaugeCoefficients.Physical.WeightedTrace
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule

private theorem boundaryCongrFour {A B C D E : Type*} (f : A → B → C → D → E)
    {a a' : A} {b b' : B} {c c' : C} {d d' : D}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') : f a b c d = f a' b' c' d' := by
  cases ha; cases hb; cases hc; cases hd; rfl

variable (lower upper length : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (upperHalf : upper ≤ 1 / 2) (included : lower ≤ upper)

theorem lowEnergyRestriction_outerEndpoint (field : lowEnergyGraph lower length lowerPositive)
    (index : LowAnnularIndex) :
    lowEnergyEndpoint upper length upperPositive (upperHalf.trans_lt (by norm_num)) 1
      (lowEnergyRestriction lower upper length included lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) field) index =
    lowEnergyEndpoint lower length lowerPositive ((included.trans upperHalf).trans_lt (by norm_num)) 1 field index :=
  congrArg (fun representative : RadialContinuousSection 1 upper =>
    representative ⟨1,upperHalf.trans (by norm_num),le_rfl⟩)
      (lowEnergyRestriction_section lower upper length included lowerPositive upperPositive
        (upperHalf.trans_lt (by norm_num)) field index)

theorem lowEnergyRestriction_halfOuter (field : lowEnergyGraph lower length lowerPositive) :
    lowOuterHalfTrace upper length upperPositive upperHalf
      (lowEnergyRestriction lower upper length included lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) field) =
    lowOuterHalfTrace lower length lowerPositive (included.trans upperHalf) field := by
  apply lp.ext
  funext index
  rw [lowOuterHalfTrace_apply,lowOuterHalfTrace_apply,
    lowEnergyRestriction_outerEndpoint lower upper length lowerPositive upperPositive upperHalf included]

variable (parameters : PhaseParameters) (lengthPositive : 0 < length)

theorem lowEnergyRestriction_outerX (field : lowEnergyGraph lower length lowerPositive) :
    lowOuterXNegative parameters upper length lengthPositive upperPositive upperHalf
      (lowEnergyRestriction lower upper length included lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) field) =
    lowOuterXNegative parameters lower length lengthPositive lowerPositive (included.trans upperHalf) field := by
  unfold lowOuterXNegative
  simp only [ContinuousLinearMap.comp_apply]
  rw [lowEnergyRestriction_halfOuter]

theorem lowEnergyRestriction_outerXi (field : lowEnergyGraph lower length lowerPositive) :
    lowOuterXiPositive parameters upper length lengthPositive upperPositive upperHalf
      (lowEnergyRestriction lower upper length included lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) field) =
    lowOuterXiPositive parameters lower length lengthPositive lowerPositive (included.trans upperHalf) field := by
  unfold lowOuterXiPositive
  simp only [ContinuousLinearMap.comp_apply]
  rw [lowEnergyRestriction_halfOuter]

theorem lowEnergyRestriction_outerSeven (field : lowEnergyGraph lower length lowerPositive) :
    lowOuterSevenTrace parameters upper length lengthPositive upperPositive upperHalf
      (lowEnergyRestriction lower upper length included lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) field) =
    lowOuterSevenTrace parameters lower length lengthPositive lowerPositive (included.trans upperHalf) field := by
  rw [lowOuterSevenTrace_apply,lowOuterSevenTrace_apply,lowEnergyRestriction_outerX,lowEnergyRestriction_outerXi]

theorem coupledEndpointRestriction_fluxOuter (field : CoupledSpace lower length lowerPositive lengthPositive) :
    coupledHighFluxOuter parameters upper length upperPositive upperHalf lengthPositive
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included field) =
    coupledHighFluxOuter parameters lower length lowerPositive (included.trans upperHalf) lengthPositive field :=
  congrArg (highFluxBoundaryEmbedding parameters)
    (highOmegaRestriction_outerTrace lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num))
      lengthPositive included field.ofLp.1.ofLp.2)

variable (compact : ℝ) (state : RetainedInverseState parameters length compact)

/-- The original complete physical h is unchanged: T, N, the full copied
source H term, and the low physical outer contribution all use the SAME endpoint values. -/
theorem coupledEndpointRestriction_fullOuter (field : CoupledSpace lower length lowerPositive lengthPositive)
    (graphs : HighKnownGraphHilbert parameters lower) :
    coupledFullOuterBoundary parameters length compact upper upperPositive upperHalf lengthPositive state
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included field)
      (originalSourceGraphPairRestriction parameters lower upper included graphs) =
    coupledFullOuterBoundary parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state field graphs := by
  have flux := coupledEndpointRestriction_fluxOuter lower upper length lowerPositive upperPositive upperHalf included parameters lengthPositive field
  have xi := highEnergyRestriction_actualOuter parameters lower upper length lowerPositive upperPositive upperHalf lengthPositive included field.ofLp.1.ofLp.1
  have source := originalSourceGraphPairRestriction_outerTuple parameters lower upper included lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) graphs
  have low := lowEnergyRestriction_outerSeven lower upper length lowerPositive upperPositive upperHalf included parameters lengthPositive field.ofLp.2
  exact boundaryCongrFour
    (fun (x : HighBoundaryPrimitive parameters 0 0) (xi : PositiveTrace parameters 0 0 1)
      (source : SourceBoundaryTuple) (low : SevenSlotTrace parameters 0 0) =>
      graphNativePhysicalBoundary state.outerInverseState 0 0 x xi source +
        lowStateBoundaryPR parameters length compact state low)
    flux xi source low

/-- Full outer datum locality in the literal original BF6 coordinates. -/
theorem originalRetainedRestriction_fullOuter (candidate : OriginalCoupledSpace lower length lowerPositive)
    (graphs : HighKnownGraphHilbert parameters lower) :
    originalOuterBoundaryTrace parameters length compact upper upperPositive upperHalf lengthPositive state
      (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive
        (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate,
        originalSourceGraphPairRestriction parameters lower upper included graphs) =
    originalOuterBoundaryTrace parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state (candidate,graphs) := by
  exact (originalOuterBoundaryTrace_to_coupled parameters length compact upper upperPositive upperHalf lengthPositive state _ _).trans
    ((congrArg (fun weighted => coupledFullOuterBoundary parameters length compact upper upperPositive upperHalf lengthPositive state weighted
      (originalSourceGraphPairRestriction parameters lower upper included graphs))
      (originalRetainedRestriction_weighted parameters lower upper length lowerPositive upperPositive
        (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate)).trans
      ((coupledEndpointRestriction_fullOuter lower upper length lowerPositive upperPositive upperHalf included parameters lengthPositive compact state _ graphs).trans
        (originalOuterBoundaryTrace_to_coupled parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state candidate graphs).symm))

end Grad.AnnularRestriction
