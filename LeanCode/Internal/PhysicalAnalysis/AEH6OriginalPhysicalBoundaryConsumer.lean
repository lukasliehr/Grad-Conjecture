import AEH5SesquilinearBoundaryForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Grad.AnnularCurrentBoundary

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.BoundaryTrace Grad.AxisCore Grad.RealFixedRanges
open Grad.AnnularVariational Grad.BoundaryKernelAction
open Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse Grad.AnnularReconstruction

section Consumer

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (angular cell : ℕ) (large : 3 ≤ angular + cell + 2)
    (state : RetainedInverseState parameters L compact)

/-- Exact AHV10/BCI25 consumer with the current annular energy supplying the
original positive trace. The complete `sourceRange` and physical datum are
unchanged; no source slot is subjected to a new trace hypothesis. -/
theorem actualCurrentHighBoundary_originalPhysical_iff
    (field : annularEnergySpace lower L positive)
    (x datum : HighBoundaryPrimitive parameters angular cell)
    (source : sourceRange parameters (angular + cell + 2) large) :
    physicalBoundaryFromPrescribedSource parameters L
      state.boundaryState.val.rho state.boundaryState.val.alpha
      state.boundaryState.val.delta state.boundaryState.val.parameter
      state.boundaryState.val.epsilon compact state.boundaryState.val.field
      state.boundaryState.property state.boundaryState.val.compactNonnegative
      state.boundaryState.val.alphaSmall state.boundaryState.val.deltaSmall
      state.boundaryState.val.parameterSmall angular cell large
      ⟨x.val, x.property.meanFree⟩
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
        lengthPositive angular cell field) source = datum ↔
    x = actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
          lengthPositive angular cell state.outerInverseState field +
      (actualBoundaryInverseOnHigh state.outerInverseState angular cell datum +
        originalSourceBoundaryLiftOnHigh state.outerInverseState angular cell source.val) := by
  simpa only [actualCurrentHighBoundaryD_apply] using
    (retainedInverse_originalPhysicalBoundary_iff state angular cell large x datum
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
        lengthPositive angular cell field) source)

/-- The exact equation remains valid after spelling the SAME AAG outer trace
of the literal `b_m`-decoded energy. -/
theorem actualCurrentHighBoundary_sameTrace_originalPhysical_iff
    (field : annularEnergySpace lower L positive)
    (x datum : HighBoundaryPrimitive parameters angular cell)
    (source : sourceRange parameters (angular + cell + 2) large) :
    physicalBoundaryFromPrescribedSource parameters L
      state.boundaryState.val.rho state.boundaryState.val.alpha
      state.boundaryState.val.delta state.boundaryState.val.parameter
      state.boundaryState.val.epsilon compact state.boundaryState.val.field
      state.boundaryState.property state.boundaryState.val.compactNonnegative
      state.boundaryState.val.alphaSmall state.boundaryState.val.deltaSmall
      state.boundaryState.val.parameterSmall angular cell large
      ⟨x.val, x.property.meanFree⟩
      (highBoundaryIntoPositive parameters angular cell
        (annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num))
          lengthPositive 1 (Grad.AnnularTiltedReference.bEnergyDecode lower L positive field)))
      source = datum ↔
    x = actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
          lengthPositive angular cell state.outerInverseState field +
      (actualBoundaryInverseOnHigh state.outerInverseState angular cell datum +
        originalSourceBoundaryLiftOnHigh state.outerInverseState angular cell source.val) := by
  rw [← actualCurrentHighOuterTrace_same parameters lower L positive lowerHalf
    lengthPositive angular cell field]
  exact actualCurrentHighBoundary_originalPhysical_iff parameters L compact lower positive
    lowerHalf lengthPositive angular cell large state field x datum source

end Consumer

end Grad.AnnularCurrentBoundary
