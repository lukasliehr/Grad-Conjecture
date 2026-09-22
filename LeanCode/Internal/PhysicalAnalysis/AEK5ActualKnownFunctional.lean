import AEK4DirectKnownBulk

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.AxisCore Grad.RealFixedRanges
open Grad.AnnularVariational Grad.AnnularUniformBoundary
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentBoundary
open Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed
  Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed
  Grad.AnnularCurrentEnergy.energyRealModule

local instance knownBulkRealInner (lower : ℝ) :
    InnerProductSpace ℝ (DivisionRow 3 lower) :=
  InnerProductSpace.rclikeToReal ℂ (DivisionRow 3 lower)

local instance knownBoundaryRealInner (parameters : PhaseParameters)
    (angular cell : ℕ) :
    InnerProductSpace ℝ (NegativeTrace parameters angular cell 1) :=
  InnerProductSpace.rclikeToReal ℂ (NegativeTrace parameters angular cell 1)

/-- The prescribed datum and the original source-range contribution after the
same actual high boundary inverse.  The plus sign is the solved AI11 sign;
the full known functional below pairs its negative with the test trace. -/
def actualHighKnownBoundaryVector {parameters : PhaseParameters} {L compact : ℝ}
    (state : BoundaryInverseState parameters L compact) (angular cell : ℕ)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2)) :
    HighBoundaryPrimitive parameters angular cell :=
  actualBoundaryInverseOnHigh state angular cell datum +
    originalSourceBoundaryLiftOnHigh state angular cell source

section Functional

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (angular cell : ℕ)

/-- Literal complex AI14/BF13 known side.  AHW is used at power zero;
`g` is paired through `-r g`, `q_c` through the accepted `L⁻¹` test row,
`r q_v` directly, and the differentiated datum/source boundary vector has
the required minus sign. -/
def actualHighKnownFunctionalValue
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2))
    (test : annularEnergySpace lower L positive) : ℂ :=
  inner ℂ
      (highEnergyTestPacket parameters lower L positive lengthPositive
        widthHalf widthLength test)
      (actualHighKnownBulkOutput parameters L compact lower positive
        (lowerHalf.trans (by norm_num)) state known auxiliary) -
    inner ℂ
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
        lengthPositive angular cell test)
      (actualHighKnownBoundaryVector state.outerInverseState angular cell datum source).val

/-- Real functional consumed by the actual current coercive inverse. -/
def actualHighKnownFunctional
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2)) :
    annularEnergySpace lower L positive →L[ℝ] ℝ :=
  (innerSL ℝ (actualHighKnownBulkOutput parameters L compact lower positive
      (lowerHalf.trans (by norm_num)) state known auxiliary)).comp
    ((highEnergyTestPacket parameters lower L positive lengthPositive
      widthHalf widthLength).restrictScalars ℝ) -
  (innerSL ℝ
      (actualHighKnownBoundaryVector state.outerInverseState angular cell datum source).val).comp
    ((actualCurrentHighOuterTrace parameters lower L positive lowerHalf
      lengthPositive angular cell).restrictScalars ℝ)

theorem actualHighKnownFunctional_literal
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2))
    (test : annularEnergySpace lower L positive) :
    actualHighKnownFunctional parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state angular cell known auxiliary datum source test =
      (actualHighKnownFunctionalValue parameters L compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state angular cell known auxiliary datum source test).re := by
  change (inner ℂ
      (actualHighKnownBulkOutput parameters L compact lower positive
        (lowerHalf.trans (by norm_num)) state known auxiliary)
      (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)).re -
    (inner ℂ
      (actualHighKnownBoundaryVector state.outerInverseState angular cell datum source).val
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
        lengthPositive angular cell test)).re = _
  simp only [actualHighKnownFunctionalValue, Complex.sub_re]
  exact congrArg₂ (fun first second : ℝ => first - second)
    (inner_re_symm (𝕜 := ℂ) _ _) (inner_re_symm (𝕜 := ℂ) _ _)

/-- The same functional restricted to the actual zero-incoming-trace test
space, in the exact type expected by `currentHighDualInverse`. -/
def actualHighKnownZeroFunctional
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2)) :
    annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ :=
  (actualHighKnownFunctional parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state angular cell known auxiliary datum source).comp
      ((annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive).subtypeL.restrictScalars ℝ)

end Functional
end Grad.AnnularCurrentSource
