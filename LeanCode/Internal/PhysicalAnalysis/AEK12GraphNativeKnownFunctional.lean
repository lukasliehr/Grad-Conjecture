import AEK11GraphNativeBoundaryVector

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
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

local instance graphKnownBulkRealInner (lower : ℝ) :
    InnerProductSpace ℝ (DivisionRow 3 lower) :=
  InnerProductSpace.rclikeToReal ℂ (DivisionRow 3 lower)

local instance graphKnownBoundaryRealInner (parameters : PhaseParameters)
    (angular cell : ℕ) :
    InnerProductSpace ℝ (NegativeTrace parameters angular cell 1) :=
  InnerProductSpace.rclikeToReal ℂ (NegativeTrace parameters angular cell 1)

/-- BF2's complete known packet at every split grade.  The weighted bulk
coordinates and genuine unweighted radial graphs are linked by the exact
`r^(-9/4)` compatibility, and the outer tuple is derived from those graphs. -/
structure ActualHighGraphKnownData (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) where
  weighted : HighKnownSourceBulk lower
  auxiliary : HighAuxiliarySourceBulk lower
  graphs : HighRadialSourceGraphs parameters lower (angular + cell)
  datum : HighBoundaryPrimitive parameters angular cell
  innerValue : AnnularBoundary
  weightedGraph : WeightedGraphCompatibility parameters lower
    (angular + cell) graphs weighted

section Functional

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (angular cell : ℕ)

/-- Literal complex AI14/BF13 known side on the graph-native outer source.
The boundary term is `-<trace test,T⁻¹ datum-T⁻¹H source>`, while the
bulk term uses AHW at power zero and the direct `(0,qc,rqv-rg)` rows. -/
def actualHighGraphKnownFunctionalValue
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell))
    (datum : HighBoundaryPrimitive parameters angular cell)
    (test : annularEnergySpace lower L positive) : ℂ :=
  inner ℂ
      (highEnergyTestPacket parameters lower L positive lengthPositive
        widthHalf widthLength test)
      (actualHighKnownBulkOutput parameters L compact lower positive
        (lowerHalf.trans (by norm_num)) state known auxiliary) -
    inner ℂ
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
        lengthPositive angular cell test)
      (actualHighGraphBoundaryVector state.outerInverseState angular cell datum
        (highGraphOuterTuple parameters lower positive
          (lowerHalf.trans_lt (by norm_num)) (angular + cell) graphs)).val

/-- Real graph-native known functional consumed by the actual current
coercive inverse. -/
def actualHighGraphKnownFunctional
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell))
    (datum : HighBoundaryPrimitive parameters angular cell) :
    annularEnergySpace lower L positive →L[ℝ] ℝ :=
  (innerSL ℝ (actualHighKnownBulkOutput parameters L compact lower positive
      (lowerHalf.trans (by norm_num)) state known auxiliary)).comp
    ((highEnergyTestPacket parameters lower L positive lengthPositive
      widthHalf widthLength).restrictScalars ℝ) -
  (innerSL ℝ
      (actualHighGraphBoundaryVector state.outerInverseState angular cell datum
        (highGraphOuterTuple parameters lower positive
          (lowerHalf.trans_lt (by norm_num)) (angular + cell) graphs)).val).comp
    ((actualCurrentHighOuterTrace parameters lower L positive lowerHalf
      lengthPositive angular cell).restrictScalars ℝ)

theorem actualHighGraphKnownFunctional_literal
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell))
    (datum : HighBoundaryPrimitive parameters angular cell)
    (test : annularEnergySpace lower L positive) :
    actualHighGraphKnownFunctional parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state angular cell known auxiliary
        graphs datum test =
      (actualHighGraphKnownFunctionalValue parameters L compact lower positive
        lowerHalf lengthPositive widthHalf widthLength state angular cell known
          auxiliary graphs datum test).re := by
  change (inner ℂ
      (actualHighKnownBulkOutput parameters L compact lower positive
        (lowerHalf.trans (by norm_num)) state known auxiliary)
      (highEnergyTestPacket parameters lower L positive lengthPositive
        widthHalf widthLength test)).re -
    (inner ℂ
      (actualHighGraphBoundaryVector state.outerInverseState angular cell datum
        (highGraphOuterTuple parameters lower positive
          (lowerHalf.trans_lt (by norm_num)) (angular + cell) graphs)).val
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf
        lengthPositive angular cell test)).re = _
  simp only [actualHighGraphKnownFunctionalValue, Complex.sub_re]
  exact congrArg₂ (fun first second : ℝ => first - second)
    (inner_re_symm (𝕜 := ℂ) _ _) (inner_re_symm (𝕜 := ℂ) _ _)

/-- Restriction to the genuine zero-incoming test space, in the type consumed
by the current high dual inverse. -/
def actualHighGraphKnownZeroFunctional
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell))
    (datum : HighBoundaryPrimitive parameters angular cell) :
    annularInnerZero lower L positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ :=
  (actualHighGraphKnownFunctional parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state angular cell known auxiliary
      graphs datum).comp
    ((annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive).subtypeL.restrictScalars ℝ)

/-- On compatible large-grade ambient source data, the graph-native value is
exactly the already accepted AEK5 value. -/
theorem actualHighGraphKnownFunctionalValue_eq_known
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell))
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2))
    (same : highGraphOuterTuple parameters lower positive
      (lowerHalf.trans_lt (by norm_num)) (angular + cell) graphs =
        sourceOuterTrace parameters L (angular + cell) source)
    (test : annularEnergySpace lower L positive) :
    actualHighGraphKnownFunctionalValue parameters L compact lower positive
      lowerHalf lengthPositive widthHalf widthLength state angular cell known
        auxiliary graphs datum test =
      actualHighKnownFunctionalValue parameters L compact lower positive
        lowerHalf lengthPositive widthHalf widthLength state angular cell known
          auxiliary datum source test := by
  unfold actualHighGraphKnownFunctionalValue actualHighKnownFunctionalValue
  have boundary := actualHighGraphBoundaryVector_eq_known
    state.outerInverseState angular cell datum _ source same
  rw [congrArg Subtype.val boundary]

/-- The same exact compatibility at the real continuous-functional level. -/
theorem actualHighGraphKnownFunctional_eq_known
    (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower)
    (graphs : HighRadialSourceGraphs parameters lower (angular + cell))
    (datum : HighBoundaryPrimitive parameters angular cell)
    (source : ZAmbient parameters (angular + cell + 2))
    (same : highGraphOuterTuple parameters lower positive
      (lowerHalf.trans_lt (by norm_num)) (angular + cell) graphs =
        sourceOuterTrace parameters L (angular + cell) source) :
    actualHighGraphKnownFunctional parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state angular cell known auxiliary
        graphs datum =
      actualHighKnownFunctional parameters L compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state angular cell known auxiliary
          datum source := by
  apply ContinuousLinearMap.ext
  intro test
  rw [actualHighGraphKnownFunctional_literal, actualHighKnownFunctional_literal]
  rw [actualHighGraphKnownFunctionalValue_eq_known parameters L compact lower
    positive lowerHalf lengthPositive widthHalf widthLength state angular cell
    known auxiliary graphs datum source same test]

end Functional
end Grad.AnnularCurrentSource
