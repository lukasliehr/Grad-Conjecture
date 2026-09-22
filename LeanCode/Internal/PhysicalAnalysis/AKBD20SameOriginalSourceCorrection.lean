import AKBD19SameProjectedDeterminant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.ActualPolarFlux Grad.ActualCartesianEquations
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularSourceGraph
open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators Grad.AnnularForwardDatum Grad.AnnularRestriction
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.ActualOriginalThirdSource

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (lengthPositive : 0 < length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (same : data.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low lower positive bounded 0 source flat).val.ofLp.1)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) solution))
    (forces : ∀ component : Fin 3, SmoothLowPhysicalRow parameters lower positive
      (strongKnownBulk parameters lower positive bounded.le
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) (primitiveKnownSlot component)))

include same

/-- Every required source coordinate is the SAME original datum, including
F0 and F2 stored in the full seven packet. -/
theorem sameOriginalSource_coordinates (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (forces 0).fullField bounded (radius,angles) 0 = literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 0 angles 0 ∧
    curves.fullField bounded (radius,angles) 4 = literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 1 angles 0 ∧
    curves.fullField bounded (radius,angles) 6 = literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 2 angles 0 := by
  have literal (component : Fin 3) := sameKnownSource_fullField_literal parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
    lower positive bounded lengthPositive source flat data same component (forces component) radius inside angles
  refine ⟨congrArg (fun value : ComplexEuclidean 1 => value 0) (literal 0),?_,?_⟩
  · have known := sameSevenKnown_fullField parameters lower length positive bounded lengthPositive _ solution curves 0 (forces 1) radius inside angles
    have scalar := congrArg (fun value : ComplexEuclidean 1 => value 0) (known.trans (literal 1))
    change (curves.bulkUnit (0 : Fin 1) 4).fullField bounded (radius,angles) 0 = _ at scalar
    rwa [fullField_bulkUnit_zero_scalar curves bounded 4 radius inside angles] at scalar
  · have known := sameSevenKnown_fullField parameters lower length positive bounded lengthPositive _ solution curves 2 (forces 2) radius inside angles
    have scalar := congrArg (fun value : ComplexEuclidean 1 => value 0) (known.trans (literal 2))
    change (curves.bulkUnit (0 : Fin 1) 6).fullField bounded (radius,angles) 0 = _ at scalar
    rwa [fullField_bulkUnit_zero_scalar curves bounded 6 radius inside angles] at scalar

theorem sameOriginalSource_radialMean (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    removePolarMean (fun query => (forces 0).fullField bounded (radius,query) 0) angles =
      (forces 0).fullField bounded (radius,angles) 0 := by
  have literal := funext (fun query => congrArg (fun value : ComplexEuclidean 1 => value 0)
    (sameKnownSource_fullField_literal parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
      lower positive bounded lengthPositive source flat data same 0 (forces 0) radius inside query))
  have vector := congrArg (fun field : ℝ × ℝ → ComplexEuclidean 1 => field angles 0)
    (literalRadialSource_meanFree parameters length source flat radius (positive.le.trans inside.1) inside.2)
  rw [removePolarMean_coordinate _ (literalPrimitiveSource_continuous parameters length source radius (positive.le.trans inside.1) inside.2 0) angles] at vector
  exact (congrArg (fun field : ℝ × ℝ → ℂ => removePolarMean field angles) literal).trans (vector.trans (congrFun literal angles).symm)

theorem sameOriginalSource_correction (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    sameDeterminantSourceCorrection parameters length compact lower positive bounded state lengthPositive
      (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) solution curves (forces 0) radius angles =
      physicalCorrection parameters length state.val.val.epsilon state.val.val.field source radius (positive.le.trans inside.1) inside.2 angles 0 := by
  have literal := sameOriginalSource_coordinates parameters length compact lower positive bounded state lengthPositive source flat data same solution curves forces radius inside angles
  unfold sameDeterminantSourceCorrection
  refine Eq.trans ?_ (physicalCorrection_sameCofactor parameters length compact state source ⟨radius,positive.le.trans inside.1,inside.2⟩ angles).symm
  have triple : ((forces 0).fullField bounded (radius,angles) 0,curves.fullField bounded (radius,angles) 4,curves.fullField bounded (radius,angles) 6) =
      (literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 0 angles 0,
       literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 1 angles 0,
       literalPrimitiveSource parameters length source radius (positive.le.trans inside.1) inside.2 2 angles 0) :=
    Prod.ext literal.1 (Prod.ext literal.2.1 literal.2.2)
  exact congrArg (fun values : ℂ × (ℂ × ℂ) => (originalCofactorSmoothEntry parameters length compact state 1 0 radius angles * values.1 + originalCofactorSmoothEntry parameters length compact state 1 1 radius angles * values.2.1 - originalCofactorSmoothEntry parameters length compact state 1 2 radius angles * values.2.2) / (radius : ℂ)) triple

include same in
/-- Exact G3 from the original datum, in the very correction appearing in
the product-rule cancellation. -/
theorem sameOriginalSource_third (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive bounded.le 0 0
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data)).ofLp.1.ofLp.2)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    third.fullField bounded (radius,angles) 0 = (length : ℂ)⁻¹ * corePolarValue parameters (source 2) radius (positive.le.trans inside.1) inside.2 angles 0 +
      removePolarMean (sameDeterminantSourceCorrection parameters length compact lower positive bounded state lengthPositive
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) solution curves (forces 0) radius) angles := by
  have given := congrArg (fun value : ComplexEuclidean 1 => value 0)
    (sameThird_fullField_physicalG3_pointwise parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
      lower positive bounded lengthPositive source flat data same third radius inside angles)
  have physical : physicalG3 parameters length state.val.val.epsilon state.val.val.field source radius (positive.le.trans inside.1) inside.2 angles 0 =
      (length : ℂ)⁻¹ * corePolarValue parameters (source 2) radius (positive.le.trans inside.1) inside.2 angles 0 +
      removePolarMean (fun query => physicalCorrection parameters length state.val.val.epsilon state.val.val.field source radius (positive.le.trans inside.1) inside.2 query 0) angles := by
    exact congrArg ((length : ℂ)⁻¹ * corePolarValue parameters (source 2) radius (positive.le.trans inside.1) inside.2 angles 0 + ·)
      (removePolarMean_coordinate _ (physicalCorrection_continuous parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low source radius (positive.le.trans inside.1) inside.2) angles)
  have correction := funext (fun query => sameOriginalSource_correction parameters length compact lower positive bounded state lengthPositive source flat data same solution curves forces radius inside query)
  exact given.trans (physical.trans (congrArg (fun field : ℝ × ℝ → ℂ =>
    (length : ℂ)⁻¹ * corePolarValue parameters (source 2) radius (positive.le.trans inside.1) inside.2 angles 0 + removePolarMean field angles) correction.symm))

end Grad.ActualDeterminantEquations
