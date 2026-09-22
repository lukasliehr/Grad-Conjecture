import AKBD20SameOriginalSourceCorrection

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


variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade solution weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive solution grade) (Icc lower 1))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive bounded.le 0 0
        (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data)).ofLp.1.ofLp.2)

include same allGrades smooth

/-- Actual original-data determinant equation on every punctured collar.
The only differential inputs are the genuine SAME Xi and corrected-p radial
laws, supplied by AKAK and AKBB. No source correction or mean is assumed. -/
theorem actualOriginalPolarDeterminant_from_radial (radius : ℝ) (inside : radius ∈ Ioo lower 1)
    (xiRadial : ∀ angles, HasDerivWithinAt
      (fun query => originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1 (query,angles))
      (((curves.lowPhysicalCurves parameters length compact lower positive bounded state 0).add (forces 0)).meanFree.fullField bounded (radius,angles))
      (Icc lower 1) radius)
    (pRadial : ∀ angles,
      scalarDirectionalField (curves.correctedP parameters length compact lower positive bounded state) bounded 0 (1,0,0) (radius,angles) =
      removePolarMean (fun query =>
        -(curves.correctedP parameters length compact lower positive bounded state).fullField bounded (radius,query) 0 / (radius : ℂ) -
        scalarDirectionalField (curves.bThree parameters length compact lower positive bounded state) bounded 0 (0,0,1) (radius,query) / (length : ℂ) -
        (curves.lowPhysicalCurves parameters length compact lower positive bounded state 2).fullField bounded (radius,query) 0 / (radius : ℂ) +
        third.fullField bounded (radius,query) 0) angles)
    (angles : ℝ × ℝ) :
    removePolarMean (polarDeterminantDivergence parameters length compact lower positive bounded state lengthPositive
      (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) solution curves radius) angles =
      (length : ℂ)⁻¹ * corePolarValue parameters (source 2) radius (positive.le.trans inside.1.le) inside.2.le angles 0 := by
  have closed : radius ∈ Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  let g := corePolarValue parameters (source 2) radius (positive.le.trans closed.1) closed.2
  have gContinuous : Continuous (fun query => g query 0) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp (corePolarValue_continuous parameters (source 2) radius (positive.le.trans closed.1) closed.2)
  have projected := sameProjectedDeterminant_from_radial parameters length compact lower positive bounded state lengthPositive
    (originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0 data) solution allGrades smooth curves (forces 0)
    radius inside (fun query => (length : ℂ)⁻¹ * g query 0) (continuous_const.mul gContinuous)
    (sameOriginalSource_radialMean parameters length compact lower positive bounded state lengthPositive source flat data same forces radius closed)
    xiRadial ?_ angles
  · apply projected.trans
    have sourceMean := congrArg (fun field : ℝ × ℝ → ComplexEuclidean 1 => field angles 0)
      (literalScalarSource_meanFree parameters source flat radius (positive.le.trans closed.1) closed.2)
    rw [removePolarMean_coordinate _ (corePolarValue_continuous parameters (source 2) radius (positive.le.trans closed.1) closed.2) angles] at sourceMean
    have scaled := congrFun (removePolarMean_smul (length : ℂ)⁻¹ (fun query => g query 0)) angles
    change removePolarMean (fun query => (length : ℂ)⁻¹ * g query 0) angles =
      (length : ℂ)⁻¹ * removePolarMean (fun query => g query 0) angles at scaled
    exact scaled.trans (congrArg ((length : ℂ)⁻¹ * ·) sourceMean)
  · intro query
    apply (pRadial query).trans
    apply congrArg (fun field : ℝ × ℝ → ℂ => removePolarMean field query)
    funext location
    have given := sameOriginalSource_third parameters length compact lower positive bounded state lengthPositive source flat data same solution curves forces third radius closed location
    have shifted := congrArg (fun value : ℂ =>
      -(curves.correctedP parameters length compact lower positive bounded state).fullField bounded (radius,location) 0 / (radius : ℂ) -
      scalarDirectionalField (curves.bThree parameters length compact lower positive bounded state) bounded 0 (0,0,1) (radius,location) / (length : ℂ) -
      (curves.lowPhysicalCurves parameters length compact lower positive bounded state 2).fullField bounded (radius,location) 0 / (radius : ℂ) + value) given
    exact shifted.trans (by dsimp only [g]; ring)

end Grad.ActualDeterminantEquations
