import AKBD18LiteralDeterminantSourceCorrection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
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
open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade solution weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive solution grade) (Icc lower 1))
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))
    (force : SmoothLowPhysicalRow parameters lower positive (strongKnownBulk parameters lower positive bounded.le data 3))



theorem fullScalarField_continuous_angles {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (component : Fin dimension) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    Continuous (fun angles => curves.fullField bounded (radius,angles) component) :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin dimension => ℂ) component).continuous.comp
    (curves.fullField_continuous_angles bounded radius inside)

theorem sameDeterminantSourceCorrection_continuous (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    Continuous (sameDeterminantSourceCorrection parameters length compact lower positive bounded state lengthPositive data solution curves force radius) := by
  let point : RadialPoint := ⟨radius,positive.le.trans inside.1,inside.2⟩
  have coefficient := cofactorSmoothEntry_continuous_angles parameters length compact state 1
  exact (((coefficient 0 point).mul (fullScalarField_continuous_angles force bounded 0 radius inside)).add
    ((coefficient 1 point).mul (fullScalarField_continuous_angles curves bounded 4 radius inside))).sub
    ((coefficient 2 point).mul (fullScalarField_continuous_angles curves bounded 6 radius inside)) |>.div_const (radius : ℂ)

theorem polarDeterminantDivergence_continuous (radius : ℝ) (inside : radius ∈ Ioo lower 1) :
    Continuous (polarDeterminantDivergence parameters length compact lower positive bounded state lengthPositive data solution curves radius) := by
  let flux := polarCofactorFluxCurves parameters length compact lower positive bounded state curves
  exact ((scalarDirectionalField_continuous_angles (flux 0) bounded 0 (1,0,0) radius inside).add
    ((fullScalarField_continuous_angles (flux 0) bounded 0 radius ⟨inside.1.le,inside.2.le⟩).div_const (radius : ℂ))).add
    ((scalarDirectionalField_continuous_angles (flux 1) bounded 0 (0,1,0) radius inside).div_const (radius : ℂ)) |>.add
    ((scalarDirectionalField_continuous_angles (flux 2) bounded 0 (0,0,1) radius inside).div_const (length : ℂ))

include allGrades smooth

/-- The SAME corrected-p radial law implies the exact signed projected
polar determinant divergence. Both differential laws are explicit inputs
here; the original-equation wrapper supplies them without new PDE assumptions. -/
theorem sameProjectedDeterminant_from_radial (radius : ℝ) (inside : radius ∈ Ioo lower 1)
    (source : ℝ × ℝ → ℂ) (sourceContinuous : Continuous source)
    (sourceMean : ∀ angles, removePolarMean (fun query => force.fullField bounded (radius,query) 0) angles = force.fullField bounded (radius,angles) 0)
    (xiRadial : ∀ angles, HasDerivWithinAt
      (fun query => originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1 (query,angles))
      (((curves.lowPhysicalCurves parameters length compact lower positive bounded state 0).add force).meanFree.fullField bounded (radius,angles))
      (Icc lower 1) radius)
    (pRadial : ∀ angles,
      scalarDirectionalField (curves.correctedP parameters length compact lower positive bounded state) bounded 0 (1,0,0) (radius,angles) =
      removePolarMean (fun query =>
        -(curves.correctedP parameters length compact lower positive bounded state).fullField bounded (radius,query) 0 / (radius : ℂ) -
        scalarDirectionalField (curves.bThree parameters length compact lower positive bounded state) bounded 0 (0,0,1) (radius,query) / (length : ℂ) -
        (curves.lowPhysicalCurves parameters length compact lower positive bounded state 2).fullField bounded (radius,query) 0 / (radius : ℂ) +
        source query + removePolarMean (sameDeterminantSourceCorrection parameters length compact lower positive bounded state lengthPositive data solution curves force radius) query) angles)
    (angles : ℝ × ℝ) :
    removePolarMean (polarDeterminantDivergence parameters length compact lower positive bounded state lengthPositive data solution curves radius) angles =
      removePolarMean source angles := by
  have closed : radius ∈ Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  let rawCurve := rawCorrectedPCurves parameters length compact lower positive bounded state curves
  let raw : C(ℝ × ℝ,ℂ) := ⟨fun query => rawCurve.fullField bounded (radius,query) 0,
    fullScalarField_continuous_angles rawCurve bounded 0 radius closed⟩
  let rawRadial : C(ℝ × ℝ,ℂ) := ⟨fun query => scalarDirectionalField rawCurve bounded 0 (1,0,0) (radius,query),
    scalarDirectionalField_continuous_angles rawCurve bounded 0 (1,0,0) radius inside⟩
  let thirdAxial : C(ℝ × ℝ,ℂ) := ⟨fun query => scalarDirectionalField (curves.bThree parameters length compact lower positive bounded state) bounded 0 (0,0,1) (radius,query),
    scalarDirectionalField_continuous_angles _ bounded 0 (0,0,1) radius inside⟩
  let retained : C(ℝ × ℝ,ℂ) := ⟨fun query => retainedRVRawField parameters length compact lower positive bounded state curves radius query 0,
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp (retainedRVRawField_continuous parameters length compact lower positive bounded state curves radius closed)⟩
  have retainedValue : (retained : ℝ × ℝ → ℂ) = fun query => retainedRVRawField parameters length compact lower positive bounded state curves radius query 0 := rfl
  let correction : C(ℝ × ℝ,ℂ) := ⟨sameDeterminantSourceCorrection parameters length compact lower positive bounded state lengthPositive data solution curves force radius,
    sameDeterminantSourceCorrection_continuous parameters length compact lower positive bounded state lengthPositive data solution curves force radius closed⟩
  let original : C(ℝ × ℝ,ℂ) := ⟨source,sourceContinuous⟩
  let divergence : C(ℝ × ℝ,ℂ) := ⟨polarDeterminantDivergence parameters length compact lower positive bounded state lengthPositive data solution curves radius,
    polarDeterminantDivergence_continuous parameters length compact lower positive bounded state lengthPositive data solution curves radius inside⟩
  have expansion : rawRadial+(radius : ℂ)⁻¹ • raw+(length : ℂ)⁻¹ • thirdAxial+(radius : ℂ)⁻¹ • retained-correction=divergence := by
    ext query
    have actual := sameDeterminant_productExpansion parameters length compact lower positive bounded state lengthPositive data solution allGrades smooth curves force
      radius inside query.1 query.2 (xiRadial query) (sourceMean query)
    simpa [raw,rawCurve,rawRadial,thirdAxial,retainedValue,correction,divergence,ContinuousMap.coe_add,ContinuousMap.coe_sub,
      ContinuousMap.coe_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.add_def,Pi.sub_def,Pi.smul_def,Pi.neg_def,smul_eq_mul,div_eq_mul_inv,mul_comm] using actual
  have law : polarMeanFreeLinearMap rawRadial = polarMeanFreeLinearMap
      (-(radius : ℂ)⁻¹ • polarMeanFreeLinearMap raw-(length : ℂ)⁻¹ • thirdAxial-(radius : ℂ)⁻¹ • polarMeanFreeLinearMap retained+original+polarMeanFreeLinearMap correction) := by
    ext query
    have actual := pRadial query
    rw [correctedP_radial_projected parameters length compact lower positive bounded state curves radius inside query.1 query.2] at actual
    simp_rw [correctedP_projection_same parameters length compact lower positive bounded state curves radius closed,
      sameRV_scalar parameters length compact lower positive bounded state curves radius closed] at actual
    simpa [polarMeanFreeLinearMap,raw,rawCurve,rawRadial,thirdAxial,retainedValue,correction,original,ContinuousMap.coe_add,ContinuousMap.coe_sub,
      ContinuousMap.coe_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.add_def,Pi.sub_def,Pi.smul_def,Pi.neg_def,smul_eq_mul,div_eq_mul_inv,mul_comm,neg_mul,mul_neg] using actual
  exact congrArg (fun field : C(ℝ × ℝ,ℂ) => field angles)
    (projectedDeterminant_residual polarMeanFreeLinearMap polarMeanFreeLinearMap_idempotent
      (radius : ℂ)⁻¹ (length : ℂ)⁻¹ raw rawRadial thirdAxial retained correction original divergence expansion law)

end Grad.ActualDeterminantEquations
