import AKI36LiteralTupleOriginalEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularCurrentSource Grad.AnnularCurrentLow Grad.AnnularStrongOrbit Grad.AnnularHighTilt Grad.AnnularVariational Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Vanishing original physical coefficients force the original full source
coordinate to satisfy its mean constraint. -/
theorem originalF1Coefficient_mask (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (source : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      originalF1Coefficient parameters lower positive bounded (sourceMeanFreeLp source) radius mode =
        if mode.1 = 0 then 0 else originalF1Coefficient parameters lower positive bounded source radius mode := by
  filter_upwards [Lp.coeFn_zero (ComplexEuclidean 1) 2 (volume.restrict (Icc lower 1))] with radius zero
  have zeroValue : (0 : RadialL2 1 lower) radius = 0 := zero
  intro mode
  unfold originalF1Coefficient lowRhoPhysicalCoefficient
  rw [divisionHighWeight_mode,sourceMeanFreeLp_apply]
  by_cases mean : mode.1 = 0
  · rw [if_pos mean,map_zero,zeroValue,smul_zero,if_pos mean]
  · rw [if_neg mean,if_neg mean,divisionHighWeight_mode]

theorem sourceMeanFree_of_physicalZero (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (source : DivisionRow 1 lower)
    (zero : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ cell,
      originalF1Coefficient parameters lower positive bounded source radius (0,cell) = 0) :
    sourceMeanFreeLp source = source := by
  apply originalF1Coefficient_faithful parameters lower positive bounded
  filter_upwards [originalF1Coefficient_mask parameters lower positive bounded source,zero] with radius masked vanishing
  intro mode
  rw [masked mode]
  by_cases mean : mode.1 = 0
  · rw [if_pos mean]
    have modeSame : mode = (0,mode.2) := Prod.ext mean rfl
    rw [modeSame,vanishing mode.2]
  · rw [if_neg mean]

/-- Mean-free literal fields have mean-free genuine radial derivatives. -/
theorem originalTuple_derivative_meanFree (parameters : PhaseParameters) (lower : ℝ) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4) (mean : slot ≠ 2)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (cell : ℤ) :
    derivWithin (fun location => originalPhysicalCoefficient (tuple.val slot) location (0,cell)) (Icc lower 1) radius = 0 := by
  have zeroDerivative : HasDerivWithinAt
      (fun location => originalPhysicalCoefficient (tuple.val slot) location (0,cell)) 0 (Icc lower 1) radius := by
    apply (hasDerivWithinAt_const radius (Icc lower 1) (0 : ComplexEuclidean 1)).congr
    · intro location member
      exact tuple.property.2 slot mean location member cell
    · exact tuple.property.2 slot mean radius inside cell
  exact zeroDerivative.derivWithin (uniqueDiffOn_Icc bounded radius inside)

/-- Both computed AH24 residuals have the original zero angular mean;
this is a consequence of the four literal fields. -/
theorem originalTuple_residual_meanFree (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    (tuple : OriginalSmoothTuple parameters lower) (radius : Icc lower (1 : ℝ)) (cell : ℤ) :
    originalTupleF1 parameters length compact lower positive state tuple radius (0,cell) = 0 ∧
      originalTupleG3 parameters length compact lower positive state tuple radius (0,cell) = 0 := by
  have xiZero := originalTuple_derivative_meanFree parameters lower bounded tuple 1 (by decide) radius.val radius.property cell
  have pZero := originalTuple_derivative_meanFree parameters lower bounded tuple 0 (by decide) radius.val radius.property cell
  have pValue := tuple.property.2 0 (by decide) radius.val radius.property cell
  constructor
  · simp only [originalTupleF1,xiZero,angularMeanFreeMultiplier,ite_true,zero_smul,sub_zero]
  · simp only [originalTupleG3,pZero,pValue,angularMeanFreeMultiplier,ite_true,zero_smul,smul_zero,zero_add]
    exact tupleVTrace_meanFree parameters length compact lower positive state tuple radius cell

end Grad.AnnularOriginalSmoothCore
