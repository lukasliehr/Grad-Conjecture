import AKBD10SameKVScalarExpression

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
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)

open Grad.ActualPolarFlux Grad.ActualCartesianEquations

variable {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- The actual unprojected AH23 retained numerator, using SAME coefficient
jets and the already constructed K_v field. -/
def retainedRVRawField (radius : ℝ) (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  (originalCofactorSmoothEntry parameters length compact state 1 1 radius angles •
      matrixUnit (0 : Fin 1) (1 : Fin 7) (curves.fullField bounded (radius,angles)) +
    ((curves.covariant parameters length compact lower positive bounded state.val).physicalKV parameters length compact lower positive bounded state).fullField bounded (radius,angles)) -
  (radius : ℂ) • (originalCofactorJetSeries parameters length compact state 1 0 1 0
    (collarRadius lower positive bounded.le radius) angles • matrixUnit (0 : Fin 1) (3 : Fin 7) (curves.fullField bounded (radius,angles))) -
  ((radius : ℂ) * (length : ℂ)⁻¹) • (originalCofactorJetSeries parameters length compact state 1 2 0 2
    (collarRadius lower positive bounded.le radius) angles • matrixUnit (0 : Fin 1) (3 : Fin 7) (curves.fullField bounded (radius,angles)))

theorem retainedRVRawField_continuous (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    Continuous (retainedRVRawField parameters length compact lower positive bounded state curves radius) := by
  let point : RadialPoint := ⟨radius,⟨positive.le.trans inside.1,inside.2⟩⟩
  have kappa := cofactorSmoothEntry_continuous_angles parameters length compact state 1 1 point
  have source := curves.fullField_continuous_angles bounded radius inside
  have one := (matrixUnit (0 : Fin 1) (1 : Fin 7)).continuous.comp source
  have q := (matrixUnit (0 : Fin 1) (3 : Fin 7)).continuous.comp source
  have kv := ((curves.covariant parameters length compact lower positive bounded state.val).physicalKV parameters length compact lower positive bounded state).fullField_continuous_angles bounded radius inside
  exact ((kappa.smul one).add kv).sub
    (((originalCofactorJetSeries_continuous parameters length compact state 1 0 1 0 _).smul q).const_smul (radius : ℂ)) |>.sub
    (((originalCofactorJetSeries_continuous parameters length compact state 1 2 0 2 _).smul q).const_smul ((radius : ℂ)*(length : ℂ)⁻¹))

/-- Exact scalar retained row with its outer P, after all full-cell products. -/
theorem sameRV_scalar (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.lowPhysicalCurves parameters length compact lower positive bounded state 2).fullField bounded (radius,angles) 0 =
      removePolarMean (fun query => retainedRVRawField parameters length compact lower positive bounded state curves radius query 0) angles := by
  let point : RadialPoint := ⟨radius,⟨positive.le.trans inside.1,inside.2⟩⟩
  have coefficient (query : ℝ × ℝ) := originalCofactorSmoothEntry_literal parameters length compact state 1 1 point query
  dsimp only [point] at coefficient
  have given := fullField_originalRV parameters length compact lower positive bounded state curves radius inside angles
  have same : (curves.lowPhysicalCurves parameters length compact lower positive bounded state 2).fullField bounded (radius,angles) =
      removePolarMean (retainedRVRawField parameters length compact lower positive bounded state curves radius) angles := by
    apply given.trans
    apply congrArg (fun field : ℝ × ℝ → ComplexEuclidean 1 => removePolarMean field angles)
    funext query
    simp only [retainedRVRawField,coefficient query]
  have scalar := congrArg (fun value : ComplexEuclidean 1 => value 0) same
  rw [removePolarMean_coordinate _ (retainedRVRawField_continuous parameters length compact lower positive bounded state curves radius inside) angles] at scalar
  exact scalar

theorem retainedRVRawField_scalar (radius : ℝ) (angles : ℝ × ℝ) :
    retainedRVRawField parameters length compact lower positive bounded state curves radius angles 0 =
      originalCofactorSmoothEntry parameters length compact state 1 1 radius angles * curves.fullField bounded (radius,angles) 1 +
      ((curves.covariant parameters length compact lower positive bounded state.val).physicalKV parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0 -
      (radius : ℂ) * originalCofactorJetSeries parameters length compact state 1 0 1 0 (collarRadius lower positive bounded.le radius) angles * curves.fullField bounded (radius,angles) 3 -
      ((radius : ℂ)*(length : ℂ)⁻¹) * originalCofactorJetSeries parameters length compact state 1 2 0 2 (collarRadius lower positive bounded.le radius) angles * curves.fullField bounded (radius,angles) 3 := by
  simp only [retainedRVRawField,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,matrixUnit_apply,operatorBasis]
  dsimp
  ring

end Grad.ActualDeterminantEquations
