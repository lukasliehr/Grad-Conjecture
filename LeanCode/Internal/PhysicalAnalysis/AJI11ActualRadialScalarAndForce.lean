import AJI10ActualCofactorRadialSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularRadialSmoothness Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

theorem polynomialKernelAction_smul {source target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (scalar : ℂ) (kernel : FullTwoFrequencyKernel parameters source target) :
    polynomialKernelAction parameters power (fullKernelSmul scalar kernel) =
      scalar • polynomialKernelAction parameters power kernel := by
  apply polynomialObservation_ext parameters power
  intro field
  rw [← polynomialObservation_kernel, fullNegativeKernelAction_smul, map_smul,
    polynomialObservation_kernel]
  rfl

theorem smoothPolynomialFamily_radial_smul {source target : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {bounded : lower ≤ 1}
    {kernel : (radius : RadialPoint) → RadialKernel parameters radius source target}
    (smooth : SmoothPolynomialFamily parameters lower positive bounded kernel)
    (scalar : ℝ → ℂ) (scalarSmooth : ContDiffOn ℝ ∞ scalar (Icc lower 1)) :
    SmoothPolynomialFamily parameters lower positive bounded
      (fun r => fullKernelSmul (scalar r.val) (kernel r)) := by
  intro power
  apply (scalarSmooth.smul (smooth power)).congr
  intro radius inside
  change polynomialKernelAction _ power (fullKernelSmul _ _) = _
  rw [polynomialKernelAction_smul, collarRadius_literal lower positive bounded radius inside]
  rfl

variable (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem actualRetainedForce_smooth :
    SmoothPolynomialFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun r => radialRetainedForceKernel parameters length compact state.val.val r) := by
  have base := rowRadialJet_smooth parameters 3 lower positive bounded
    (fun order radius column => polarEntryScalar parameters
      (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field)
      (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
      0 column order radius)
    (fun order radius column mode => polarEntryScalar_hasDerivAt parameters _ _ 0 column order radius mode)
    (fun order r column moment => polarEntryScalarMoment_summable parameters _ _ 0 column moment order r.val r.property.1 r.property.2)
    (fun order moment column => ⟨_, fun r => polarEntryScalarMoment_bound parameters _ _ 0 column moment order r.val r.property.1 r.property.2⟩) 0
  have projection := smoothPolynomialFamily_fixed parameters lower positive bounded.le
    (fun p => coordinateProjectionKernel p 3 1) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  exact (smoothPolynomialFamily_radial_smul base (fun _ => 2) contDiffOn_const).add
    (smoothPolynomialFamily_radial_smul projection (fun _ => 2) contDiffOn_const)

theorem actualSignedCofactorRow_smooth (row : Fin 3) :
    SmoothPolynomialFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun r => radialSignedCofactorRowKernel parameters length compact state row r) := by
  have projection := smoothPolynomialFamily_fixed parameters lower positive bounded.le
    (fun p => coordinateProjectionKernel p 3 row) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  exact projection.neg.add (actualCofactorRow_smooth parameters length compact state lower positive bounded row 0 0)

theorem actualSignedCofactorComponent_smooth (row column : Fin 3) :
    SmoothPolynomialFamily (source := 1) (target := 1) parameters lower positive bounded.le
      (fun r => radialSignedCofactorComponentKernel parameters length compact state row column r) := by
  have fixed := smoothPolynomialFamily_fixed parameters lower positive bounded.le
    (fun p => circularCofactorComponentKernel p row column) (fun first second => sameCircularCofactorComponentKernel first second row column)
  exact fixed.add (actualCofactorComponent_smooth parameters length compact state lower positive bounded row column 0 0)

end Grad.AnnularSmoothCore
