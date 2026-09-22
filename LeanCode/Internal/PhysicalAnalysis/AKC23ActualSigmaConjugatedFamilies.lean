import AKC22ActualPrimitiveConjugatedFamilies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped BigOperators ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularRadialSmoothness

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)

theorem radialRotatedSigmaKernel_conjugated_smooth (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (order : ℕ) :
    SmoothConjugatedFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun radius => radialRotatedSigmaKernel parameters L compact state radius order) := by
  apply smoothConjugatedFamily_matrixJets parameters lower positive bounded
    (fun order radius => radialRotatedSigmaKernel parameters L compact state radius order)
    (fun order radius shift => rowMultiplicationEntry 3
      (fun component => angularCoefficientSequence (sigmaScalar parameters L state.data.rho state.data.epsilon state.data.field state.low component order radius)) shift (0,0))
    (fun _ _ _ _ => rfl) _ (rotatedSigmaJet_regular parameters L compact state) order
  intro order shift radius
  exact rowMultiplicationEntry_hasDerivAt 3 _ _
    (fun component point mode => (sigmaScalar_hasDerivAt parameters L state.data.rho state.data.epsilon
      state.data.field state.low component order point mode).const_mul _) radius shift (0,0)

/-- A scalar coefficient tower uses the same scalar multiplication kernel,
including its original moment norm and literal coefficient formula. -/
theorem scalarRadialJet_conjugated_smooth (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (coefficient : ℕ → ℝ → (ℤ × ℤ) → ℂ)
    (derivative : ∀ order radius mode, HasDerivAt (fun point => coefficient order point mode)
      (coefficient (order + 1) radius mode) radius)
    (moments : ∀ order (r : RadialPoint) moment, Summable (productMoment parameters moment r.val (coefficient order r.val)))
    (bounds : ∀ order moment, ∃ constant : ℝ, ∀ r : RadialPoint,
      (∑' shift, productMoment parameters moment r.val (coefficient order r.val) shift) ≤ constant)
    (order : ℕ) :
    SmoothConjugatedFamily (source := dimension) (target := dimension) parameters lower positive bounded.le
      (fun r => radialScalarKernel parameters r dimension (coefficient order r.val) (moments order r)) := by
  have regular : ∀ order, RegularKernelFamily
      (fun r : RadialPoint => radialScalarKernel parameters r dimension (coefficient order r.val) (moments order r)) := by
    intro order
    choose constants estimates using bounds order
    refine regularKernelFamily_of_bound _ ?_
      (fun moment => Real.exp (parameters.sigma0 + 2 * parameters.gamma) * constants moment) ?_
    · intro shift input
      have cont : Continuous (fun radius => coefficient order radius shift) :=
        continuous_iff_continuousAt.mpr (fun radius => (derivative order radius shift).continuousAt)
      exact (cont.comp continuous_subtype_val).smul continuous_const
    · intro moment r
      exact (radialScalarKernel_moment_le parameters r dimension moment _ _).trans
        (mul_le_mul_of_nonneg_left (estimates moment r) (Real.exp_pos _).le)
  apply smoothConjugatedFamily_matrixJets parameters lower positive bounded
    (fun order r => radialScalarKernel parameters r dimension (coefficient order r.val) (moments order r))
    (fun order radius shift => scalarMultiplicationEntry dimension (coefficient order radius) shift (0,0))
    (fun _ _ _ _ => rfl) _ regular order
  intro order shift radius
  exact (derivative order radius shift).smul_const (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension))

theorem radialSigmaComponentKernel_conjugated_smooth (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (component : Fin 3) :
    SmoothConjugatedFamily (source := 1) (target := 1) parameters lower positive bounded.le
      (fun radius => radialSigmaComponentKernel parameters L compact state radius component) := by
  apply scalarRadialJet_conjugated_smooth parameters 1 lower positive bounded
    (fun order radius => sigmaScalar parameters L state.rho state.epsilon state.field state.low component order radius)
    (fun order radius mode => sigmaScalar_hasDerivAt parameters L state.rho state.epsilon state.field state.low component order radius mode)
    (fun order r moment => radialSigmaCoefficients_moments parameters L compact state r component order moment) _ 0
  intro order moment
  exact ⟨_, fun r => radialSigmaCoefficients_bound parameters L compact state r component order moment⟩

theorem radialRotatedSigmaComponentKernel_conjugated_smooth (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (component : Fin 3) :
    SmoothConjugatedFamily (source := 1) (target := 1) parameters lower positive bounded.le
      (fun radius => radialRotatedSigmaComponentKernel parameters L compact state radius component) := by
  apply scalarRadialJet_conjugated_smooth parameters 1 lower positive bounded
    (fun order radius => angularCoefficientSequence (sigmaScalar parameters L state.rho state.epsilon state.field state.low component order radius))
    (fun order radius mode => (sigmaScalar_hasDerivAt parameters L state.rho state.epsilon state.field state.low component order radius mode).const_mul _)
    (fun order r moment => (sigmaAngularScalarMoment_bound parameters L state.rho state.epsilon state.field state.low component moment order r.val r.property.1 r.property.2).1) _ 0
  intro order moment
  exact ⟨_, fun r => (sigmaAngularScalarMoment_bound parameters L state.rho state.epsilon state.field state.low component moment order r.val r.property.1 r.property.2).2⟩


end Grad.AnnularWeightedSmoothness
