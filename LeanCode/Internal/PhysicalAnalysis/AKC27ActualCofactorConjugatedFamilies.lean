import AKC26SameMassAndReconstructionConjugatedFamilies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped BigOperators ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularRadialSmoothness Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularSmoothCore

theorem rowRadialJet_conjugated_smooth (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (coefficient : ℕ → ℝ → Fin dimension → (ℤ × ℤ) → ℂ)
    (derivative : ∀ order radius column mode, HasDerivAt (fun point => coefficient order point column mode)
      (coefficient (order + 1) radius column mode) radius)
    (moments : ∀ order (r : RadialPoint) column moment,
      Summable (productMoment parameters moment r.val (coefficient order r.val column)))
    (bounds : ∀ order moment column, ∃ constant : ℝ, ∀ r : RadialPoint,
      (∑' shift, productMoment parameters moment r.val (coefficient order r.val column) shift) ≤ constant)
    (order : ℕ) :
    SmoothConjugatedFamily (source := dimension) (target := 1) parameters lower positive bounded.le
      (fun r => radialRowKernel parameters r dimension (coefficient order r.val) (moments order r)) := by
  have regular : ∀ order, RegularKernelFamily
      (fun r : RadialPoint => radialRowKernel parameters r dimension (coefficient order r.val) (moments order r)) := by
    intro order
    choose constants estimates using bounds order
    refine regularKernelFamily_of_bound _ ?_
      (fun moment => Real.exp (parameters.sigma0 + 2 * parameters.gamma) * ∑ column, constants moment column) ?_
    · intro shift input
      exact rowMultiplicationEntry_continuous (X := RadialPoint) dimension
        (fun r column mode => coefficient order r.val column mode)
        (fun column mode => (continuous_iff_continuousAt.mpr
          (fun radius => (derivative order radius column mode).continuousAt)).comp continuous_subtype_val) shift input
    · intro moment r
      exact (radialRowKernel_moment_le parameters r dimension moment _ _).trans
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun column _ => estimates moment column r)) (Real.exp_pos _).le)
  apply smoothConjugatedFamily_matrixJets parameters lower positive bounded
    (fun order r => radialRowKernel parameters r dimension (coefficient order r.val) (moments order r))
    (fun order radius shift => rowMultiplicationEntry dimension (coefficient order radius) shift (0,0))
    (fun _ _ _ _ => rfl) _ regular order
  intro order shift radius
  exact rowMultiplicationEntry_hasDerivAt dimension _ _
    (fun column point mode => derivative order point column mode) radius shift (0,0)

variable (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact)

theorem actualCofactorRow_conjugated_smooth (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (row : Fin 3) (radial : Fin 2) (direction : Fin 3) :
    SmoothConjugatedFamily (source := 3) (target := 1) parameters lower positive bounded.le
      (fun r => radialCofactorJetRowKernel parameters length compact state row radial direction r) := by
  exact rowRadialJet_conjugated_smooth parameters 3 lower positive bounded
    (fun order radius column => actualCofactorRadialScalar parameters length compact state row column direction order radius)
    (fun order radius column mode => actualCofactorRadialScalar_derivative parameters length compact state row column direction order radius mode)
    (fun order r column moment => actualCofactorRadialScalar_moments parameters length compact state row column direction order r moment)
    (fun order moment column => actualCofactorRadialScalar_bounds parameters length compact state row column direction order moment) radial.val

theorem actualCofactorComponent_conjugated_smooth (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (row column : Fin 3) (radial : Fin 2) (direction : Fin 3) :
    SmoothConjugatedFamily (source := 1) (target := 1) parameters lower positive bounded.le
      (fun r => radialCofactorJetComponentKernel parameters length compact state row column radial direction r) := by
  exact scalarRadialJet_conjugated_smooth parameters 1 lower positive bounded
    (actualCofactorRadialScalar parameters length compact state row column direction)
    (actualCofactorRadialScalar_derivative parameters length compact state row column direction)
    (actualCofactorRadialScalar_moments parameters length compact state row column direction)
    (actualCofactorRadialScalar_bounds parameters length compact state row column direction) radial.val


end Grad.AnnularWeightedSmoothness
