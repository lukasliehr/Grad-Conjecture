import AKAC2ActualSevenAndCovariantCurves
import AKZ5ActualMatrixBulkAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set
open scoped BigOperators ContDiff
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularRadialSmoothness Grad.AnnularWeightedSmoothness
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualPhysicalField Grad.SourceCollarRestriction

 theorem matrixRadialJet_conjugated_smooth (parameters : PhaseParameters) (source target : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (coefficient : ℕ → ℝ → Fin target → Fin source → (ℤ × ℤ) → ℂ)
    (derivative : ∀ order radius row column mode, HasDerivAt (fun point => coefficient order point row column mode)
      (coefficient (order+1) radius row column mode) radius)
    (moments : ∀ order (r : RadialPoint) row column moment,
      Summable (productMoment parameters moment r.val (coefficient order r.val row column)))
    (bounds : ∀ order moment row column, ∃ constant : ℝ, ∀ r : RadialPoint,
      (∑' shift, productMoment parameters moment r.val (coefficient order r.val row column) shift) ≤ constant)
    (order : ℕ) :
    SmoothConjugatedFamily parameters lower positive bounded.le
      (fun r => radialMatrixKernel parameters r source target (coefficient order r.val) (moments order r)) := by
  have regular : ∀ order, RegularKernelFamily
      (fun r : RadialPoint => radialMatrixKernel parameters r source target (coefficient order r.val) (moments order r)) := by
    intro order
    choose constants estimates using bounds order
    refine regularKernelFamily_of_bound _ ?_
      (fun moment => Real.exp (parameters.sigma0 + 2 * parameters.gamma) * ∑ row, ∑ column, constants moment row column) ?_
    · intro shift input
      exact matrixMultiplicationEntry_continuous (X := RadialPoint) source target
        (fun r row column mode => coefficient order r.val row column mode)
        (fun row column mode => (continuous_iff_continuousAt.mpr
          (fun radius => (derivative order radius row column mode).continuousAt)).comp continuous_subtype_val) shift input
    · intro moment r
      exact (radialMatrixKernel_moment_le parameters r source target moment _ _).trans
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun row _ => Finset.sum_le_sum
          (fun column _ => estimates moment row column r))) (Real.exp_pos _).le)
  apply smoothConjugatedFamily_matrixJets parameters lower positive bounded
    (fun order r => radialMatrixKernel parameters r source target (coefficient order r.val) (moments order r))
    (fun order radius shift => matrixMultiplicationEntry source target (coefficient order radius) shift (0,0))
    (fun _ _ _ _ => rfl) _ regular order
  intro order shift radius
  exact matrixMultiplicationEntry_hasDerivAt source target _ _
    (fun row column point mode => derivative order point row column mode) radius shift (0,0)

variable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family)

theorem physicalMatrixScalar_hasDerivAt (row : Fin output) (column : Fin input)
    (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    HasDerivAt (fun point => physicalMatrixScalar parameters family coherent row column radial point mode)
      (physicalMatrixScalar parameters family coherent row column (radial+1) radius mode) radius :=
  ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin output => ℂ) row).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius
    (radialCoefficientJet_hasDerivAt _ (originalPolarValue_smooth
      (coefficientColumnJet parameters family coherent mode.2 (operatorBasis column))) mode.1 radial radius)

/-- The same original full matrix family, including F^-T, has finite-order
phase-conjugated regularity at its original analytic width. -/
theorem originalMatrixRadialKernel_conjugated_smooth (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    SmoothConjugatedFamily parameters lower positive bounded.le (originalMatrixRadialKernel parameters family coherent) := by
  exact matrixRadialJet_conjugated_smooth parameters input output lower positive bounded
    (fun order radius row column => physicalMatrixScalar parameters family coherent row column order radius)
    (fun order radius row column mode => physicalMatrixScalar_hasDerivAt parameters family coherent row column order radius mode)
    (fun order r row column moment => physicalMatrixScalar_moment_summable parameters family coherent row column moment order
      r.val r.property.1 r.property.2)
    (fun order moment row column => ⟨_,fun r => physicalMatrixScalar_moment_bound parameters family coherent row column moment order
      r.val r.property.1 r.property.2⟩) 0

end Grad.ActualSmoothPhysicalField
