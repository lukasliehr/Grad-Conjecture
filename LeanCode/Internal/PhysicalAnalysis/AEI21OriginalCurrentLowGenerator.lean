import AEI20CompletedCircularLowResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

open Grad.PhaseAlgebra

/-- Exact completed identification with the already accepted BE10 operator.
It includes the original phase derivative and both geometric diagonal terms. -/
theorem lowCommonDiagonal_add_circular (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1) :
    lowCommonDiagonal parameters length lower lengthPositive positive +
      lowCircularResponse parameters length lower lengthPositive positive bounded =
        lowReferenceBulk parameters length lower lengthPositive positive := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext index
  apply Lp.ext
  filter_upwards [lowCommonDiagonal_ae parameters length lower lengthPositive positive field index,
    lowCircularResponse_ae parameters length lower lengthPositive positive bounded field index,
    lowReferenceBulk_ae parameters length lower lengthPositive positive field index,
    Lp.coeFn_add (lowCommonDiagonal parameters length lower lengthPositive positive field index)
      (lowCircularResponse parameters length lower lengthPositive positive bounded field index),
    ae_restrict_mem measurableSet_Icc] with radius diagonal circular reference additive inside
  change (lowCommonDiagonal parameters length lower lengthPositive positive field index +
    lowCircularResponse parameters length lower lengthPositive positive bounded field index) radius = _
  rw [additive]
  simp only [Pi.add_apply]
  rw [diagonal, circular, reference]
  have muzero : (lowMu length radius index.2.val.2 : ℂ) ≠ 0 := by
    exact_mod_cast (lowMu_pos length radius index.2.val.2 (positive.trans_le inside.1)).ne'
  have azero : (lowAmplitude length parameters.gamma index.2 : ℂ) ≠ 0 := by
    exact_mod_cast (lowAmplitude_pos length parameters.gamma index.2).ne'
  rcases index with ⟨row, mode⟩
  have cases : row = 0 ∨ row = 1 := by omega
  rcases cases with rfl | rfl
  · simp only [ite_true]
    apply PiLp.ext
    intro slot
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Complex.real_smul]
    simp only [lowReferenceMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
      lowReferenceUpper_conjugation length parameters.gamma radius mode]
    push_cast
    field_simp [muzero]
    ring
  · simp only [Fin.reduceEq, ite_false]
    apply PiLp.ext
    intro slot
    simp only [PiLp.add_apply, PiLp.smul_apply, Complex.real_smul]
    simp only [lowReferenceMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
      lowReferenceLower_conjugation length parameters.gamma radius mode (positive.trans_le inside.1)]
    push_cast
    field_simp [muzero, azero]
    ring

/-- The actual normalized current low generator, built from the physical
pre-Q rows, without an assumed perturbation or free trace coordinates. -/
def lowCurrentBulk (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) : LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  lowCommonDiagonal parameters length lower lengthPositive positive +
    lowPhysicalResponse parameters length compact lower lengthPositive positive bounded state

theorem lowCurrentBulk_reference_error (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) :
    lowCurrentBulk parameters length compact lower lengthPositive positive bounded state =
      lowReferenceBulk parameters length lower lengthPositive positive +
        lowPhysicalResponseError parameters length compact lower lengthPositive positive bounded state := by
  rw [← lowCommonDiagonal_add_circular parameters length lower lengthPositive positive bounded,
    lowPhysicalResponseError_sub, lowCurrentBulk]
  abel

end Grad.AnnularCurrentLow
