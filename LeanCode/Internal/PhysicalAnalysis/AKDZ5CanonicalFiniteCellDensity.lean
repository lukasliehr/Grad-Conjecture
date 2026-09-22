import AKDZ4OriginalPolarDensityIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.Constraints
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarCoefficients
open Grad.AnnularGeneralSourceRegularity Grad.OriginalCartesianTameEstimate

/-- One fixed collar/order constant, independent of the axial support,
original core and source payment. -/
def canonicalPolarDensityConstant (lower : ℝ) (grade : ℕ) : ℝ :=
  ∑ order∈Finset.range (grade+1),canonicalPolarTensorConstant lower order

theorem canonicalPolarDensityConstant_nonnegative (lower : ℝ) (grade : ℕ) :
    0≤canonicalPolarDensityConstant lower grade :=
  Finset.sum_nonneg (fun order _ => canonicalPolarTensorConstant_nonnegative lower order)

/-- Actual canonical Euler energies control the SAME original closed-jet
polar density over every finite axial support, after summing cells before
applying the full Fourier norm. This is the literal fixedCollarIntegral
input of the original planar cutoff estimate. -/
theorem canonicalFiniteCell_polarDensity {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (grade : ℕ)
    (core : ACore parameters dimension) (payment : ℝ) (paymentNonnegative : 0≤payment)
    (energy : ∀ power rank,power+rank≤grade →
      (∫⁻ radius in Icc lower 1,ENNReal.ofReal
        (‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (cartesianWeightedRadialCurve parameters lower positive bounded core power 0) radius‖^2))≤ENNReal.ofReal (payment^2))
    (cells : Finset ℤ) :
    (∑ cell∈cells,fixedCollarIntegral lower
      (polarJetSquaredDensity (smoothClosedExtension (phaseWeightedJet parameters cell (core.val cell)) ∘ collarPlane) grade))≤
      canonicalPolarDensityConstant lower grade*payment^2 := by
  simp_rw [fixedCollarIntegral_originalDensity_orders lower bounded]
  rw [Finset.sum_comm]
  have paid := Finset.sum_le_sum (s:=Finset.range (grade+1)) (fun order member =>
    canonicalPolarTensor_integral parameters lower positive bounded order core payment paymentNonnegative
      (fun power rank rankLe => energy power rank (rankLe.trans (by have := Finset.mem_range.mp member; omega))) cells)
  exact paid.trans_eq (by rw [←Finset.sum_mul]; rfl)

end Grad.OriginalCollarNorm
