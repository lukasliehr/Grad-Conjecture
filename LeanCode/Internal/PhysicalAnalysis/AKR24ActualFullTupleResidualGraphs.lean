import AKR23OriginalStrengthenedResidualGrade

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularHighTilt

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (tuple : OriginalSmoothTuple parameters lower)

/-- Actual full F1 bulk of the literal computed AH24 residual. -/
def tupleOriginalF1 : DivisionRow 1 lower :=
  coherentOriginalBulk lower positive bounded (tupleConjugatedF1Curve parameters length compact lower positive bounded state tuple)
    (tupleConjugatedF1Curve_continuous parameters length compact lower positive bounded state tuple)
    (tupleConjugatedF1Curve_grade parameters length compact lower positive bounded state tuple)

/-- Actual full G3 bulk with its original first angular weight. -/
def tupleOriginalG3 : DivisionRow 1 lower :=
  coherentOriginalBulk lower positive bounded (tupleStrengthenedG3Curve parameters length compact lower positive bounded state tuple)
    (tupleStrengthenedG3Curve_continuous parameters length compact lower positive bounded state tuple)
    (tupleStrengthenedG3Curve_grade parameters length compact lower positive bounded state tuple)

theorem tupleOriginalF1_physical :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode,
      originalF1Coefficient parameters lower positive bounded.le
        (tupleOriginalF1 parameters length compact lower positive bounded state tuple) radius mode =
        originalTupleF1 parameters length compact lower positive state tuple ⟨radius,inside⟩ mode := by
  apply coherentOriginalBulk_physical lower positive bounded _ _ _ parameters
    (originalTupleF1 parameters length compact lower positive state tuple)
  intro radius mode
  simpa only [pow_zero,Complex.ofReal_one,one_smul] using
    tupleConjugatedF1Curve_coefficient parameters length compact lower positive bounded state tuple 0 radius mode

theorem tupleOriginalG3_strengthened :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode,
      originalF1Coefficient parameters lower positive bounded.le
        (tupleOriginalG3 parameters length compact lower positive bounded state tuple) radius mode =
        ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) • originalTupleG3 parameters length compact lower positive state tuple ⟨radius,inside⟩ mode := by
  apply coherentOriginalBulk_physical lower positive bounded _ _ _ parameters
    (fun radius mode => ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) • originalTupleG3 parameters length compact lower positive state tuple radius mode)
  intro radius mode
  simpa only [pow_zero,Complex.ofReal_one,one_smul] using
    tupleStrengthenedG3Curve_coefficient parameters length compact lower positive bounded state tuple 0 radius mode

theorem tupleOriginalG3_physical :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode,
      originalG3Coefficient parameters lower positive bounded.le
        (tupleOriginalG3 parameters length compact lower positive bounded state tuple) radius mode =
        originalTupleG3 parameters length compact lower positive state tuple ⟨radius,inside⟩ mode := by
  filter_upwards [tupleOriginalG3_strengthened parameters length compact lower positive bounded state tuple,
    originalG3Coefficient_strengthened parameters lower positive bounded.le
      (tupleOriginalG3 parameters length compact lower positive bounded state tuple)] with radius actual strengthened
  intro inside mode
  apply smul_right_injective (ComplexEuclidean 1) (Complex.ofReal_ne_zero.mpr (by positivity : (1 + |(mode.1 : ℝ)|) ≠ 0))
  exact (strengthened mode).trans (actual inside mode)

end Grad.AnnularOriginalCoreRealization
