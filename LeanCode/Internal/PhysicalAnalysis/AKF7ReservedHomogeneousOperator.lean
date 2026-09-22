import AKF6SameWeightedFieldReserves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2 Grad.BoundaryKernelAction

/-- Composition by a fixed input reserve leaves the actual kernel unchanged. -/
theorem radialConjugatedAction_compReserve {source target : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (grade reserve : ℕ) (radius : ℝ) (field : CellL2 source) :
    radialConjugatedAction parameters lower positive bounded kernel grade 0 radius
      (hilbertReserve parameters source reserve field) =
      radialConjugatedAction parameters lower positive bounded kernel grade reserve radius field := by
  have zero := hilbertReserve_same parameters source 0
    (hilbertReserve parameters source reserve field) (hilbertReserve parameters source reserve field)
    (fun mode => by rw [pow_zero, one_smul])
  change bulkKernelAction parameters grade _ _ (hilbertReserve parameters source 0
      (hilbertReserve parameters source reserve field)) =
    bulkKernelAction parameters grade _ _ (hilbertReserve parameters source reserve field)
  rw [zero]

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (state : RetainedInverseState parameters length compact)
    (positive : 0 < lower) (bounded : lower < 1)

/-- Finite-order realization of the homogeneous operator using any requested
input reserve, retaining the same original-width kernel in all three rows. -/
def reservedConjugatedRadialSystemOperator (grade reserve : ℕ) (radius : ℝ) :
    PhysicalHilbertPair →L[ℂ] PhysicalHilbertPair :=
  let input := rawUnknownSevenOperator parameters radius
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  let row := fun row : Fin 3 => radialConjugatedAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) (grade + 1) reserve radius
  let xiDerivative := (hilbertMeanFree parameters).comp (drop.comp ((row 0).comp input))
  let xDerivative :=
    (-((radius : ℂ)⁻¹)) • drop.comp (drop.comp
      ((ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1)).comp (physicalPairReserve parameters reserve))) -
    (length : ℂ)⁻¹ • axial.comp ((row 1).comp input) -
    (radius : ℂ)⁻¹ • angular.comp ((row 2).comp input)
  xDerivative.prod xiDerivative

theorem reservedConjugatedRadialSystemOperator_same (grade reserve : ℕ) (radius : ℝ)
    (field : PhysicalHilbertPair) :
    reservedConjugatedRadialSystemOperator parameters length compact lower state positive bounded grade reserve radius field =
      conjugatedRadialSystemOperator parameters length compact lower state positive bounded grade radius
        (physicalPairReserve parameters reserve field) := by
  have rowSame (index : Fin 3) :
      radialConjugatedAction parameters lower positive bounded.le
        (lowPhysicalRowKernel parameters length compact state index) (grade + 1) 0 radius
        (rawUnknownSevenOperator parameters radius (physicalPairReserve parameters reserve field)) =
      radialConjugatedAction parameters lower positive bounded.le
        (lowPhysicalRowKernel parameters length compact state index) (grade + 1) reserve radius
        (rawUnknownSevenOperator parameters radius field) := by
    have inputSame := congrArg (fun mapping : PhysicalHilbertPair →L[ℂ] CellL2 7 => mapping field)
      (rawUnknownSevenOperator_reserve parameters reserve radius)
    change rawUnknownSevenOperator parameters radius (physicalPairReserve parameters reserve field) =
      hilbertReserve parameters 7 reserve (rawUnknownSevenOperator parameters radius field) at inputSame
    rw [inputSame]
    exact radialConjugatedAction_compReserve parameters lower positive bounded.le
      (lowPhysicalRowKernel parameters length compact state index) (grade + 1) reserve radius _
  let input := rawUnknownSevenOperator parameters radius (physicalPairReserve parameters reserve field)
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  let row := fun index : Fin 3 => radialConjugatedAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state index) (grade + 1) 0 radius input
  let outputX := (-((radius : ℂ)⁻¹)) • drop (drop (physicalPairReserve parameters reserve field).1) -
    (length : ℂ)⁻¹ • axial (row 1) - (radius : ℂ)⁻¹ • angular (row 2)
  let outputXi := hilbertMeanFree parameters (drop (row 0))
  change _ = (outputX + 0, 0 + outputXi)
  rw [add_zero, zero_add]
  dsimp only [outputX, outputXi, row, input]
  rw [rowSame 0, rowSame 1, rowSame 2]
  rfl

end Grad.AnnularWeightedSystem
