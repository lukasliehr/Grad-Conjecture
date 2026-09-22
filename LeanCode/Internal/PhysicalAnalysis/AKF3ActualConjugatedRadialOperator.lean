import AKF2SameConjugatedUnknownRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

/-- Literal bounded polynomial-frequency formula for the homogeneous
radial RHS, used only to transport the same common original phase. -/
def conjugatedUnknownPointRHS (length radius : ℝ) (mode : ℤ × ℤ)
    (x j c v : ComplexEuclidean 1) : ComplexEuclidean 1 × ComplexEuclidean 1 :=
  ((-((radius : ℂ)⁻¹)) • (frequencyRatioSymbol none mode • (frequencyRatioSymbol none mode • x)) -
    (length : ℂ)⁻¹ • (frequencyRatioSymbol (some true) mode • c) -
    (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • v),
    (if mode.1 = 0 then (0 : ℂ) else 1) • (frequencyRatioSymbol none mode • j))

theorem conjugatedUnknownPointRHS_smul (length radius : ℝ) (mode : ℤ × ℤ)
    (scalar : ℂ) (x j c v : ComplexEuclidean 1) :
    conjugatedUnknownPointRHS length radius mode (scalar • x) (scalar • j) (scalar • c) (scalar • v) =
      scalar • conjugatedUnknownPointRHS length radius mode x j c v := by
  apply Prod.ext <;> apply PiLp.ext <;> intro entry
  · simp only [conjugatedUnknownPointRHS, Prod.smul_mk, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · simp only [conjugatedUnknownPointRHS, Prod.smul_mk, PiLp.smul_apply, smul_eq_mul]
    ring

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (state : RetainedInverseState parameters length compact)
    (positive : 0 < lower) (bounded : lower < 1)

/-- The actual original-width homogeneous radial operator in weighted
coordinates. No regularity of this operator is assumed in its definition. -/
def conjugatedRadialSystemOperator (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair →L[ℂ] PhysicalHilbertPair :=
  let input := rawUnknownSevenOperator parameters radius
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  let row := fun row : Fin 3 => radialConjugatedAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) (grade + 1) 0 radius
  let xiDerivative := (hilbertMeanFree parameters).comp (drop.comp ((row 0).comp input))
  let xDerivative :=
    (-((radius : ℂ)⁻¹)) • drop.comp (drop.comp (ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1))) -
    (length : ℂ)⁻¹ • axial.comp ((row 1).comp input) -
    (radius : ℂ)⁻¹ • angular.comp ((row 2).comp input)
  (ContinuousLinearMap.inl ℂ (CellL2 1) (CellL2 1)).comp xDerivative +
    (ContinuousLinearMap.inr ℂ (CellL2 1) (CellL2 1)).comp xiDerivative

theorem conjugatedRadialSystemOperator_coefficient (grade : ℕ) (radius : ℝ)
    (input : PhysicalHilbertPair) (mode : ℤ × ℤ) :
    let row := fun index : Fin 3 => radialConjugatedAction parameters lower positive bounded.le
      (lowPhysicalRowKernel parameters length compact state index) (grade + 1) 0 radius
      (rawUnknownSevenOperator parameters radius input) mode
    hilbertPairCoefficient mode
      (conjugatedRadialSystemOperator parameters length compact lower state positive bounded grade radius input) =
      conjugatedUnknownPointRHS length radius mode (input.1 mode) (row 0) (row 1) (row 2) := by
  dsimp only
  let row := fun index : Fin 3 => radialConjugatedAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state index) (grade + 1) 0 radius
    (rawUnknownSevenOperator parameters radius input)
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  let outputX : CellL2 1 := (-((radius : ℂ)⁻¹)) • drop (drop input.1) -
    (length : ℂ)⁻¹ • axial (row 1) - (radius : ℂ)⁻¹ • angular (row 2)
  let outputXi : CellL2 1 := hilbertMeanFree parameters (drop (row 0))
  change ((outputX + 0) mode, (0 + outputXi) mode) = (outputX mode, outputXi mode)
  rw [add_zero, zero_add]

end Grad.AnnularWeightedSystem
