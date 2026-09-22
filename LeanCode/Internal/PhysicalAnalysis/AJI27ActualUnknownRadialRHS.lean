import AJI26SameUnknownPhysicalRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularStrongSolution
open Grad.AnnularSourceGraph Grad.AnnularRadialSmoothness

def rawOriginalUnknownRHS (length radius : ℝ) (mode : ℤ × ℤ)
    (x j c v : ComplexEuclidean 1) : ComplexEuclidean 1 × ComplexEuclidean 1 :=
  ((-((radius : ℂ)⁻¹)) • x - (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • c) -
    (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • v),
    (if mode.1 = 0 then (0 : ℂ) else 1) • j)

theorem originalUnknown_frequency_algebra (length radius : ℝ) (mode : ℤ × ℤ) (grade : ℕ)
    (x j c v : ComplexEuclidean 1) :
    let weight := ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ)
    let next := ((annularFrequency mode.1 mode.2 ^ (grade + 1) : ℝ) : ℂ)
    let higher := ((annularFrequency mode.1 mode.2 ^ (grade + 2) : ℝ) : ℂ)
    ((-((radius : ℂ)⁻¹)) • (frequencyRatioSymbol none mode • (frequencyRatioSymbol none mode • (higher • x))) -
      (length : ℂ)⁻¹ • (frequencyRatioSymbol (some true) mode • (next • c)) -
      (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • (next • v)),
      (if mode.1 = 0 then (0 : ℂ) else 1) • (frequencyRatioSymbol none mode • (next • j))) =
      weight • rawOriginalUnknownRHS length radius mode x j c v := by
  dsimp only
  rw [frequencyRatio_weighted none mode (grade + 1)]
  simp only [frequencyNumerator, one_smul]
  rw [frequencyRatio_weighted, frequencyRatio_weighted, frequencyRatio_weighted, frequencyRatio_weighted]
  simp only [rawOriginalUnknownRHS, Prod.smul_mk, smul_sub, frequencyNumerator, one_smul]
  rw [smul_comm (-((radius : ℂ)⁻¹)) ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ),
    smul_comm ((length : ℂ)⁻¹) ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ),
    smul_comm ((radius : ℂ)⁻¹) ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ),
    smul_comm (if mode.1 = 0 then (0 : ℂ) else 1) ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ)]

variable (parameters : PhaseParameters) (lower length compact : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (field : CoupledSpace lower length positive lengthPositive)

theorem originalRadialSystemOperator_coefficient (grade : ℕ) (radius : ℝ) (input : PhysicalHilbertPair) (mode : ℤ × ℤ) :
    let row := fun index : Fin 3 => radialPolynomialAction parameters lower positive bounded.le
      (lowPhysicalRowKernel parameters length compact state index) (grade + 1) radius
      (rawUnknownSevenOperator parameters radius input) mode
    let output := originalRadialSystemOperator parameters length compact lower state positive bounded grade radius input
    (output.1 mode,output.2 mode) =
      ((-((radius : ℂ)⁻¹)) • (frequencyRatioSymbol none mode • (frequencyRatioSymbol none mode • input.1 mode)) -
        (length : ℂ)⁻¹ • (frequencyRatioSymbol (some true) mode • row 1) -
        (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • row 2),
        (if mode.1 = 0 then (0 : ℂ) else 1) • (frequencyRatioSymbol none mode • row 0)) := by
  dsimp only
  let row := fun index : Fin 3 => radialPolynomialAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state index) (grade + 1) radius
    (rawUnknownSevenOperator parameters radius input)
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  let outputX : CellL2 1 := (-((radius : ℂ)⁻¹)) • drop (drop input.1) -
    (length : ℂ)⁻¹ • axial (row 1) - (radius : ℂ)⁻¹ • angular (row 2)
  let outputXi : CellL2 1 := hilbertMeanFree parameters (drop (row 0))
  change ((outputX + 0) mode, (0 + outputXi) mode) = (outputX mode, outputXi mode)
  rw [add_zero, zero_add]

end Grad.AnnularSmoothCore
