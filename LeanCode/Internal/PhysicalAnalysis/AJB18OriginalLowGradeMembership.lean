import AJB17ActualFiniteDataOrbitSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal ContDiff
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit Grad.AnnularOrbitGenerators
open Grad.AnnularCoupledOrbit Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularReconstruction
open Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.PhaseAlgebra Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Physical.Allocation

/-- An actual, possibly unbounded Fourier multiplier belongs to the original
weak graph whenever both original stored coordinates are genuinely summable. -/
def lowSummableGraphMultiplier (lower length : ℝ) (positive : 0 < lower)
    (field : lowEnergyGraph lower length positive) (coefficient : LowAnnularIndex → ℂ)
    (summable : ∀ coordinate : Fin 2, Memℓp (fun index => coefficient index • field.val coordinate index) 2) :
    lowEnergyGraph lower length positive :=
  ⟨WithLp.toLp 2 (fun coordinate => ⟨fun index => coefficient index • field.val coordinate index, summable coordinate⟩), by
    intro index
    change CollarWeakDerivative lower
      (collarScalar 1 lower (lowStorageInverse lower positive) (coefficient index • field.val 0 index))
      (collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)
        (collarScalar 1 lower (lowStorageInverse lower positive) (coefficient index • field.val 1 index)))
    rw [map_smul, map_smul, map_smul]
    exact collarWeakDerivative_complex_smul lower (coefficient index) _ _ (field.property index)⟩

theorem cellGeneratorFactor_norm (mode : ℤ) (order : ℕ) :
    ‖(Complex.I * (mode : ℂ)) ^ order‖ = |(mode : ℝ)| ^ order := by
  rw [norm_pow, norm_mul, Complex.norm_I, one_mul]
  congr 1
  have cast : (mode : ℂ) = ((mode : ℝ) : ℂ) := by simp
  rw [cast, Complex.norm_real, Real.norm_eq_abs]

/-- Polynomial control from the actual derivative vector gives weighted lp
membership; the comparator is the original Hilbert norm of two real norm families. -/
theorem lowWeighted_memℓp_of_generator (lower : ℝ) (field generator : LowEnergyBulk lower)
    (order : ℕ) (actual : ∀ index, generator index = (Complex.I * (index.2.val.2 : ℂ)) ^ order • field index)
    (coefficient : LowAnnularIndex → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ index, |coefficient index| ≤ constant * (1 + |(index.2.val.2 : ℝ)| ^ order)) :
    Memℓp (fun index => (coefficient index : ℂ) • field index) 2 := by
  apply (lp.memℓp (constant • (lpNormFamily field + lpNormFamily generator))).mono'
  intro index
  change ‖(coefficient index : ℂ) • field index‖ ≤
    ‖constant • (‖field index‖ + ‖generator index‖)‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    norm_smul, Real.norm_of_nonneg nonnegative,
    Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
    actual index, norm_smul, cellGeneratorFactor_norm]
  exact (mul_le_mul_of_nonneg_right (bound index) (norm_nonneg _)).trans_eq (by ring)

theorem lowCellGrade_generator_bound (order : ℕ) (index : LowAnnularIndex) :
    |cellFrequency index.2.val.2 ^ order| ≤ (2 : ℝ) ^ order * (1 + |(index.2.val.2 : ℝ)| ^ order) := by
  rw [abs_of_nonneg (pow_nonneg (cellFrequency_pos _).le _)]
  apply (pow_le_pow_left₀ (cellFrequency_pos _).le (cellFrequency_le_abs_add_one _) order).trans
  simpa only [one_pow, add_comm] using Grad.BoundaryTrace.two_term_pow_bound
    |(index.2.val.2 : ℝ)| 1 (abs_nonneg _) (by norm_num) order

theorem lowGraph_originalCellGrade_of_generator (lower length : ℝ) (positive : 0 < lower)
    (field generator : lowEnergyGraph lower length positive) (order : ℕ)
    (actual : ∀ (coordinate : Fin 2) (index : LowAnnularIndex),
      generator.val coordinate index = (Complex.I * (index.2.val.2 : ℂ)) ^ order • field.val coordinate index) :
    ∃ weighted : lowEnergyGraph lower length positive, ∀ (coordinate : Fin 2) (index : LowAnnularIndex),
      weighted.val coordinate index = ((cellFrequency index.2.val.2 ^ order : ℝ) : ℂ) • field.val coordinate index := by
  have summable (coordinate : Fin 2) :
      Memℓp (fun index : LowAnnularIndex => ((cellFrequency index.2.val.2 ^ order : ℝ) : ℂ) • field.val coordinate index) 2 :=
    lowWeighted_memℓp_of_generator lower (field.val coordinate) (generator.val coordinate) order
      (actual coordinate) (fun index => cellFrequency index.2.val.2 ^ order) (2 ^ order) (by positivity)
      (lowCellGrade_generator_bound order)
  exact ⟨lowSummableGraphMultiplier lower length positive field
    (fun index => ((cellFrequency index.2.val.2 ^ order : ℝ) : ℂ)) summable, fun _ _ => rfl⟩

/-- Literal original AJ cell grade: Lambda_n^order on BOTH true graph
coordinates, without changing rho, analytic width, or radial normalization. -/
theorem actualLowSolution_originalCellGrade (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower)
    (dataSmooth : ContDiff ℝ ∞ (fun time : ℝ => lowDataTranslationEquivalence lower (0, time) data)) (order : ℕ) :
    ∃ weighted : lowEnergyGraph lower length positive, ∀ (coordinate : Fin 2) (index : LowAnnularIndex),
      weighted.val coordinate index = ((cellFrequency index.2.val.2 ^ order : ℝ) : ℂ) •
        (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val coordinate index := by
  exact lowGraph_originalCellGrade_of_generator lower length positive
    (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data)
    (actualLowSolutionCellGenerator parameters length compact lower lengthPositive positive bounded state data order) order
    (actualLowSolutionCellGenerator_coefficients parameters length compact lower lengthPositive positive bounded state small data dataSmooth order)

/-- Finite original data supply the grade without any assumed data or solution smoothness. -/
theorem lowFiniteDataInverse_originalCellGrade (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower) (support : Finset LowAnnularIndex)
    (bulkFinite : ∀ index, index ∉ support → data.ofLp.1 index = 0)
    (incomingFinite : ∀ index, index ∉ support → data.ofLp.2 index = 0) (order : ℕ) :
    ∃ weighted : lowEnergyGraph lower length positive, ∀ (coordinate : Fin 2) (index : LowAnnularIndex),
      weighted.val coordinate index = ((cellFrequency index.2.val.2 ^ order : ℝ) : ℂ) •
        (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val coordinate index :=
  actualLowSolution_originalCellGrade parameters length compact lower lengthPositive positive bounded state small data
    (lowFiniteDataOrbit_contDiff lower data support bulkFinite incomingFinite) order

end Grad.AnnularLowOrbit
