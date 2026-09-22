import FiniteRowMultiplier

noncomputable section

namespace Grad.TensorBootstrap

open Grad.PDEBootstrap Grad.SobolevBridge MeasureTheory

abbrev TensorIndex := Fin 2 × Fin 2

def tensorSymbol (index : TensorIndex) : Spatial → ℂ :=
  firstHalfSymbol index.1 * firstHalfSymbol index.2

theorem tensorSymbol_temperate (index : TensorIndex) : (tensorSymbol index).HasTemperateGrowth :=
  (firstHalfSymbol_temperate index.1).mul (firstHalfSymbol_temperate index.2)

theorem tensorSymbol_norm_le (index : TensorIndex) (frequency : Spatial) : ‖tensorSymbol index frequency‖ ≤ 1 := by
  rw [tensorSymbol, Pi.mul_apply, norm_mul]
  simpa only [one_mul] using mul_le_mul (firstHalfSymbol_norm_le index.1 frequency)
    (firstHalfSymbol_norm_le index.2 frequency) (norm_nonneg _) zero_le_one

theorem tensorSymbol_memLp (index : TensorIndex) : MemLp (tensorSymbol index) ⊤ (volume : Measure Spatial) :=
  ⟨(tensorSymbol_temperate index).1.continuous.aestronglyMeasurable,
    eLpNormEssSup_lt_top_of_ae_bound (Filter.Eventually.of_forall (tensorSymbol_norm_le index))⟩

theorem tensorSymbol_row_bound (frequency : Spatial) : ∑ index : TensorIndex, ‖tensorSymbol index frequency‖ ^ 2 ≤ 1 := by
  have sumBound : ∑ coordinate : Fin 2, ‖firstHalfSymbol coordinate frequency‖ ^ 2 ≤ 1 := by
    have identity := halfSymbols_partition frequency
    linarith [sq_nonneg ‖halfSymbol frequency‖]
  have sumNonnegative : 0 ≤ ∑ coordinate : Fin 2, ‖firstHalfSymbol coordinate frequency‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp only [tensorSymbol, Pi.mul_apply, norm_mul, mul_pow, Fintype.sum_prod_type,
    ← Finset.mul_sum, ← Finset.sum_mul]
  simpa only [one_mul] using mul_le_mul sumBound sumBound sumNonnegative zero_le_one

theorem halfSymbol_square : halfSymbol * halfSymbol = inverseBesselSymbol := by
  rw [halfSymbol, weightSymbol_mul]
  norm_num
  exact weightSymbol_neg_one

theorem tensorSymbol_derivatives (index : TensorIndex) :
    tensorSymbol index = firstDerivativeSymbol index.1 * firstDerivativeSymbol index.2 * inverseBesselSymbol := by
  rw [← halfSymbol_square]
  unfold tensorSymbol firstHalfSymbol
  ring

theorem tensorSymbol_formula (index : TensorIndex) (frequency : Spatial) :
    tensorSymbol index frequency =
      -Complex.ofReal ((2 * Real.pi) ^ 2 * frequency index.1 * frequency index.2 / besselWeight frequency) := by
  rw [tensorSymbol_derivatives]
  simp only [Pi.mul_apply, firstDerivativeSymbol, inverseBesselSymbol]
  push_cast
  calc
    _ = Complex.I ^ 2 * ((2 * (Real.pi : ℂ)) ^ 2 * frequency index.1 * frequency index.2 /
      (besselWeight frequency : ℂ)) := by ring
    _ = _ := by simp

theorem tensorSymbol_distribution (index : TensorIndex) (field : FieldDistribution) :
    TemperedDistribution.fourierMultiplierCLM CellValues (tensorSymbol index) field =
      distributionResolvent (distributionDerivative index.1 (distributionDerivative index.2 field)) := by
  simp_rw [distributionDerivative_eq_multiplier]
  change TemperedDistribution.fourierMultiplierCLM CellValues (tensorSymbol index) field =
    TemperedDistribution.fourierMultiplierCLM CellValues inverseBesselSymbol
      (TemperedDistribution.fourierMultiplierCLM CellValues (firstDerivativeSymbol index.1)
        (TemperedDistribution.fourierMultiplierCLM CellValues (firstDerivativeSymbol index.2) field))
  rw [distributionMultiplier_comp (firstDerivativeSymbol_temperate index.1) (firstDerivativeSymbol_temperate index.2),
    distributionMultiplier_comp inverseBesselSymbol_temperate
      ((firstDerivativeSymbol_temperate index.1).mul (firstDerivativeSymbol_temperate index.2)),
    tensorSymbol_derivatives, mul_comm inverseBesselSymbol]

end Grad.TensorBootstrap
