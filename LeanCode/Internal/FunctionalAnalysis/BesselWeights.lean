import ResolventH1

noncomputable section

namespace Grad.SobolevBridge

open Grad.PDEBootstrap

def weightSymbol (exponent : ℝ) (frequency : Spatial) : ℂ :=
  Complex.ofReal (besselWeight frequency ^ exponent)

theorem weightSymbol_temperate (exponent : ℝ) : (weightSymbol exponent).HasTemperateGrowth := by
  have scaledGrowth : (fun frequency : Spatial => (2 * Real.pi) • frequency).HasTemperateGrowth := by
    fun_prop
  exact Function.Complex.hasTemperateGrowth_ofReal.comp
    ((Function.hasTemperateGrowth_one_add_norm_sq_rpow Spatial exponent).comp scaledGrowth)

theorem weightSymbol_zero : weightSymbol 0 = fun _ => 1 := by
  funext frequency
  simp [weightSymbol]

theorem weightSymbol_one : weightSymbol 1 = besselSymbol := by
  funext frequency
  simp [weightSymbol, besselSymbol]

theorem weightSymbol_neg_one : weightSymbol (-1) = inverseBesselSymbol := by
  funext frequency
  simp [weightSymbol, inverseBesselSymbol, Real.rpow_neg_one]

theorem weightSymbol_mul (first second : ℝ) :
    weightSymbol first * weightSymbol second = weightSymbol (first + second) := by
  funext frequency
  simp only [Pi.mul_apply, weightSymbol, ← Complex.ofReal_mul,
    Real.rpow_add (besselWeight_pos frequency)]

def distributionWeight (exponent : ℝ) : FieldDistribution →L[ℂ] FieldDistribution :=
  TemperedDistribution.fourierMultiplierCLM CellValues (weightSymbol exponent)

theorem distributionWeight_zero (field : FieldDistribution) : distributionWeight 0 field = field := by
  simp [distributionWeight, weightSymbol_zero]

theorem distributionWeight_add (first second : ℝ) (field : FieldDistribution) :
    distributionWeight first (distributionWeight second field) =
      distributionWeight (first + second) field := by
  unfold distributionWeight
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (weightSymbol_temperate second) (weightSymbol_temperate first), weightSymbol_mul, add_comm]

theorem distributionWeight_inverse (exponent : ℝ) (field : FieldDistribution) :
    distributionWeight (-exponent) (distributionWeight exponent field) = field := by
  rw [distributionWeight_add, neg_add_cancel, distributionWeight_zero]

theorem distributionWeight_injective (exponent : ℝ) : Function.Injective (distributionWeight exponent) :=
  Function.LeftInverse.injective (distributionWeight_inverse exponent)

theorem distributionWeight_neg_one : distributionWeight (-1) = distributionResolvent := by
  simp only [distributionWeight, weightSymbol_neg_one, distributionResolvent]

def weightedEmbedding (exponent : ℝ) : FieldL2 →L[ℂ] FieldDistribution :=
  distributionWeight exponent ∘L distributionEmbedding

theorem weightedEmbedding_injective (exponent : ℝ) : Function.Injective (weightedEmbedding exponent) :=
  (distributionWeight_injective exponent).comp distributionEmbedding_injective

theorem weightSymbol_norm (exponent : ℝ) (frequency : Spatial) :
    ‖weightSymbol exponent frequency‖ = besselWeight frequency ^ exponent := by
  simp [weightSymbol, abs_of_nonneg (Real.rpow_nonneg (besselWeight_pos frequency).le exponent)]

theorem weightSymbol_norm_sq (exponent : ℝ) (frequency : Spatial) :
    ‖weightSymbol exponent frequency‖ ^ 2 = besselWeight frequency ^ (exponent * 2) := by
  rw [weightSymbol_norm, Real.rpow_mul (besselWeight_pos frequency).le, Real.rpow_two]

end Grad.SobolevBridge
