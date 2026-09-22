import WeakH1
import Mathlib.Analysis.Distribution.FourierMultiplier

noncomputable section

open FourierTransform Laplacian

namespace Grad.PDEBootstrap

def besselWeight (frequency : Spatial) : ℝ :=
  1 + ‖(2 * Real.pi) • frequency‖ ^ 2

theorem besselWeight_eq (frequency : Spatial) :
    besselWeight frequency = 1 + (2 * Real.pi) ^ 2 * ‖frequency‖ ^ 2 := by
  simp [besselWeight, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem besselWeight_one_le (frequency : Spatial) : 1 ≤ besselWeight frequency :=
  le_add_of_nonneg_right (sq_nonneg _)

theorem besselWeight_pos (frequency : Spatial) : 0 < besselWeight frequency :=
  zero_lt_one.trans_le (besselWeight_one_le frequency)

def besselSymbol (frequency : Spatial) : ℂ := besselWeight frequency

def inverseBesselSymbol (frequency : Spatial) : ℂ := Complex.ofReal ((besselWeight frequency)⁻¹)

theorem besselSymbol_temperate : besselSymbol.HasTemperateGrowth := by
  have scaledGrowth : (fun frequency : Spatial => (2 * Real.pi) • frequency).HasTemperateGrowth := by
    fun_prop
  have squareGrowth := (Function.hasTemperateGrowth_norm_sq Spatial).comp scaledGrowth
  exact Function.Complex.hasTemperateGrowth_ofReal.comp
    ((Function.HasTemperateGrowth.const (1 : ℝ)).add squareGrowth)

theorem inverseBesselSymbol_temperate : inverseBesselSymbol.HasTemperateGrowth := by
  have realGrowth : (fun frequency : Spatial => (besselWeight frequency)⁻¹).HasTemperateGrowth := by
    have scaledGrowth : (fun frequency : Spatial => (2 * Real.pi) • frequency).HasTemperateGrowth := by
      fun_prop
    simpa only [besselWeight, Real.rpow_neg_one, Function.comp_def] using
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow Spatial (-1)).comp scaledGrowth
  exact Function.Complex.hasTemperateGrowth_ofReal.comp realGrowth

theorem besselSymbol_mul_inverse : besselSymbol * inverseBesselSymbol = fun _ => 1 := by
  funext frequency
  simp [besselSymbol, inverseBesselSymbol, (besselWeight_pos frequency).ne']

theorem inverseBesselSymbol_mul : inverseBesselSymbol * besselSymbol = fun _ => 1 := by
  rw [mul_comm]
  exact besselSymbol_mul_inverse

theorem distributionMultiplier_add {first second : Spatial → ℂ}
    (firstGrowth : first.HasTemperateGrowth) (secondGrowth : second.HasTemperateGrowth) :
    TemperedDistribution.fourierMultiplierCLM CellValues (first + second) =
      TemperedDistribution.fourierMultiplierCLM CellValues first +
        TemperedDistribution.fourierMultiplierCLM CellValues second := by
  ext field
  simp [TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.smulLeftCLM_add firstGrowth secondGrowth]

theorem one_sub_laplacian_eq_multiplier (field : FieldDistribution) :
    field - laplacian field = TemperedDistribution.fourierMultiplierCLM CellValues besselSymbol field := by
  have squareGrowth : (fun frequency : Spatial => Complex.ofReal (‖frequency‖ ^ 2)).HasTemperateGrowth :=
    Function.Complex.hasTemperateGrowth_ofReal.comp (Function.hasTemperateGrowth_norm_sq Spatial)
  have symbolDecomposition : besselSymbol = (fun _ : Spatial => (1 : ℂ)) +
      (((2 * Real.pi) ^ 2 : ℝ) : ℂ) • (fun frequency : Spatial => Complex.ofReal (‖frequency‖ ^ 2)) := by
    funext frequency
    simp [besselSymbol, besselWeight_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [symbolDecomposition, distributionMultiplier_add (by fun_prop) (by fun_prop),
    add_apply, TemperedDistribution.fourierMultiplierCLM_const]
  rw [TemperedDistribution.fourierMultiplierCLM_smul squareGrowth,
    TemperedDistribution.laplacian_eq_fourierMultiplierCLM]
  simp only [one_smul, ContinuousLinearMap.id_apply, smul_apply]
  rw [← Complex.coe_smul, Complex.ofReal_neg, neg_smul, sub_neg_eq_add]

def distributionResolvent : FieldDistribution →L[ℂ] FieldDistribution :=
  TemperedDistribution.fourierMultiplierCLM CellValues inverseBesselSymbol

theorem distributionResolvent_right (field : FieldDistribution) :
    distributionResolvent field - laplacian (distributionResolvent field) = field := by
  rw [one_sub_laplacian_eq_multiplier]
  change TemperedDistribution.fourierMultiplierCLM CellValues besselSymbol
    (TemperedDistribution.fourierMultiplierCLM CellValues inverseBesselSymbol field) = field
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    inverseBesselSymbol_temperate besselSymbol_temperate, inverseBesselSymbol_mul]
  simp

theorem distributionResolvent_left (field : FieldDistribution) :
    distributionResolvent (field - laplacian field) = field := by
  rw [one_sub_laplacian_eq_multiplier]
  change TemperedDistribution.fourierMultiplierCLM CellValues inverseBesselSymbol
    (TemperedDistribution.fourierMultiplierCLM CellValues besselSymbol field) = field
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    besselSymbol_temperate inverseBesselSymbol_temperate, besselSymbol_mul_inverse]
  simp

theorem one_sub_laplacian_injective :
    Function.Injective (fun field : FieldDistribution => field - laplacian field) :=
  Function.LeftInverse.injective distributionResolvent_left

end Grad.PDEBootstrap
