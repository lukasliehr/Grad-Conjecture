import BesselWeights

noncomputable section

namespace Grad.SobolevBridge

open Grad.PDEBootstrap MeasureTheory

def halfSymbol : Spatial → ℂ := weightSymbol (-1 / 2)

def firstHalfSymbol (coordinate : Fin 2) : Spatial → ℂ :=
  firstDerivativeSymbol coordinate * halfSymbol

theorem halfSymbol_temperate : halfSymbol.HasTemperateGrowth := weightSymbol_temperate _

theorem firstHalfSymbol_temperate (coordinate : Fin 2) : (firstHalfSymbol coordinate).HasTemperateGrowth :=
  (firstDerivativeSymbol_temperate coordinate).mul halfSymbol_temperate

theorem halfSymbol_norm_sq (frequency : Spatial) :
    ‖halfSymbol frequency‖ ^ 2 = (besselWeight frequency)⁻¹ := by
  rw [halfSymbol, weightSymbol_norm_sq]
  norm_num [Real.rpow_neg_one]

theorem halfSymbol_norm_le (frequency : Spatial) : ‖halfSymbol frequency‖ ≤ 1 := by
  rw [halfSymbol, weightSymbol_norm]
  exact Real.rpow_le_one_of_one_le_of_nonpos (besselWeight_one_le frequency) (by norm_num)

theorem firstHalfSymbol_norm_le (coordinate : Fin 2) (frequency : Spatial) :
    ‖firstHalfSymbol coordinate frequency‖ ≤ 1 := by
  have coordinateBound : ‖firstDerivativeSymbol coordinate frequency‖ ≤ ‖(2 * Real.pi) • frequency‖ := by
    simpa [firstDerivativeSymbol, norm_mul] using
      PiLp.norm_apply_le ((2 * Real.pi) • frequency) coordinate
  have squareBound : ‖firstDerivativeSymbol coordinate frequency‖ ^ 2 ≤ besselWeight frequency := by
    have := pow_le_pow_left₀ (norm_nonneg _) coordinateBound 2
    unfold besselWeight
    linarith
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  simpa [firstHalfSymbol, norm_mul, mul_pow, halfSymbol_norm_sq, div_eq_mul_inv] using
    (div_le_one (besselWeight_pos frequency)).mpr squareBound

theorem halfSymbol_memLp : MemLp halfSymbol ⊤ (volume : Measure Spatial) :=
  ⟨halfSymbol_temperate.1.continuous.aestronglyMeasurable,
    eLpNormEssSup_lt_top_of_ae_bound (Filter.Eventually.of_forall halfSymbol_norm_le)⟩

theorem firstHalfSymbol_memLp (coordinate : Fin 2) :
    MemLp (firstHalfSymbol coordinate) ⊤ (volume : Measure Spatial) :=
  ⟨(firstHalfSymbol_temperate coordinate).1.continuous.aestronglyMeasurable,
    eLpNormEssSup_lt_top_of_ae_bound (Filter.Eventually.of_forall (firstHalfSymbol_norm_le coordinate))⟩

theorem derivativeSymbols_norm_sq_sum (frequency : Spatial) :
    ∑ coordinate : Fin 2, ‖firstDerivativeSymbol coordinate frequency‖ ^ 2 =
      ‖(2 * Real.pi) • frequency‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro coordinate membership
  simp [firstDerivativeSymbol, norm_mul, PiLp.smul_apply]

theorem halfSymbols_partition (frequency : Spatial) :
    ‖halfSymbol frequency‖ ^ 2 + ∑ coordinate : Fin 2, ‖firstHalfSymbol coordinate frequency‖ ^ 2 = 1 := by
  simp only [firstHalfSymbol, Pi.mul_apply, norm_mul, mul_pow, halfSymbol_norm_sq,
    ← Finset.sum_mul, derivativeSymbols_norm_sq_sum]
  calc
    _ = (1 + ‖(2 * Real.pi) • frequency‖ ^ 2) * (besselWeight frequency)⁻¹ := by ring
    _ = 1 := mul_inv_cancel₀ (besselWeight_pos frequency).ne'

theorem derivativeSymbol_square (coordinate : Fin 2) (frequency : Spatial) :
    firstDerivativeSymbol coordinate frequency * firstDerivativeSymbol coordinate frequency =
      -Complex.ofReal (((2 * Real.pi) * frequency coordinate) ^ 2) := by
  unfold firstDerivativeSymbol
  calc
    _ = Complex.I ^ 2 * Complex.ofReal (((2 * Real.pi) * frequency coordinate) ^ 2) := by
      push_cast
      ring
    _ = _ := by simp

theorem besselSymbol_derivatives : besselSymbol = (fun _ => 1) -
    ∑ coordinate : Fin 2, firstDerivativeSymbol coordinate * firstDerivativeSymbol coordinate := by
  funext frequency
  simp [besselSymbol, besselWeight, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two, derivativeSymbol_square, PiLp.smul_apply]
  ring

theorem halfSymbol_reconstruction : weightSymbol (1 / 2) = halfSymbol -
    ∑ coordinate : Fin 2, firstHalfSymbol coordinate * firstDerivativeSymbol coordinate := by
  have weightIdentity : weightSymbol (1 / 2) = halfSymbol * besselSymbol := by
    rw [halfSymbol, ← weightSymbol_one, weightSymbol_mul]
    norm_num
  rw [weightIdentity, besselSymbol_derivatives]
  funext frequency
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Fin.sum_univ_two, firstHalfSymbol]
  ring

def halfJetSymbol : Fin 3 → Spatial → ℂ := Fin.cons halfSymbol firstHalfSymbol

theorem halfJetSymbol_memLp (coordinate : Fin 3) :
    MemLp (halfJetSymbol coordinate) ⊤ (volume : Measure Spatial) := by
  refine Fin.cases halfSymbol_memLp (fun spatial => firstHalfSymbol_memLp spatial) coordinate

theorem halfJetSymbol_partition (frequency : Spatial) :
    ∑ coordinate : Fin 3, ‖halfJetSymbol coordinate frequency‖ ^ 2 = 1 := by
  rw [Fin.sum_univ_succ]
  exact halfSymbols_partition frequency

end Grad.SobolevBridge
