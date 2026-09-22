import L2Multipliers

noncomputable section

open MeasureTheory FourierTransform

namespace Grad.PDEBootstrap

theorem spatialDirection_inner (coordinate : Fin 2) (frequency : Spatial) :
    inner ℝ frequency (spatialDirection coordinate) = frequency coordinate := by
  change inner ℝ frequency (EuclideanSpace.single coordinate (1 : ℝ)) = _
  simpa using EuclideanSpace.inner_single_right coordinate (1 : ℝ) frequency

def firstDerivativeSymbol (coordinate : Fin 2) (frequency : Spatial) : ℂ :=
  Complex.I * Complex.ofReal ((2 * Real.pi) * frequency coordinate)

theorem firstDerivativeSymbol_temperate (coordinate : Fin 2) :
    (firstDerivativeSymbol coordinate).HasTemperateGrowth := by
  have coordinateGrowth : (fun frequency : Spatial => frequency coordinate).HasTemperateGrowth :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) coordinate).hasTemperateGrowth
  exact (Function.HasTemperateGrowth.const Complex.I).mul
    (Function.Complex.hasTemperateGrowth_ofReal.comp
      ((Function.HasTemperateGrowth.const (2 * Real.pi)).mul coordinateGrowth))

theorem distributionDerivative_eq_multiplier (coordinate : Fin 2) (field : FieldDistribution) :
    distributionDerivative coordinate field =
      TemperedDistribution.fourierMultiplierCLM CellValues (firstDerivativeSymbol coordinate) field := by
  have innerGrowth : (fun frequency : Spatial =>
      Complex.ofReal (inner ℝ frequency (spatialDirection coordinate))).HasTemperateGrowth :=
    Function.Complex.hasTemperateGrowth_ofReal.comp
      (Function.hasTemperateGrowth_inner_left (spatialDirection coordinate))
  have symbolIdentity : firstDerivativeSymbol coordinate =
      (2 * (Real.pi : ℂ) * Complex.I) • (fun frequency : Spatial =>
        Complex.ofReal (inner ℝ frequency (spatialDirection coordinate))) := by
    funext frequency
    simp [firstDerivativeSymbol, spatialDirection_inner, mul_comm, mul_assoc]
  rw [symbolIdentity, TemperedDistribution.fourierMultiplierCLM_smul innerGrowth]
  exact TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM (spatialDirection coordinate) field

def resolventDerivativeSymbol (coordinate : Fin 2) : Spatial → ℂ :=
  firstDerivativeSymbol coordinate * inverseBesselSymbol

theorem resolventDerivativeSymbol_temperate (coordinate : Fin 2) :
    (resolventDerivativeSymbol coordinate).HasTemperateGrowth :=
  (firstDerivativeSymbol_temperate coordinate).mul inverseBesselSymbol_temperate

theorem resolventDerivativeSymbol_norm_le (coordinate : Fin 2) (frequency : Spatial) :
    ‖resolventDerivativeSymbol coordinate frequency‖ ≤ 1 := by
  have coordinateBound : ‖firstDerivativeSymbol coordinate frequency‖ ≤ ‖(2 * Real.pi) • frequency‖ := by
    simpa [firstDerivativeSymbol, norm_mul] using
      PiLp.norm_apply_le ((2 * Real.pi) • frequency) coordinate
  have weightBound : ‖(2 * Real.pi) • frequency‖ ≤ besselWeight frequency := by
    unfold besselWeight
    nlinarith [sq_nonneg (‖(2 * Real.pi) • frequency‖ - 1 / 2)]
  calc
    ‖resolventDerivativeSymbol coordinate frequency‖ =
        ‖firstDerivativeSymbol coordinate frequency‖ / besselWeight frequency := by
      simp [resolventDerivativeSymbol, inverseBesselSymbol,
        abs_of_pos (besselWeight_pos frequency), div_eq_mul_inv]
    _ ≤ 1 := (div_le_one (besselWeight_pos frequency)).mpr (coordinateBound.trans weightBound)

theorem resolventDerivativeSymbol_memLp (coordinate : Fin 2) :
    MemLp (resolventDerivativeSymbol coordinate) ⊤ (volume : Measure Spatial) :=
  ⟨(resolventDerivativeSymbol_temperate coordinate).1.continuous.aestronglyMeasurable,
    eLpNormEssSup_lt_top_of_ae_bound
      (Filter.Eventually.of_forall (resolventDerivativeSymbol_norm_le coordinate))⟩

def l2ResolventDerivative (coordinate : Fin 2) : FieldL2 →L[ℂ] FieldL2 :=
  l2Multiplier ((resolventDerivativeSymbol_memLp coordinate).toLp (resolventDerivativeSymbol coordinate))

theorem l2ResolventDerivative_distribution (coordinate : Fin 2) (field : FieldL2) :
    distributionEmbedding (l2ResolventDerivative coordinate field) =
      distributionDerivative coordinate (distributionEmbedding (l2Resolvent field)) := by
  rw [l2Resolvent_distribution, distributionDerivative_eq_multiplier]
  change distributionEmbedding (l2Multiplier
    ((resolventDerivativeSymbol_memLp coordinate).toLp _) field) =
      TemperedDistribution.fourierMultiplierCLM CellValues (firstDerivativeSymbol coordinate)
        (TemperedDistribution.fourierMultiplierCLM CellValues inverseBesselSymbol
          (distributionEmbedding field))
  rw [l2Multiplier_distribution (resolventDerivativeSymbol_temperate coordinate)
    (resolventDerivativeSymbol_memLp coordinate)]
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    inverseBesselSymbol_temperate (firstDerivativeSymbol_temperate coordinate)]
  rw [resolventDerivativeSymbol, mul_comm (firstDerivativeSymbol coordinate) inverseBesselSymbol]

def h1Resolvent (field : FieldL2) : FieldH1 :=
  ofWeakDerivatives (l2Resolvent field) (fun coordinate => l2ResolventDerivative coordinate field)
    (fun coordinate => (l2ResolventDerivative_distribution coordinate field).symm)

theorem h1Resolvent_value (field : FieldL2) : valueInclusion (h1Resolvent field) = l2Resolvent field := rfl

theorem l2Resolvent_has_weak_derivatives (field : FieldL2) :
    l2Resolvent field ∈ Set.range valueInclusion :=
  ⟨h1Resolvent field, rfl⟩

theorem l2ResolventDerivative_norm_le (coordinate : Fin 2) (field : FieldL2) :
    ‖l2ResolventDerivative coordinate field‖ ≤ ‖field‖ := by
  have symbolBound := symbol_linf_norm_le_one (resolventDerivativeSymbol_memLp coordinate)
    (resolventDerivativeSymbol_norm_le coordinate)
  exact (l2Multiplier_norm_le _ field).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right symbolBound (norm_nonneg field))

theorem h1Resolvent_norm_le (field : FieldL2) : ‖h1Resolvent field‖ ≤ 2 * ‖field‖ := by
  have derivativeSquares (coordinate : Fin 2) :
      ‖l2ResolventDerivative coordinate field‖ ^ 2 ≤ ‖field‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (l2ResolventDerivative_norm_le coordinate field) 2
  have sumBound := Finset.sum_le_sum (fun coordinate (_ : coordinate ∈ Finset.univ) =>
    derivativeSquares coordinate)
  have valueSquare : ‖l2Resolvent field‖ ^ 2 ≤ ‖field‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (l2Resolvent_norm_le field) 2
  have graphNorm := fieldH1_norm_sq (h1Resolvent field)
  change ‖h1Resolvent field‖ ^ 2 = ‖l2Resolvent field‖ ^ 2 +
    ∑ coordinate : Fin 2, ‖l2ResolventDerivative coordinate field‖ ^ 2 at graphNorm
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at sumBound
  norm_num at sumBound
  rw [Fin.sum_univ_two] at graphNorm
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg field))).mp
  nlinarith [sq_nonneg ‖field‖]

def h1ResolventLinear : FieldL2 →ₗ[ℂ] FieldH1 where
  toFun := h1Resolvent
  map_add' first second := by
    apply valueInclusion_injective
    change l2Resolvent (first + second) = l2Resolvent first + l2Resolvent second
    exact map_add l2Resolvent first second
  map_smul' scalar field := by
    apply valueInclusion_injective
    change l2Resolvent (scalar • field) = scalar • l2Resolvent field
    exact map_smul l2Resolvent scalar field

def h1ResolventCLM : FieldL2 →L[ℂ] FieldH1 :=
  h1ResolventLinear.mkContinuous 2 h1Resolvent_norm_le

theorem h1ResolventCLM_compatible : valueInclusion ∘L h1ResolventCLM = l2Resolvent := by
  ext field
  rfl

theorem h1ResolventCLM_opNorm_le : ‖h1ResolventCLM‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le h1ResolventLinear (by norm_num) h1Resolvent_norm_le

end Grad.PDEBootstrap
