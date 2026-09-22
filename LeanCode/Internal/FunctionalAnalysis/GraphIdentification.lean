import SobolevSpaces
import HalfSymbols
import MultiplierEnergy

noncomputable section

namespace Grad.SobolevBridge

open Grad.PDEBootstrap

def halfL2 : FieldL2 →L[ℂ] FieldL2 := l2Multiplier (halfSymbol_memLp.toLp halfSymbol)

def firstHalfL2 (coordinate : Fin 2) : FieldL2 →L[ℂ] FieldL2 :=
  l2Multiplier ((firstHalfSymbol_memLp coordinate).toLp (firstHalfSymbol coordinate))

theorem halfL2_distribution (field : FieldL2) :
    distributionEmbedding (halfL2 field) = distributionWeight (-1 / 2) (distributionEmbedding field) :=
  l2Multiplier_distribution halfSymbol_temperate halfSymbol_memLp field

theorem firstHalfL2_distribution (coordinate : Fin 2) (field : FieldL2) :
    distributionEmbedding (firstHalfL2 coordinate field) =
      TemperedDistribution.fourierMultiplierCLM CellValues (firstHalfSymbol coordinate)
        (distributionEmbedding field) :=
  l2Multiplier_distribution (firstHalfSymbol_temperate coordinate) (firstHalfSymbol_memLp coordinate) field

theorem halfL2_derivatives (coordinate : Fin 2) (field : FieldL2) :
    distributionDerivative coordinate (distributionEmbedding (halfL2 field)) =
      distributionEmbedding (firstHalfL2 coordinate field) := by
  rw [halfL2_distribution, firstHalfL2_distribution, distributionDerivative_eq_multiplier]
  change TemperedDistribution.fourierMultiplierCLM CellValues (firstDerivativeSymbol coordinate)
    (TemperedDistribution.fourierMultiplierCLM CellValues halfSymbol (distributionEmbedding field)) = _
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    halfSymbol_temperate (firstDerivativeSymbol_temperate coordinate)]
  rw [firstHalfSymbol, mul_comm halfSymbol]

def halfGraph (field : FieldL2) : FieldH1 :=
  ofWeakDerivatives (halfL2 field) (fun coordinate => firstHalfL2 coordinate field)
    (fun coordinate => halfL2_derivatives coordinate field)

theorem halfGraph_norm_sq (field : FieldL2) : ‖halfGraph field‖ ^ 2 = ‖field‖ ^ 2 := by
  rw [fieldH1_norm_sq]
  have energy := multiplier_partition_energy halfJetSymbol halfJetSymbol_memLp halfJetSymbol_partition field
  rw [Fin.sum_univ_succ] at energy
  exact energy

theorem halfGraph_norm (field : FieldL2) : ‖halfGraph field‖ = ‖field‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (halfGraph_norm_sq field)

def halfGraphLinear : FieldL2 →ₗ[ℂ] FieldH1 where
  toFun := halfGraph
  map_add' first second := by
    apply valueInclusion_injective
    change halfL2 (first + second) = halfL2 first + halfL2 second
    exact map_add halfL2 first second
  map_smul' scalar field := by
    apply valueInclusion_injective
    change halfL2 (scalar • field) = scalar • halfL2 field
    exact map_smul halfL2 scalar field

def halfGraphIsometry : FieldL2 →ₗᵢ[ℂ] FieldH1 :=
  { halfGraphLinear with norm_map' := halfGraph_norm }

theorem distributionMultiplier_sub {first second : Spatial → ℂ}
    (firstGrowth : first.HasTemperateGrowth) (secondGrowth : second.HasTemperateGrowth) :
    TemperedDistribution.fourierMultiplierCLM CellValues (first - second) =
      TemperedDistribution.fourierMultiplierCLM CellValues first -
        TemperedDistribution.fourierMultiplierCLM CellValues second := by
  ext field
  simp [TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.smulLeftCLM_sub firstGrowth secondGrowth]

theorem distributionMultiplier_comp {first second : Spatial → ℂ}
    (firstGrowth : first.HasTemperateGrowth) (secondGrowth : second.HasTemperateGrowth)
    (field : FieldDistribution) :
    TemperedDistribution.fourierMultiplierCLM CellValues first
      (TemperedDistribution.fourierMultiplierCLM CellValues second field) =
        TemperedDistribution.fourierMultiplierCLM CellValues (first * second) field := by
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply secondGrowth firstGrowth,
    mul_comm]

theorem distribution_half_reconstruction (field : FieldDistribution) :
    distributionWeight (1 / 2) field = distributionWeight (-1 / 2) field -
      ∑ coordinate : Fin 2, TemperedDistribution.fourierMultiplierCLM CellValues (firstHalfSymbol coordinate)
        (distributionDerivative coordinate field) := by
  simp_rw [distributionDerivative_eq_multiplier,
    distributionMultiplier_comp (firstHalfSymbol_temperate _) (firstDerivativeSymbol_temperate _)]
  change TemperedDistribution.fourierMultiplierCLM CellValues (weightSymbol (1 / 2)) field =
    TemperedDistribution.fourierMultiplierCLM CellValues halfSymbol field - _
  rw [halfSymbol_reconstruction, Fin.sum_univ_two,
    distributionMultiplier_sub halfSymbol_temperate
      (((firstHalfSymbol_temperate 0).mul (firstDerivativeSymbol_temperate 0)).add
        ((firstHalfSymbol_temperate 1).mul (firstDerivativeSymbol_temperate 1))),
    distributionMultiplier_add
      ((firstHalfSymbol_temperate 0).mul (firstDerivativeSymbol_temperate 0))
      ((firstHalfSymbol_temperate 1).mul (firstDerivativeSymbol_temperate 1))]
  simp only [sub_apply, add_apply, Fin.sum_univ_two]

def graphCoordinates (field : FieldH1) : FieldL2 :=
  halfL2 (valueInclusion field) - ∑ coordinate : Fin 2, firstHalfL2 coordinate (weakDerivative coordinate field)

set_option maxHeartbeats 800000 in
theorem graphCoordinates_distribution (field : FieldH1) :
    distributionEmbedding (graphCoordinates field) =
      distributionWeight (1 / 2) (distributionEmbedding (valueInclusion field)) := by
  rw [graphCoordinates, map_sub, map_sum, halfL2_distribution, distribution_half_reconstruction]
  simp_rw [firstHalfL2_distribution, weakDerivative_distribution]

theorem halfGraph_graphCoordinates (field : FieldH1) : halfGraph (graphCoordinates field) = field := by
  apply valueInclusion_injective
  apply distributionEmbedding_injective
  change distributionEmbedding (halfL2 (graphCoordinates field)) = _
  rw [halfL2_distribution, graphCoordinates_distribution, distributionWeight_add]
  norm_num
  rw [distributionWeight_zero]

theorem halfGraphIsometry_surjective : Function.Surjective halfGraphIsometry :=
  fun field => ⟨graphCoordinates field, halfGraph_graphCoordinates field⟩

def halfGraphEquiv : FieldL2 ≃ₗᵢ[ℂ] FieldH1 :=
  LinearIsometryEquiv.ofSurjective halfGraphIsometry halfGraphIsometry_surjective

def sobolevOneEquivGraph : Sobolev 1 ≃ₗᵢ[ℂ] FieldH1 :=
  (sobolevCoordinates 1).trans halfGraphEquiv

theorem sobolevOneEquivGraph_distribution (field : Sobolev 1) :
    distributionEmbedding (valueInclusion (sobolevOneEquivGraph field)) = sobolevDistribution 1 field :=
  halfL2_distribution (sobolevCoordinates 1 field)

theorem sobolevOneEquivGraph_norm (field : Sobolev 1) : ‖sobolevOneEquivGraph field‖ = ‖field‖ :=
  sobolevOneEquivGraph.norm_map field

theorem sobolevOne_range_iff_weak_derivatives (field : FieldDistribution) :
    field ∈ Set.range (sobolevDistribution 1) ↔
      ∃ value : FieldL2, distributionEmbedding value = field ∧
        ∃ derivatives : Fin 2 → FieldL2, ∀ coordinate,
          distributionDerivative coordinate field = distributionEmbedding (derivatives coordinate) := by
  constructor
  · rintro ⟨representative, rfl⟩
    let graph := sobolevOneEquivGraph representative
    have equality := sobolevOneEquivGraph_distribution representative
    refine ⟨valueInclusion graph, equality, fun coordinate => weakDerivative coordinate graph, ?_⟩
    intro coordinate
    rw [← equality]
    exact (weakDerivative_distribution graph coordinate).symm
  · rintro ⟨value, equality, derivatives, identities⟩
    let graph := ofWeakDerivatives value derivatives (fun coordinate => by rw [equality]; exact identities coordinate)
    refine ⟨sobolevOneEquivGraph.symm graph, ?_⟩
    rw [← sobolevOneEquivGraph_distribution, LinearIsometryEquiv.apply_symm_apply]
    exact equality

end Grad.SobolevBridge
