import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.FinCases

noncomputable section

open MeasureTheory LineDeriv
open scoped SchwartzMap

namespace Grad.PDEBootstrap

abbrev Spatial := EuclideanSpace ℝ (Fin 2)
abbrev CellValues := lp (fun _ : ℤ => EuclideanSpace ℂ (Fin 3)) 2
abbrev FieldL2 := Lp CellValues 2 (volume : Measure Spatial)
abbrev FieldDistribution := TemperedDistribution Spatial CellValues
abbrev FirstJet := PiLp 2 (fun _ : Fin 3 => FieldL2)

def spatialDirection (coordinate : Fin 2) : Spatial :=
  WithLp.toLp 2 (Pi.single coordinate 1)

def distributionEmbedding : FieldL2 →L[ℂ] FieldDistribution :=
  Lp.toTemperedDistributionCLM CellValues volume 2

theorem distributionEmbedding_injective : Function.Injective distributionEmbedding := by
  apply LinearMap.ker_eq_bot.mp
  exact Lp.ker_toTemperedDistributionCLM_eq_bot

def jetCoordinate (coordinate : Fin 3) : FirstJet →L[ℂ] FieldL2 :=
  PiLp.proj 2 (fun _ : Fin 3 => FieldL2) coordinate

def distributionDerivative (coordinate : Fin 2) : FieldDistribution →L[ℂ] FieldDistribution :=
  lineDerivOpCLM ℂ FieldDistribution (spatialDirection coordinate)

def weakDerivativeResidual (coordinate : Fin 2) : FirstJet →L[ℂ] FieldDistribution :=
  distributionDerivative coordinate ∘L distributionEmbedding ∘L jetCoordinate 0 -
    distributionEmbedding ∘L jetCoordinate coordinate.succ

def firstOrderGraph : Submodule ℂ FirstJet :=
  ⨅ coordinate : Fin 2, (weakDerivativeResidual coordinate).ker

theorem firstOrderGraph_mem_iff (jet : FirstJet) :
    jet ∈ firstOrderGraph ↔ ∀ coordinate : Fin 2,
      distributionDerivative coordinate (distributionEmbedding (jet 0)) =
        distributionEmbedding (jet coordinate.succ) := by
  simp [firstOrderGraph, weakDerivativeResidual, jetCoordinate, sub_eq_zero]

theorem firstOrderGraph_closed : IsClosed (firstOrderGraph : Set FirstJet) := by
  simp only [firstOrderGraph, Submodule.coe_iInf]
  exact isClosed_iInter fun coordinate => (weakDerivativeResidual coordinate).isClosed_ker

abbrev FieldH1 := firstOrderGraph

instance fieldH1Complete : CompleteSpace FieldH1 :=
  firstOrderGraph_closed.completeSpace_coe

def valueInclusion : FieldH1 →L[ℂ] FieldL2 :=
  jetCoordinate 0 ∘L firstOrderGraph.subtypeL

def weakDerivative (coordinate : Fin 2) : FieldH1 →L[ℂ] FieldL2 :=
  jetCoordinate coordinate.succ ∘L firstOrderGraph.subtypeL

theorem weakDerivative_distribution (field : FieldH1) (coordinate : Fin 2) :
    distributionEmbedding (weakDerivative coordinate field) =
      distributionDerivative coordinate (distributionEmbedding (valueInclusion field)) :=
  ((firstOrderGraph_mem_iff field.val).mp field.property coordinate).symm

theorem valueInclusion_injective : Function.Injective valueInclusion := by
  intro first second sameValue
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  refine Fin.cases ?_ (fun spatial => ?_) coordinate
  · exact sameValue
  · apply distributionEmbedding_injective
    change distributionEmbedding (weakDerivative spatial first) =
      distributionEmbedding (weakDerivative spatial second)
    rw [weakDerivative_distribution, weakDerivative_distribution, sameValue]

theorem valueInclusion_norm_le (field : FieldH1) : ‖valueInclusion field‖ ≤ ‖field‖ :=
  PiLp.norm_apply_le field.val 0

theorem valueInclusion_opNorm_le : ‖valueInclusion‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  simpa only [one_mul] using valueInclusion_norm_le field

theorem weakDerivative_norm_le (field : FieldH1) (coordinate : Fin 2) :
    ‖weakDerivative coordinate field‖ ≤ ‖field‖ :=
  PiLp.norm_apply_le field.val coordinate.succ

theorem fieldH1_norm_sq (field : FieldH1) :
    ‖field‖ ^ 2 = ‖valueInclusion field‖ ^ 2 +
      ∑ coordinate : Fin 2, ‖weakDerivative coordinate field‖ ^ 2 := by
  change ‖field.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  rfl

def ofWeakDerivatives (field : FieldL2) (derivatives : Fin 2 → FieldL2)
    (identities : ∀ coordinate, distributionDerivative coordinate (distributionEmbedding field) =
      distributionEmbedding (derivatives coordinate)) : FieldH1 :=
  ⟨WithLp.toLp 2 (Fin.cons field derivatives), by
    apply (firstOrderGraph_mem_iff _).mpr
    intro coordinate
    exact identities coordinate⟩

theorem valueInclusion_ofWeakDerivatives (field : FieldL2) (derivatives : Fin 2 → FieldL2)
    (identities : ∀ coordinate, distributionDerivative coordinate (distributionEmbedding field) =
      distributionEmbedding (derivatives coordinate)) :
    valueInclusion (ofWeakDerivatives field derivatives identities) = field := rfl

theorem mem_valueInclusion_range_iff (field : FieldL2) :
    field ∈ Set.range valueInclusion ↔ ∃ derivatives : Fin 2 → FieldL2,
      ∀ coordinate, distributionDerivative coordinate (distributionEmbedding field) =
        distributionEmbedding (derivatives coordinate) := by
  constructor
  · rintro ⟨regularField, rfl⟩
    exact ⟨fun coordinate => weakDerivative coordinate regularField,
      fun coordinate => (weakDerivative_distribution regularField coordinate).symm⟩
  · rintro ⟨derivatives, identities⟩
    exact ⟨ofWeakDerivatives field derivatives identities, rfl⟩

end Grad.PDEBootstrap
