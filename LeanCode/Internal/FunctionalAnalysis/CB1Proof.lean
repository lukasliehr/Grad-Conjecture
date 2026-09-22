import CB1Domains
import CE1Proof

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (FieldL2 fieldCellProjection)
open Grad.CellWeights Grad.WeightedJets
open scoped BigOperators

namespace Grad.CellBinomial

theorem field_binomial (dimension weight : ℕ) (domain : Set Spatial)
    (field weighted : FieldL2 dimension domain)
    (derivatives : Fin (weight + 1) → FieldL2 dimension domain)
    (positiveGraph : (field, weighted) ∈ fieldGraph dimension domain (positiveFactor weight))
    (derivativeGraphs : ∀ power : Fin (weight + 1),
      (field, derivatives power) ∈ fieldGraph dimension domain (derivativeFactor power.val)) :
    ‖weighted‖ ^ 2 = ∑ power : Fin (weight + 1), (weight.choose power.val : ℝ) * ‖derivatives power‖ ^ 2 := by
  have coordinateIdentity (cell : ℤ) :
      ‖fieldCellProjection dimension domain cell weighted‖ ^ 2 =
        ∑ power : Fin (weight + 1), (weight.choose power.val : ℝ) *
          ‖fieldCellProjection dimension domain cell (derivatives power)‖ ^ 2 := by
    rw [(fieldGraph_mem dimension domain _ _ _).mp positiveGraph cell, norm_smul, mul_pow,
      scalar_binomial, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro power _membership
    rw [(fieldGraph_mem dimension domain _ _ _).mp (derivativeGraphs power) cell, norm_smul, mul_pow]
    ring
  rw [Grad.CellEnergy.field_norm_sq_eq_tsum]
  simp_rw [coordinateIdentity]
  rw [Summable.tsum_finsetSum (fun power _membership =>
    (Grad.CellEnergy.cellEnergy_summable dimension domain (derivatives power)).mul_left
      (weight.choose power.val : ℝ))]
  apply Finset.sum_congr rfl
  intro power _membership
  rw [tsum_mul_left, ← Grad.CellEnergy.field_norm_sq_eq_tsum]

theorem normIdentity : NormGoal := by
  intro dimension order weight domain openDomain field weighted baseEquality lambda derivatives
  obtain ⟨lambdaEquality, coordinateEquality⟩ :=
    equality dimension order weight domain openDomain field weighted baseEquality lambda derivatives
  have lambdaNorm : ‖weighted‖ ^ 2 = ‖lambda.jet‖ ^ 2 := by
    change ‖weighted.val‖ ^ 2 = ‖lambda.jet.val‖ ^ 2
    rw [lambdaEquality]
  refine ⟨lambdaNorm, ?_⟩
  rw [← lambdaNorm, graphGrade_norm_sq]
  have indexIdentity (index : JetIndex order) :
      ‖weighted.val index‖ ^ 2 = ∑ power : Fin (weight + 1),
        (weight.choose power.val : ℝ) * ‖(derivatives power).jet.val index‖ ^ 2 := by
    apply field_binomial dimension weight domain
      (Realization.recoveredDerivative dimension order domain (fun _ => weight) index weighted)
    · exact Realization.recoveredDerivative_fieldGraph dimension order domain (fun _ => weight) index weighted
    · intro power
      simpa only [fieldOperator_graph] using (coordinateEquality power index).1
  simp_rw [indexIdentity]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro power _membership
  rw [← Finset.mul_sum, ← graphGrade_norm_sq]

theorem unitOperator_domain (dimension : ℕ) (domain : Set Spatial) :
    (fieldOperator dimension domain (fun _ => 1)).domain = ⊤ := by
  apply top_unique
  intro field _membership
  apply (fieldOperator_domain dimension domain _ field).mpr
  exact ⟨field, fun _cell => (one_smul ℂ _).symm⟩

theorem unitOperator_apply (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain)
    (membership : field ∈ (fieldOperator dimension domain (fun _ => 1)).domain) :
    fieldOperator dimension domain (fun _ => 1) ⟨field, membership⟩ = field := by
  apply fields_ext dimension domain
  intro cell
  rw [fieldOperator_apply, one_smul]

theorem zero : ZeroGoal := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro power
    simp [positiveFactor, cellWeight]
  · intro cell
    simp [derivativeFactor]
  · intro power
    simp [derivativeFactor]
  · intro dimension domain
    simp only [derivativeOperator, lambdaOperator]
    exact ⟨unitOperator_domain dimension domain, unitOperator_domain dimension domain,
      unitOperator_apply dimension domain, unitOperator_apply dimension domain⟩

theorem block : BlockGoal :=
  ⟨scalar, witness, uniqueness, derivative_domain, lambda_domain, equality, normIdentity, allCell, zero⟩

end Grad.CellBinomial
