import SM1Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.SpatialMultiplier

theorem fieldMultiplier_norm_le (dimension : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (scalar : BoundedScalar domain) :
    ‖fieldMultiplier dimension domain openDomain scalar‖ ≤ scalar.bound :=
  Grad.MatrixMultiplier.norm_matrixMultiplier_le _ _ _ _ _ scalar.bound.property

theorem fieldMultiplier_apply_norm_le (dimension : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (scalar : BoundedScalar domain) (field : FieldL2 dimension domain) :
    ‖fieldMultiplier dimension domain openDomain scalar field‖ ≤ scalar.bound * ‖field‖ :=
  Grad.MatrixMultiplier.norm_matrixMultiplier_apply_le _ _ _ _ _ field

theorem fieldMultiplier_ae (dimension : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (scalar : BoundedScalar domain) (field : FieldL2 dimension domain) :
    ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      fieldMultiplier dimension domain openDomain scalar field point cell =
        (scalar.toFun point : ℂ) • field point cell := by
  filter_upwards [Grad.MatrixMultiplier.matrixMultiplier_apply_ae (volume.restrict domain)
    (scalarCoefficient dimension scalar.toFun) scalar.bound
    (scalarCoefficient_measurable dimension domain scalar)
    (scalarCoefficient_bound dimension domain openDomain scalar) field] with point equality
  intro cell
  exact congrArg (fun value : CellValues dimension => value cell) equality

theorem fieldMultiplier_pairing (dimension : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (scalar : BoundedScalar domain) (field : FieldL2 dimension domain)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain) :
    testPairing dimension domain cell vector test
        (fieldMultiplier dimension domain openDomain scalar field) =
      testPairing dimension domain cell vector (multiplyTest scalar.toFun scalar.smooth test) field := by
  rw [testPairing_apply, testPairing_apply]
  apply integral_congr_ae
  filter_upwards [fieldMultiplier_ae dimension domain openDomain scalar field] with point equality
  rw [equality cell, inner_smul_right]
  change (test.toFun point : ℂ) * ((scalar.toFun point : ℂ) * inner ℂ vector (field point cell)) =
    ((scalar.toFun point * test.toFun point : ℝ) : ℂ) * inner ℂ vector (field point cell)
  push_cast
  ring

theorem fieldMultiplier_inverse (dimension : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (scalar : BoundedScalar domain) (weight : ℕ) :
    (fieldMultiplier dimension domain openDomain scalar).comp
        (Grad.CellWeights.inverseFieldCLM dimension domain weight) =
      (Grad.CellWeights.inverseFieldCLM dimension domain weight).comp
        (fieldMultiplier dimension domain openDomain scalar) := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  filter_upwards [
    fieldMultiplier_ae dimension domain openDomain scalar
      (Grad.CellWeights.inverseFieldCLM dimension domain weight field),
    Grad.CellWeights.inverseFieldCLM_coordinate dimension domain weight field,
    Grad.CellWeights.inverseFieldCLM_coordinate dimension domain weight
      (fieldMultiplier dimension domain openDomain scalar field),
    fieldMultiplier_ae dimension domain openDomain scalar field] with point outer first second inner
  apply lp.ext
  funext cell
  change fieldMultiplier dimension domain openDomain scalar
      (Grad.CellWeights.inverseFieldCLM dimension domain weight field) point cell =
    Grad.CellWeights.inverseFieldCLM dimension domain weight
      (fieldMultiplier dimension domain openDomain scalar field) point cell
  rw [outer cell, first cell, second cell, inner cell]
  exact smul_comm _ _ _

theorem field_consumer : FieldGoal := by
  intro dimension domain openDomain scalar
  exact ⟨fieldMultiplier_norm_le dimension domain openDomain scalar,
    fun field => ⟨fieldMultiplier_apply_norm_le dimension domain openDomain scalar field,
      fieldMultiplier_ae dimension domain openDomain scalar field⟩,
    fieldMultiplier_pairing dimension domain openDomain scalar,
    fieldMultiplier_inverse dimension domain openDomain scalar⟩

end Grad.WeightedJets.SpatialMultiplier
