import SCD12AllCellEnergy

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

theorem rayAverageValue_closed {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    rayAverageValue field point.val =
      ∫ scale in (0 : ℝ)..1, field.value (ambientClosedDisk (scale • point.val)) := by
  rw [rayAverageValue, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  apply intervalIntegral.integral_congr
  intro scale inside
  dsimp only
  have member : scale ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using inside
  have ambient : ambientClosedDisk (scale • point.val) = dilationPoint scale member.1 member.2 point := by
    apply Subtype.ext
    exact ambientClosedDisk_val_of_mem (dilation_mem_closed member.1 member.2 point)
  rw [ambient]
  exact smoothClosedExtension_value field (dilationPoint scale member.1 member.2 point)

theorem rayAverageJet_add {dimension : ℕ} (first second : ClosedJet dimension) :
    rayAverageJet (first + second) = rayAverageJet first + rayAverageJet second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change rayAverageValue (first + second) point.val =
    rayAverageValue first point.val + rayAverageValue second point.val
  simp_rw [rayAverageValue_closed, closedJet_value_add, ContinuousMap.add_apply]
  exact intervalIntegral.integral_add
    ((first.value.continuous.comp (continuous_ambientClosedDisk.comp
      (continuous_id.smul continuous_const))).intervalIntegrable 0 1)
    ((second.value.continuous.comp (continuous_ambientClosedDisk.comp
      (continuous_id.smul continuous_const))).intervalIntegrable 0 1)

theorem rayAverageJet_smul {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension) :
    rayAverageJet (scalar • field) = scalar • rayAverageJet field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change rayAverageValue (scalar • field) point.val = scalar • rayAverageValue field point.val
  simp_rw [rayAverageValue_closed, closedJet_value_smul, ContinuousMap.smul_apply]
  exact intervalIntegral.integral_smul scalar _

def rayAverageLinear (dimension : ℕ) : ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := rayAverageJet
  map_add' := rayAverageJet_add
  map_smul' := rayAverageJet_smul

def shiftedJetLinear (dimension : ℕ) {order : ℕ} (word : CartesianWord order) :
    ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := fun field => shiftedClosedJet field word
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    rw [closedJet_value_add, shiftedClosedJet_value, shiftedClosedJet_value, shiftedClosedJet_value]
    exact closedJetAdd_derivative first second order word
  map_smul' scalar field := by
    apply closedJet_eq_of_value_eq
    rw [closedJet_value_smul, shiftedClosedJet_value, shiftedClosedJet_value]
    exact closedJetSmul_derivative scalar field order word

def averagedPartialLinear (dimension : ℕ) (coordinate : Fin 2) :
    ClosedJet dimension →ₗ[ℂ] ClosedJet dimension :=
  (rayAverageLinear dimension).comp (shiftedJetLinear dimension (fun _ : Fin 1 => coordinate))

theorem dividedPolarValue_closed {dimension : ℕ} (field : ClosedJet dimension)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    dividedPolarValue field (radius, angle) = ∑ coordinate : Fin 2, radialDirection angle coordinate •
      (averagedPartialLinear dimension coordinate field).value (polarClosedPoint radius angle nonnegative bounded) := rfl

theorem dividedPolarValue_add_closed {dimension : ℕ} (first second : ClosedJet dimension)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    dividedPolarValue (first + second) (radius, angle) =
      dividedPolarValue first (radius, angle) + dividedPolarValue second (radius, angle) := by
  simp_rw [dividedPolarValue_closed _ radius angle nonnegative bounded, map_add, closedJet_value_add,
    ContinuousMap.add_apply, smul_add, Finset.sum_add_distrib]

theorem dividedPolarValue_smul_closed {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    dividedPolarValue (scalar • field) (radius, angle) = scalar • dividedPolarValue field (radius, angle) := by
  simp_rw [dividedPolarValue_closed _ radius angle nonnegative bounded, map_smul, closedJet_value_smul,
    ContinuousMap.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact smul_comm _ _ _

end Grad.SourceCollarDivision
