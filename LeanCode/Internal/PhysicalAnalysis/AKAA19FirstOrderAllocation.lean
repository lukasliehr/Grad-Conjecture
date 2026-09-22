import AKAA18WeakAllocationOperators

noncomputable section

set_option maxHeartbeats 1400000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.RepresentedKernel
open Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct

abbrev startupFirstWord (direction : Fin 2) : Word 1 := fun _ => direction

def startupFirstIndex (direction : Fin 2) : ℕ × ℕ :=
  if direction = 0 then (1, 0) else (0, 1)

theorem startupFirst_selected_empty (direction : Fin 2) :
    selectedIndex (startupFirstWord direction) ∅ = (0, 0) := by
  fin_cases direction <;> decide

theorem startupFirst_selected_univ (direction : Fin 2) :
    selectedIndex (startupFirstWord direction) Finset.univ = startupFirstIndex direction := by
  fin_cases direction <;> decide

theorem startupFirst_chain_univ {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (direction : Fin 2) (target : Word ((Finset.univ : Finset (Fin 1))ᶜ).card) (parameter : Parameter) :
    chainProduct data (startupFirstWord direction) Finset.univ target parameter = 1 := by
  rw [chainProduct, chainFactor_eq]
  apply Finset.prod_eq_one
  intro position _
  have empty : ((Finset.univ : Finset (Fin 1))ᶜ).card = 0 := by decide
  exact Fin.elim0 (Fin.cast empty position)

theorem startupFirst_chain_empty {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} {inputDimension outputDimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (direction : Fin 2) (target : Word ((∅ : Finset (Fin 1))ᶜ).card) (parameter : Parameter)
    (identity : data.orthogonal parameter = LinearIsometryEquiv.refl ℝ _) :
    chainProduct data (startupFirstWord direction) ∅ target parameter =
      if target = (fun _ => direction) then 1 else 0 := by
  change Word 1 at target
  change chainFactor 1 (data.orthogonal parameter) (startupFirstWord direction) target = _
  rw [chainFactor_eq, identity]
  change (∏ position : Fin 1, Grad.PDEBootstrap.spatialDirection direction (target position)) = _
  rw [Fin.prod_univ_one]
  by_cases same : target = (fun _ => direction)
  · subst target
    simp [Grad.PDEBootstrap.spatialDirection]
    rfl
  · have different : target 0 ≠ direction := by
      intro equal
      apply same
      funext position
      have positionZero : position = 0 := Subsingleton.elim _ _
      simpa only [positionZero] using equal
    simp [Grad.PDEBootstrap.spatialDirection, Ne.symm different]
    exact same

end Grad.CartesianStartup
