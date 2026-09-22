import GC1Proof

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Grad.CellEnergy

open Grad.PDEBootstrap (Spatial)
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2 fieldCellProjection)

def cellEnergy (dimension : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain)
    (cell : ℤ) : ℝ := ‖fieldCellProjection dimension domain cell field‖ ^ 2

def CoordinateEnergyGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain),
    (∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      fieldCellProjection dimension domain cell field point = field point cell) ∧
    (∀ cell : ℤ, Integrable (fun point : Spatial => ‖field point cell‖ ^ 2)
      (volume.restrict domain)) ∧
    (∀ cell : ℤ, cellEnergy dimension domain field cell =
      ∫ point : Spatial, ‖field point cell‖ ^ 2 ∂volume.restrict domain) ∧
    (∀ cell : ℤ, ENNReal.ofReal (cellEnergy dimension domain field cell) =
      ∫⁻ point : Spatial, ENNReal.ofReal (‖field point cell‖ ^ 2) ∂volume.restrict domain) ∧
    (‖field‖ ^ 2 = ∫ point : Spatial, ‖field point‖ ^ 2 ∂volume.restrict domain) ∧
    (ENNReal.ofReal (‖field‖ ^ 2) =
      ∫⁻ point : Spatial, ENNReal.ofReal (‖field point‖ ^ 2) ∂volume.restrict domain)

def TonelliGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain),
    (∑' cell : ℤ, ENNReal.ofReal (cellEnergy dimension domain field cell)) =
      ENNReal.ofReal (‖field‖ ^ 2) ∧
    (∑' cell : ℤ, ENNReal.ofReal (cellEnergy dimension domain field cell)) < ⊤

def EnergyGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain),
    (∀ cell : ℤ, 0 ≤ cellEnergy dimension domain field cell) ∧
    Summable (fun cell : ℤ => ‖fieldCellProjection dimension domain cell field‖ ^ 2) ∧
    ‖field‖ ^ 2 = ∑' cell : ℤ, ‖fieldCellProjection dimension domain cell field‖ ^ 2

def WeightedEnergyGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain)
    (weight : ℤ → ℝ) (bound : ℝ),
    0 ≤ bound → (∀ cell : ℤ, 0 ≤ weight cell) → (∀ cell : ℤ, weight cell ≤ bound) →
    Summable (fun cell : ℤ => weight cell * ‖fieldCellProjection dimension domain cell field‖ ^ 2) ∧
    (∑' cell : ℤ, weight cell * ‖fieldCellProjection dimension domain cell field‖ ^ 2) ≤
      bound * ‖field‖ ^ 2

def LiteralConsumerGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial)
    (field : Lp (lp (fun _ : ℤ => EuclideanSpace ℂ (Fin dimension)) 2) 2 (volume.restrict domain)),
    Summable (fun cell : ℤ =>
      ‖(lp.evalCLM ℂ (fun _ : ℤ => EuclideanSpace ℂ (Fin dimension)) 2 cell).compLpL
        2 (volume.restrict domain) field‖ ^ 2) ∧
    (‖field‖ ^ 2 = ∑' cell : ℤ,
      ‖(lp.evalCLM ℂ (fun _ : ℤ => EuclideanSpace ℂ (Fin dimension)) 2 cell).compLpL
        2 (volume.restrict domain) field‖ ^ 2) ∧
    ∀ (weight : ℤ → ℝ) (bound : ℝ),
      0 ≤ bound → (∀ cell : ℤ, 0 ≤ weight cell) → (∀ cell : ℤ, weight cell ≤ bound) →
      Summable (fun cell : ℤ => weight cell *
        ‖(lp.evalCLM ℂ (fun _ : ℤ => EuclideanSpace ℂ (Fin dimension)) 2 cell).compLpL
          2 (volume.restrict domain) field‖ ^ 2) ∧
      (∑' cell : ℤ, weight cell *
        ‖(lp.evalCLM ℂ (fun _ : ℤ => EuclideanSpace ℂ (Fin dimension)) 2 cell).compLpL
          2 (volume.restrict domain) field‖ ^ 2) ≤ bound * ‖field‖ ^ 2

def BlockGoal : Prop :=
  CoordinateEnergyGoal ∧ TonelliGoal ∧ EnergyGoal ∧ WeightedEnergyGoal ∧ LiteralConsumerGoal

end Grad.CellEnergy
