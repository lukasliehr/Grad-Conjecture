import FullCellKernelInterface

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2 fieldCellProjection cellSingle)
open scoped BigOperators Topology

namespace Grad.FullCellKernel

def coordinateLinear (dimension : ℕ) (domain : Set Spatial) :
    FieldL2 dimension domain →ₗ[ℂ] CoordinateFields dimension domain where
  toFun field := ⟨fun cell => fieldCellProjection dimension domain cell field,
    (Grad.TensorCellExchange.memlp_iff_summable_sq _).mpr
      (Grad.CellEnergy.cellEnergy_summable dimension domain field)⟩
  map_add' first second := by
    apply lp.ext
    funext cell
    exact map_add (fieldCellProjection dimension domain cell) first second
  map_smul' scalar field := by
    apply lp.ext
    funext cell
    exact map_smul (fieldCellProjection dimension domain cell) scalar field

def coordinateIsometry (dimension : ℕ) (domain : Set Spatial) :
    FieldL2 dimension domain →ₗᵢ[ℂ] CoordinateFields dimension domain where
  toLinearMap := coordinateLinear dimension domain
  norm_map' field := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Grad.TensorCellExchange.lp_norm_sq, Grad.CellEnergy.field_norm_sq_eq_tsum]
    rfl

theorem coordinateIsometry_apply (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) (cell : ℤ) :
    coordinateIsometry dimension domain field cell =
      fieldCellProjection dimension domain cell field := rfl

theorem insertCell_ae (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (field : Lp (PhysicalValue dimension) 2 (volume.restrict domain)) :
    insertCell dimension domain cell field =ᵐ[volume.restrict domain]
      fun point => cellSingle (PhysicalValue dimension) cell (field point) :=
  (cellSingle (PhysicalValue dimension) cell).coeFn_compLpL field

theorem projection_insertCell (dimension : ℕ) (domain : Set Spatial) (cell other : ℤ)
    (field : Lp (PhysicalValue dimension) 2 (volume.restrict domain)) :
    fieldCellProjection dimension domain other (insertCell dimension domain cell field) =
      if other = cell then field else 0 := by
  split_ifs with same
  · subst other
    apply Lp.ext
    filter_upwards [Grad.GenericCarriers.fieldCellProjection_ae dimension domain
      (insertCell dimension domain cell field), insertCell_ae dimension domain cell field]
      with point coordinates literal
    rw [coordinates cell, literal, Grad.GenericCarriers.cellSingle_apply, if_pos rfl]
  · apply Lp.ext
    filter_upwards [Grad.GenericCarriers.fieldCellProjection_ae dimension domain
      (insertCell dimension domain cell field), insertCell_ae dimension domain cell field,
      Lp.coeFn_zero (PhysicalValue dimension) 2 (volume.restrict domain)]
      with point coordinates literal zeroRepresentative
    rw [coordinates other, literal, Grad.GenericCarriers.cellSingle_apply, if_neg same,
      zeroRepresentative]
    rfl

theorem coordinateIsometry_insertCell (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (field : Lp (PhysicalValue dimension) 2 (volume.restrict domain)) :
    coordinateIsometry dimension domain (insertCell dimension domain cell field) =
      lp.single 2 cell field := by
  apply lp.ext
  funext other
  rw [coordinateIsometry_apply, projection_insertCell]
  by_cases same : other = cell
  · subst other
    rw [if_pos rfl, lp.single_apply_self]
  · rw [if_neg same]
    exact (lp.single_apply_ne
      (E := fun _ : ℤ => Lp (PhysicalValue dimension) 2 (volume.restrict domain)) 2 cell field same).symm

theorem coordinateIsometry_surjective (dimension : ℕ) (domain : Set Spatial) :
    Function.Surjective (coordinateIsometry dimension domain) := by
  intro fields
  change fields ∈ Set.range (coordinateIsometry dimension domain)
  have closedRange := (coordinateIsometry dimension domain).isometry.antilipschitz.isClosed_range
    (coordinateIsometry dimension domain).isometry.uniformContinuous
  have convergence := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) fields
  apply closedRange.mem_of_tendsto convergence
  exact Filter.Eventually.of_forall (fun cells =>
    ⟨∑ cell ∈ cells, insertCell dimension domain cell (fields cell), by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun cell _ => coordinateIsometry_insertCell dimension domain cell _)⟩)

def exchange (dimension : ℕ) (domain : Set Spatial) :
    FieldL2 dimension domain ≃ₗᵢ[ℂ] CoordinateFields dimension domain :=
  LinearIsometryEquiv.ofSurjective (coordinateIsometry dimension domain)
    (coordinateIsometry_surjective dimension domain)

theorem exchange_coordinate (dimension : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) (cell : ℤ) :
    exchange dimension domain field cell = fieldCellProjection dimension domain cell field := rfl

theorem exchange_symm_coordinate (dimension : ℕ) (domain : Set Spatial)
    (fields : CoordinateFields dimension domain) (cell : ℤ) :
    fieldCellProjection dimension domain cell ((exchange dimension domain).symm fields) = fields cell := by
  simpa only [exchange_coordinate] using
    congrArg (fun coordinates : CoordinateFields dimension domain => coordinates cell)
      ((exchange dimension domain).apply_symm_apply fields)

theorem exchange_consumer : ExchangeGoal := by
  intro dimension domain
  exact ⟨exchange dimension domain, exchange_coordinate dimension domain⟩

end Grad.FullCellKernel
