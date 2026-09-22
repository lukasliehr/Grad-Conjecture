import AKBW2OrderedCovectorH1Action
import GTFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap

abbrev startupTensorDimension (dimension rank : ℕ) :=
  Fintype.card (Σ _ : DerivativeIndex rank, Fin dimension)

/-- A finite value reindexing only: the inherited tensor norm is unchanged. -/
def startupTensorValueEquiv (dimension rank : ℕ) :
    Tensor rank (PhysicalValue dimension) ≃ₗᵢ[ℂ] PhysicalValue (startupTensorDimension dimension rank) :=
  (LinearIsometryEquiv.piLpCurry ℂ 2
    (fun (_ : DerivativeIndex rank) (_ : Fin dimension) => ℂ)).symm.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin (Σ _ : DerivativeIndex rank, Fin dimension)))

/-- Apply an actual value isometry to every integer cell, with no cell cutoff. -/
def startupCellValueEquiv {Input Output : Type*}
    [NormedAddCommGroup Input] [NormedSpace ℂ Input]
    [NormedAddCommGroup Output] [NormedSpace ℂ Output]
    (equivalence : Input ≃ₗᵢ[ℂ] Output) : Cells Input ≃ₗᵢ[ℂ] Cells Output where
  toFun field := ⟨fun cell => equivalence (field cell),
    (lp.memℓp field).mono' (fun cell => (equivalence.norm_map (field cell)).le)⟩
  invFun field := ⟨fun cell => equivalence.symm (field cell),
    (lp.memℓp field).mono' (fun cell => (equivalence.symm.norm_map (field cell)).le)⟩
  left_inv field := by apply lp.ext; funext cell; exact equivalence.symm_apply_apply (field cell)
  right_inv field := by apply lp.ext; funext cell; exact equivalence.apply_symm_apply (field cell)
  map_add' first second := by apply lp.ext; funext cell; exact map_add equivalence (first cell) (second cell)
  map_smul' scalar field := by apply lp.ext; funext cell; exact map_smul equivalence scalar (field cell)
  norm_map' field := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Grad.TensorCellExchange.lp_norm_sq, Grad.TensorCellExchange.lp_norm_sq]
    apply tsum_congr
    intro cell
    change ‖equivalence (field cell)‖ ^ 2 = ‖field cell‖ ^ 2
    rw [equivalence.norm_map]

def startupTensorCellEquiv (dimension rank : ℕ) :
    Tensor rank (Grad.GenericCarriers.CellValues dimension) ≃ₗᵢ[ℂ]
      Grad.GenericCarriers.CellValues (startupTensorDimension dimension rank) :=
  (Grad.TensorCellExchange.exchange (DerivativeIndex rank) (PhysicalValue dimension)).trans
    (startupCellValueEquiv (startupTensorValueEquiv dimension rank))

end Grad.CartesianStartup
