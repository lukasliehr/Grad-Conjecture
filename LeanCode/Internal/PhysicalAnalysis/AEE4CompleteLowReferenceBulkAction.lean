import AEE3OriginalLowRadialMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowBulkSwapFamily (lower : ℝ) (field : LowEnergyBulk lower) : LowEnergyBulk lower :=
  ⟨fun index => field (lowSwapIndex index), by
    have original := (memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp field)
    exact (memℓp_gen_iff (p := 2) (by norm_num)).mpr (lowSwapIndex.summable_iff.mpr original)⟩

theorem lowBulkSwapFamily_norm (lower : ℝ) (field : LowEnergyBulk lower) :
    ‖lowBulkSwapFamily lower field‖ = ‖field‖ := by
  have first := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (lowBulkSwapFamily lower field)
  have second := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at first second
  have reindex := lowSwapIndex.tsum_eq (fun index => ‖field index‖ ^ 2)
  have square : ‖lowBulkSwapFamily lower field‖ ^ 2 = ‖field‖ ^ 2 := first.trans (reindex.trans second.symm)
  nlinarith [norm_nonneg (lowBulkSwapFamily lower field), norm_nonneg field]

def lowBulkSwapLinear (lower : ℝ) : LowEnergyBulk lower →ₗ[ℂ] LowEnergyBulk lower where
  toFun := lowBulkSwapFamily lower
  map_add' first second := by apply lp.ext; funext index; rfl
  map_smul' scalar field := by apply lp.ext; funext index; rfl

def lowBulkSwap (lower : ℝ) : LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  (lowBulkSwapLinear lower).mkContinuous 1 (fun field => by
    change ‖lowBulkSwapFamily lower field‖ ≤ 1 * ‖field‖
    rw [one_mul]
    exact (lowBulkSwapFamily_norm lower field).le)

theorem lowBulkSwap_apply (lower : ℝ) (field : LowEnergyBulk lower) (index : LowAnnularIndex) :
    lowBulkSwap lower field index = field (lowSwapIndex index) := rfl

theorem lowBulkSwap_norm (lower : ℝ) (field : LowEnergyBulk lower) :
    ‖lowBulkSwap lower field‖ = ‖field‖ := lowBulkSwapFamily_norm lower field

/-- Original normalized BE10 action on the actual all-mode rho-stored
radial L2 carrier, without regrouping or replacing the ADY bulk. -/
def lowReferenceBulk (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) :
    LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  lowRadialDiagonal parameters length lower lengthPositive positive (fun index => index.1) +
    (lowRadialDiagonal parameters length lower lengthPositive positive (fun index => (lowSwapIndex index).1)).comp
      (lowBulkSwap lower)

theorem lowReferenceBulk_bound (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (field : LowEnergyBulk lower) :
    ‖lowReferenceBulk parameters length lower lengthPositive positive field‖ ≤
      (2 * lowReferenceCoefficientConstant parameters length) * ‖field‖ := by
  have diagonal := lowRadialDiagonal_bound parameters length lower lengthPositive positive (fun index => index.1) field
  have offDiagonal := lowRadialDiagonal_bound parameters length lower lengthPositive positive
    (fun index => (lowSwapIndex index).1) (lowBulkSwap lower field)
  exact (norm_add_le _ _).trans ((add_le_add diagonal offDiagonal).trans_eq (by rw [lowBulkSwap_norm]; ring))

theorem lowReferenceBulk_ae (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (field : LowEnergyBulk lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowReferenceBulk parameters length lower lengthPositive positive field index radius =
        (lowReferenceMatrix parameters length radius index.2 index.1 0 / lowMu length radius index.2.val.2) • field (0, index.2) radius +
        (lowReferenceMatrix parameters length radius index.2 index.1 1 / lowMu length radius index.2.val.2) • field (1, index.2) radius := by
  have diagonal := lowRadialDiagonal_ae parameters length lower lengthPositive positive (fun index => index.1) field index
  have offDiagonal := lowRadialDiagonal_ae parameters length lower lengthPositive positive
    (fun index => (lowSwapIndex index).1) (lowBulkSwap lower field) index
  have additive := Lp.coeFn_add
    (lowRadialDiagonal parameters length lower lengthPositive positive (fun index => index.1) field index)
    (lowRadialDiagonal parameters length lower lengthPositive positive (fun index => (lowSwapIndex index).1)
      (lowBulkSwap lower field) index)
  filter_upwards [diagonal, offDiagonal, additive] with radius diagonal offDiagonal additive
  change (lowRadialDiagonal parameters length lower lengthPositive positive (fun index => index.1) field index +
    lowRadialDiagonal parameters length lower lengthPositive positive (fun index => (lowSwapIndex index).1)
      (lowBulkSwap lower field) index) radius = _
  rw [additive]
  simp only [Pi.add_apply]
  rw [diagonal, offDiagonal, lowBulkSwap_apply]
  rcases index with ⟨row, mode⟩
  fin_cases row
  · simp [lowSwapIndex]
  · simp [lowSwapIndex, add_comm]

end Grad.AnnularLowCompletion
