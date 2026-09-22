import AKDP35ActualPrincipalRankRemainderNorm
import AKDP36ActualNestedTensorNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 3000
open Set
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate Grad.OriginalCoreRealization Grad.ActualOriginalSourceFirst
open Grad.WeightedJets.Ordered Grad.TensorBootstrap Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupOriginalRankField_norm {dimension : ℕ} (parameters : PhaseParameters)
    (rank : ℕ) (core : ACore parameters dimension) :
    ‖startupOriginalRankField parameters rank core‖≤
      (Fintype.card (CartesianWord rank) : ℝ)*originalGradeNorm rank core := by
  rw [startupOriginalRankField,LinearIsometryEquiv.norm_map]
  apply (startupFiniteHilbert_norm_le_sum _).trans
  have bound := Finset.sum_le_sum (fun word (_ : word∈Finset.univ) =>
    startupOriginalOrdered_norm parameters (unitDiskAdmissible parameters) core rank word)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using bound

/-- Pointwise tensor estimate with the genuine compact equation and an
abstract principal operator. All numerical allocation is independent of
its later actual-ledger instantiation. -/
theorem startupCompactTensorRemainder_bound (parameters : PhaseParameters)
    (rank : ℕ) (index : TensorIndex) {inside : Set Spatial} (closed : IsClosed inside)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (plateau : ∀ point∈inside,outer point=1)
    (operators : Fin 2 → Fin 2 → StartupRankOperator rank 3 3)
    (core principal known : ACore parameters 3) (data : StartupCompactSpatialEquation rank inside)
    (fieldSame : base 3 rank openUnitDisk (fun _ => 0) data.field=originalSourceFieldLinear parameters core)
    (tensorSame : base 3 rank openUnitDisk (fun _ => 0) (data.tensor index.1 index.2)=
      originalSourceFieldLinear parameters (principal+known))
    (epsilon delta tail budget : ℝ) (tailNonnegative : 0≤tail) (budgetNonnegative : 0≤budget)
    (allocated : ‖startupCutoffL2 outer smooth compact‖*delta≤epsilon)
    (principalBound : ‖startupOriginalRankField parameters rank principal-
      (operators index.1 index.2).coarse (startupOriginalRankField parameters rank core)‖≤
        delta*originalGradeNorm rank core+tail*(budget*originalGradeNorm 0 core)) :
    ‖startupActualRankTensorRemainder data outer smooth compact operators index‖≤
      epsilon*originalGradeNorm rank core+
        (‖startupCutoffL2 outer smooth compact‖*(tail+(Fintype.card (CartesianWord rank) : ℝ)))*
          (originalGradeNorm rank known+budget*originalGradeNorm 0 core) := by
  have bounded := startupActualRankTensorRemainder_norm data closed outer smooth compact plateau operators index
  rw [startupOriginalRankField_graph parameters (principal+known) _ tensorSame,
    startupOriginalRankField_graph parameters core _ fieldSame] at bounded
  have split : startupOriginalRankField parameters rank (principal+known)-
      (operators index.1 index.2).coarse (startupOriginalRankField parameters rank core)=
      (startupOriginalRankField parameters rank principal-
        (operators index.1 index.2).coarse (startupOriginalRankField parameters rank core))+
          startupOriginalRankField parameters rank known := by
    change startupOriginalRankLinear parameters rank (principal+known)-_=
      (startupOriginalRankLinear parameters rank principal-_)+startupOriginalRankLinear parameters rank known
    rw [map_add]
    abel
  rw [split] at bounded
  have parts := (norm_add_le _ _).trans (add_le_add principalBound (startupOriginalRankField_norm parameters rank known))
  have paid := bounded.trans (mul_le_mul_of_nonneg_left parts (norm_nonneg _))
  have mainPaid := mul_le_mul_of_nonneg_right allocated (originalGradeNorm_nonnegative rank core)
  have sourceExtra := mul_nonneg (mul_nonneg (norm_nonneg (startupCutoffL2 outer smooth compact)) tailNonnegative)
    (originalGradeNorm_nonnegative rank known)
  have baseExtra := mul_nonneg (mul_nonneg (norm_nonneg (startupCutoffL2 outer smooth compact))
    (Nat.cast_nonneg (Fintype.card (CartesianWord rank)) : (0 : ℝ)≤_))
    (mul_nonneg budgetNonnegative (originalGradeNorm_nonnegative 0 core))
  nlinarith only [paid,mainPaid,sourceExtra,baseExtra]

end Grad.CartesianStartup
