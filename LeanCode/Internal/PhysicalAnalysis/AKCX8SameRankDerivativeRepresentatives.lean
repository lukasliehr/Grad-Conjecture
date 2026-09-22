import AKCX7ActualFixedRankDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

/-- Ordered weak derivatives are independent of the chosen weighted graph
once its actual base field is fixed. -/
theorem startupOrderedDerivative_sameBase {dimension order rank weight otherOrder otherWeight : ℕ}
    (first : GraphGrade dimension order weight openUnitDisk) (bound : rank ≤ order)
    (second : GraphGrade dimension otherOrder otherWeight openUnitDisk) (otherBound : rank ≤ otherOrder)
    (same : base dimension order openUnitDisk (fun _ => weight) first =
      base dimension otherOrder openUnitDisk (fun _ => otherWeight) second) :
    orderedDerivative dimension order rank openUnitDisk (fun _ => weight) bound first =
      orderedDerivative dimension otherOrder rank openUnitDisk (fun _ => otherWeight) otherBound second := by
  apply startupOrderedDerivative_unique first bound
  intro word
  rw [same]
  exact orderedDerivative_hasWeak dimension otherOrder rank openUnitDisk (fun _ => otherWeight) otherBound second word

/-- The actual signed action preserves completed spatial grades, and its
rank derivative has the original accepted rank operator as leading term.
The remainder is a genuine first graph; no top derivative first graph is
part of this certificate. -/
structure StartupSpatialAction (rank input output : ℕ) (L ell : ℝ) where
  signed : StartupSignedAction input output L ell
  ranked : StartupRankOperator rank input output
  preserves : ∀ (order : ℕ) (family : StartupSignedFamily input L ell),
    family.HasSpatialGrade order → (signed.action family).HasSpatialGrade order
  leading : ∀ (family : StartupSignedFamily input L ell), family.HasSpatialGrade rank →
    ∀ (field : GraphGrade input rank 0 openUnitDisk),
      base input rank openUnitDisk (fun _ => 0) field = family.field →
    ∀ (image : GraphGrade output rank 0 openUnitDisk),
      base output rank openUnitDisk (fun _ => 0) image = signed.coarse family.field →
      ∃ remainder : StartupFirst (startupTensorDimension output rank),
        startupTensorFieldEquiv output rank
          (orderedDerivative output rank rank openUnitDisk (fun _ => 0) le_rfl image) =
        ranked.coarse (startupTensorFieldEquiv input rank
          (orderedDerivative input rank rank openUnitDisk (fun _ => 0) le_rfl field)) +
        base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0) remainder

end Grad.CartesianStartup
