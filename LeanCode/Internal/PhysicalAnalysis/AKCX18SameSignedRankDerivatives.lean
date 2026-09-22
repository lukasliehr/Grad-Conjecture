import AKCX17JointDisplacementLeadingFirst

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

/-- The actual rank derivative of each SAME signed moment. Graph choice
is immaterial by weak derivative uniqueness. -/
def StartupSignedFamily.rankDerivative {dimension rank : ℕ} {L ell : ℝ}
    (family : StartupSignedFamily dimension L ell) (regular : family.HasSpatialGrade rank) (power : ℕ) :
    StartupL2 (startupTensorDimension dimension rank) :=
  startupTensorFieldEquiv dimension rank
    (orderedDerivative dimension rank rank openUnitDisk (fun _ => 0) le_rfl (regular power 0).choose)

theorem StartupSignedFamily.rankDerivative_of_graph {dimension rank order weight : ℕ} {L ell : ℝ}
    (family : StartupSignedFamily dimension L ell) (regular : family.HasSpatialGrade rank) (power : ℕ)
    (field : GraphGrade dimension order weight openUnitDisk) (bound : rank ≤ order)
    (same : base dimension order openUnitDisk (fun _ => weight) field = family.moment power) :
    startupTensorFieldEquiv dimension rank
      (orderedDerivative dimension order rank openUnitDisk (fun _ => weight) bound field) =
        family.rankDerivative regular power := by
  apply congrArg (startupTensorFieldEquiv dimension rank)
  exact startupOrderedDerivative_sameBase field bound (regular power 0).choose le_rfl
    (same.trans (regular power 0).choose_spec.symm)

theorem StartupSignedFamily.HasSpatialGrade.shift {dimension rank : ℕ} {L ell : ℝ}
    {family : StartupSignedFamily dimension L ell} (regular : family.HasSpatialGrade rank) (power : ℕ) :
    (family.shift power).HasSpatialGrade rank := fun q weight => regular (power+q) weight

theorem startupWeakOrdered_sum {Index : Type*} {dimension rank : ℕ} {domain : Set Spatial}
    (indices : Finset Index) {word : Fin rank → Fin 2} (fields derivatives : Index → FieldL2 dimension domain)
    (weak : ∀ index ∈ indices, HasWeakOrderedDerivative dimension domain rank word (fields index) (derivatives index)) :
    HasWeakOrderedDerivative dimension domain rank word (∑ index ∈ indices,fields index) (∑ index ∈ indices,derivatives index) := by
  intro cell vector test smooth compact supported
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro index member
  exact weak index member cell vector test smooth compact supported

end Grad.CartesianStartup
