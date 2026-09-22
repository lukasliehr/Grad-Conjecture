import AKCX20ActualMixedMatrixRank

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered
namespace StartupSignedFamily
variable {dimension rank : ℕ} {L ell : ℝ}

theorem rankDerivative_add (first second : StartupSignedFamily dimension L ell)
    (one : first.HasSpatialGrade rank) (two : second.HasSpatialGrade rank) (power : ℕ) :
    (first.add second).rankDerivative (one.add two) power = first.rankDerivative one power+second.rankDerivative two power := by
  let left := (one power 0).choose
  let right := (two power 0).choose
  have same : base dimension rank openUnitDisk (fun _ => 0) (left+right) = (first.add second).moment power := by
    rw [map_add,(one power 0).choose_spec,(two power 0).choose_spec]
    rfl
  have actual := (first.add second).rankDerivative_of_graph (one.add two) power (left+right) le_rfl same
  rw [map_add,map_add] at actual
  exact actual.symm

theorem rankDerivative_sub (first second : StartupSignedFamily dimension L ell)
    (one : first.HasSpatialGrade rank) (two : second.HasSpatialGrade rank) (power : ℕ) :
    (first.sub second).rankDerivative (one.sub two) power = first.rankDerivative one power-second.rankDerivative two power := by
  let left := (one power 0).choose
  let right := (two power 0).choose
  have same : base dimension rank openUnitDisk (fun _ => 0) (left-right) = (first.sub second).moment power := by
    rw [map_sub,(one power 0).choose_spec,(two power 0).choose_spec]
    rfl
  have actual := (first.sub second).rankDerivative_of_graph (one.sub two) power (left-right) le_rfl same
  rw [map_sub,map_sub] at actual
  exact actual.symm

theorem rankDerivative_smul (family : StartupSignedFamily dimension L ell)
    (regular : family.HasSpatialGrade rank) (scalar : ℂ) (power : ℕ) :
    (family.smul scalar).rankDerivative (regular.smul scalar) power = scalar • family.rankDerivative regular power := by
  let original := (regular power 0).choose
  have same : base dimension rank openUnitDisk (fun _ => 0) (scalar • original) = (family.smul scalar).moment power := by
    rw [map_smul,(regular power 0).choose_spec]
    rfl
  have actual := (family.smul scalar).rankDerivative_of_graph (regular.smul scalar) power (scalar • original) le_rfl same
  rw [map_smul,map_smul] at actual
  exact actual.symm

end StartupSignedFamily

/-- Exact mixed leading property at one spatial rank. The lower premise
uses strictly smaller signed powers of the SAME rank derivative. -/
def StartupSpatialAction.HasMixedLeading {rank input output : ℕ} {L ell : ℝ}
    (operator : StartupSpatialAction rank input output L ell) : Prop :=
  ∀ (family : StartupSignedFamily input L ell) (regular : family.HasSpatialGrade rank) (power : ℕ),
    (∀ q < power, ∃ first : StartupFirst (startupTensorDimension input rank),
      base (startupTensorDimension input rank) 1 openUnitDisk (fun _ => 0) first = family.rankDerivative regular q) →
    ∃ remainder : StartupFirst (startupTensorDimension output rank),
      (operator.signed.action family).rankDerivative (operator.preserves rank family regular) power =
      operator.ranked.coarse (family.rankDerivative regular power) +
        base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0) remainder

end Grad.CartesianStartup
