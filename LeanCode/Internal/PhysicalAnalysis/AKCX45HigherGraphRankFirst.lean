import AKCX44ActualNativeLowerSpatialGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.Ordered Grad.TensorBootstrap

/-- The top ordered tensor has a first graph once precisely one further spatial grade is available. -/
theorem startupHigherGraph_rankFirst {dimension order rank weight : ℕ}
    (field : GraphGrade dimension order weight openUnitDisk) (bound : rank+1 ≤ order) :
    ∃ first : StartupFirst (startupTensorDimension dimension rank),
      base (startupTensorDimension dimension rank) 1 openUnitDisk (fun _ => 0) first =
        startupTensorFieldEquiv dimension rank
          (orderedDerivative dimension order rank openUnitDisk (fun _ => weight) (by omega) field) := by
  let coordinates (word : DerivativeIndex rank) := (startupOrderedDerivative_first field bound word).choose
  have same (word : DerivativeIndex rank) : base dimension 1 openUnitDisk (fun _ => 0) (coordinates word) =
      orderedDerivative dimension order rank openUnitDisk (fun _ => weight) (by omega) field word :=
    (startupOrderedDerivative_first field bound word).choose_spec
  refine ⟨startupTensorFirstEquiv dimension rank (WithLp.toLp 2 coordinates),?_⟩
  rw [show base (startupTensorDimension dimension rank) 1 openUnitDisk (fun _ => 0)
      (startupTensorFirstEquiv dimension rank (WithLp.toLp 2 coordinates)) = _ from
        startupTensorFirstEquiv_base dimension rank (WithLp.toLp 2 coordinates)]
  apply congrArg (startupTensorFieldEquiv dimension rank)
  apply PiLp.ext
  exact same

theorem StartupSignedFamily.rankDerivative_firstOfHigher {dimension rank : ℕ} {L ell : ℝ}
    (family : StartupSignedFamily dimension L ell) (regular : family.HasSpatialGrade rank)
    (power : ℕ) (higher : ∃ graph : GraphGrade dimension (rank+1) 0 openUnitDisk,
      base dimension (rank+1) openUnitDisk (fun _ => 0) graph = family.moment power) :
    ∃ first : StartupFirst (startupTensorDimension dimension rank),
      base (startupTensorDimension dimension rank) 1 openUnitDisk (fun _ => 0) first = family.rankDerivative regular power := by
  obtain ⟨graph,same⟩ := higher
  obtain ⟨first,firstSame⟩ := startupHigherGraph_rankFirst graph (le_refl (rank+1))
  exact ⟨first,firstSame.trans (family.rankDerivative_of_graph regular power graph (by omega) same)⟩

end Grad.CartesianStartup
