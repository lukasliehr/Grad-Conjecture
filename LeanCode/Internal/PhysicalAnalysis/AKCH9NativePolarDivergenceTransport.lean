import AKCH5OriginalNativeDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.AnnularReconstruction Grad.NonlinearRange
open Grad.ActualCartesianDescent Grad.OriginalKernelHomogeneousGraph Grad.ActualDeterminantEquations
open Grad.SourceBoundaryTrace Grad.PhysicalFamily

/-- Polar specialization before inserting the full native source expression. -/
theorem originalNative_divergence_polar (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) {row : DivisionRow 3 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (core : ACore parameters 3)
    (same : ∀ (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ),
      coreValue core (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) angles.2=
        curves.fullField bounded (radius,angles))
    (radius : ℝ) (inside : radius∈Ioo lower 1) (query : ℝ×ℝ) :
    coreValue (originalCartesianDivergenceCore length core)
        (Grad.SourceCollarDivision.polarClosedPoint radius query.1 (positive.le.trans inside.1.le) inside.2.le) query.2 0=
      cartesianDeterminantDivergence length (curves.cartesianField bounded) (polarPlane (radius,query.1),query.2) := by
  have normInside : ‖polarPlane (radius,query.1)‖∈Ioo lower 1 := by
    simpa only [polarPlane_norm,abs_of_pos (positive.trans inside.1)] using inside
  exact originalNative_divergence_same parameters length lower positive bounded curves core same (polarPlane (radius,query.1),query.2) normInside

end Grad.OriginalCoreRealization
