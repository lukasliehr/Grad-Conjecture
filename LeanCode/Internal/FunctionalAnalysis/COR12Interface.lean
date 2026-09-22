import COR12Maps

noncomputable section

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.CartesianState
open Grad.DiskExtension.Operator
open Grad.FourierGrade

/-- Both maps use the single P09 extension/restriction and the original
phase parameters, independently of the later choice of grade. -/
def ExactCompositeGoal : Prop :=
  ∀ dimension (parameters : PhaseParameters),
    (∀ (field : ACore parameters dimension) (mode : FourierMode),
      (weightedFourierExtension parameters field).1 mode =
        UnitAddTorus.mFourierCoeff
          (torusSmoothNormalizedValue
            (ordinaryExtensionRetraction.extension dimension
              (weightedSmoothEquiv parameters field))) (modeVector mode)) ∧
    (∀ values : JCore (ComplexEuclidean dimension),
      weightedFourierRetraction parameters values =
        (weightedSmoothEquiv parameters).symm
          (ordinaryExtensionRetraction.restriction dimension
            (reconstructedTorusSmoothField values)))

/-- The same finite grade-only constant bounds both complex-linear maps in
the literal original Cartesian and Fourier norms, with no grade or width loss. -/
def SameGradeBoundGoal : Prop :=
  ∀ grade : ℕ, ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ dimension (parameters : PhaseParameters),
      (∀ field : ACore parameters dimension,
        ‖coreToGrade grade (weightedFourierExtension parameters field)‖ ≤
          constant * ‖GradeCore.ofCoreLinear (grade := grade) field‖) ∧
      (∀ values : JCore (ComplexEuclidean dimension),
        ‖GradeCore.ofCoreLinear (grade := grade) (weightedFourierRetraction parameters values)‖ ≤
          constant * ‖coreToGrade grade values‖)

/-- Exact standalone FA-COR12: actual Fourier/extension/phase composites,
same-grade bounds at every integer grade, and core retraction. -/
def BlockGoal : Prop :=
  ExactCompositeGoal ∧ SameGradeBoundGoal ∧
    ∀ dimension (parameters : PhaseParameters) (field : ACore parameters dimension),
      weightedFourierRetraction parameters (weightedFourierExtension parameters field) = field

end Grad.COR12Extension
