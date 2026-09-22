import ANJ3CompletedRobinTrace
import ASP7ActualStrongConsumer

noncomputable section
set_option maxHeartbeats 1200000
open Set
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskFaithfulness Grad.ActualUniformGlobal Grad.ActualSmoothPDE
local instance (priority := 2000) rightInverseUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

theorem unitScalarOperator_core (parameters : PhaseParameters) (grade : ℕ) (parameter : ℝ) (core : ClosedJet 1) :
    unitScalarOperator grade parameter (unitDiskCoreInto (grade + 2) core) =
      unitDiskCoreInto grade (scalarResidualJet parameter core) := by
  apply ordinaryBulk_injective parameters grade
  have lhs := (unitScalarOperator_bulk grade parameter (unitDiskCoreInto (grade + 2) core)).trans
    (congrArg₂ (fun value laplacian : DiskL2 1 => ((parameter ^ 2 : ℝ) : ℂ) • diskB value - laplacian)
      (unitDiskBulk_core (grade + 2) core) (unitCartesianLaplacian_core_bulk grade core))
  have rhs := (unitDiskBulk_core grade (scalarResidualJet parameter core)).trans (scalarResidualJet_bulk parameter core)
  apply lhs.trans
  apply Eq.trans _ rhs.symm
  abel

/-- Exact equation in the original completed source grade, initially for
all sources with the actual five-mode projection kept explicit. -/
theorem actualCompletedInverse_scalar (parameters : PhaseParameters) (grade : ℕ)
    (parameter : ℝ) (source : unitDiskSobolev grade) :
    unitScalarOperator grade parameter (actualCompletedInverse grade parameters parameter source) = unitHigh grade source := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_eq ((unitScalarOperator grade parameter).continuous.comp
      (actualCompletedInverse grade parameters parameter).continuous) (unitHigh grade).continuous) _ source
  intro core
  have reconstructed := congrArg (unitScalarOperator grade parameter)
    (actualSmoothInverse_grade parameters parameter core grade).symm
  have equation := sameH1_scalarResidual parameter (highL2Core core)
    (excludedAngularJet lowAngularModes core) (highL2Projection_core core)
    (actualSmoothInverse parameters parameter core) (actualSmoothInverse_H1 parameters parameter core)
  exact reconstructed.trans ((unitScalarOperator_core parameters grade parameter _).trans
    ((congrArg (unitDiskCoreInto grade) equation).trans (unitHigh_core grade core).symm))

theorem actualCompletedInverse_scalar_high (parameters : PhaseParameters) (grade : ℕ)
    (parameter : ℝ) (source : unitDiskSobolev grade) (high : unitDiskBulk grade source ∈ highDiskL2) :
    unitScalarOperator grade parameter (actualCompletedInverse grade parameters parameter source) = source :=
  (actualCompletedInverse_scalar parameters grade parameter source).trans (unitHigh_fixed parameters grade source high)

/-- The completed homogeneous solution has exactly high angular bulk. -/
theorem actualCompletedInverse_high (parameters : PhaseParameters) (grade : ℕ)
    (parameter : ℝ) (source : unitDiskSobolev grade) :
    unitDiskBulk (grade + 2) (actualCompletedInverse grade parameters parameter source) ∈ highDiskL2 :=
  (actualCompletedInverse_bulk grade parameters parameter source).symm ▸
    highDiskBulk_spectral (highRobinWeakInverse parameter (highL2ProjectionInto (unitDiskBulk grade source)))

end Grad.InhomogeneousHighRobin
