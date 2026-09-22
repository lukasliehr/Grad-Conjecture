import AKCW1SameOriginalCollarExtension
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set
open scoped ContDiff Topology
namespace Grad.OriginalParameterEvaluation
open Grad.CartesianState Grad.CompatibleCompletion

variable {dimension : ℕ} (parameters : PhaseParameters)
variable {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

/-- The same original field in each of its actual completions. -/
def completedCoreBranch (field : Parameter → ACore parameters dimension) (grade : ℕ) :
    Parameter → AGrade parameters dimension grade :=
  fun point => aGradeEta parameters (GradeCore.ofCoreLinear (field point))

omit [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter] in
theorem completedCoreBranch_inclusion (field : Parameter → ACore parameters dimension)
    {lower upper : ℕ} (ordered : lower ≤ upper) (point : Parameter) :
    completedInclusion parameters ordered (completedCoreBranch parameters field upper point)=
      completedCoreBranch parameters field lower point :=
  completedInclusion_apply_eta parameters ordered _

/-- Differentiating the exact grade-inclusion identity gives compatibility
of the completed parameter derivatives. -/
theorem completedCoreDerivative_compatible (field : Parameter → ACore parameters dimension)
    (point : Parameter)
    (differentiable : ∀ grade, DifferentiableAt ℝ (completedCoreBranch parameters field grade) point)
    {lower upper : ℕ} (ordered : lower ≤ upper) (direction : Parameter) :
    completedInclusion parameters ordered
      (fderiv ℝ (completedCoreBranch parameters field upper) point direction)=
      fderiv ℝ (completedCoreBranch parameters field lower) point direction := by
  have upperDerivative := ((completedInclusion (dimension := dimension) parameters ordered).restrictScalars ℝ).hasFDerivAt.comp point
    (differentiable upper).hasFDerivAt
  have lowerDerivative : HasFDerivAt (completedCoreBranch parameters field lower)
      (((completedInclusion (dimension := dimension) parameters ordered).restrictScalars ℝ).comp
        (fderiv ℝ (completedCoreBranch parameters field upper) point)) point := by
    change HasFDerivAt (fun input => completedInclusion parameters ordered
      (completedCoreBranch parameters field upper input)) _ _ at upperDerivative
    simpa only [completedCoreBranch_inclusion] using upperDerivative
  exact DFunLike.congr_fun (lowerDerivative.unique (differentiable lower).hasFDerivAt) direction

/-- One actual original-core parameter derivative, reconstructed simultaneously
from every original completed grade. No grade-dependent representative is chosen. -/
def originalParameterDerivative (field : Parameter → ACore parameters dimension)
    (point : Parameter)
    (differentiable : ∀ grade, DifferentiableAt ℝ (completedCoreBranch parameters field grade) point) :
    Parameter →ₗ[ℝ] ACore parameters dimension :=
  ((compatibleToCore parameters).restrictScalars ℝ).comp
    ((LinearMap.pi (fun grade =>
      (fderiv ℝ (completedCoreBranch parameters field grade) point).toLinearMap)).codRestrict
      ((compatibleAGradesSubmodule parameters dimension).restrictScalars ℝ) (by
        intro direction lower upper ordered
        exact completedCoreDerivative_compatible parameters field point differentiable ordered direction))

theorem originalParameterDerivative_component (field : Parameter → ACore parameters dimension)
    (point : Parameter)
    (differentiable : ∀ grade, DifferentiableAt ℝ (completedCoreBranch parameters field grade) point)
    (grade : ℕ) (direction : Parameter) :
    aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade)
      (originalParameterDerivative parameters field point differentiable direction))=
      fderiv ℝ (completedCoreBranch parameters field grade) point direction :=
  compatibleToCore_component parameters _ grade

/-- The reconstructed derivative is continuous in each literal original norm. -/
def originalParameterDerivativeAtGrade (field : Parameter → ACore parameters dimension)
    (point : Parameter)
    (differentiable : ∀ grade, DifferentiableAt ℝ (completedCoreBranch parameters field grade) point)
    (grade : ℕ) : Parameter →L[ℝ] GradeCore parameters dimension grade :=
  (((GradeCore.ofCoreLinear (parameters := parameters) (dimension := dimension) (grade := grade)).restrictScalars ℝ).comp
    (originalParameterDerivative parameters field point differentiable)).mkContinuous
    ‖fderiv ℝ (completedCoreBranch parameters field grade) point‖ (by
      intro direction
      rw [← aGradeEta_norm parameters]
      change ‖aGradeEta parameters (GradeCore.ofCoreLinear
        (originalParameterDerivative parameters field point differentiable direction))‖≤_
      rw [originalParameterDerivative_component]
      exact (fderiv ℝ (completedCoreBranch parameters field grade) point).le_opNorm direction)

/-- The reconstructed map is the actual Fréchet derivative in every original
norm, reflected through the faithful isometric completion embedding. -/
theorem originalParameterDerivative_hasFDerivAt
    (field : Parameter → ACore parameters dimension) (point : Parameter)
    (differentiable : ∀ grade, DifferentiableAt ℝ (completedCoreBranch parameters field grade) point)
    (grade : ℕ) :
    HasFDerivAt (fun input => GradeCore.ofCoreLinear (grade := grade) (field input))
      (originalParameterDerivativeAtGrade parameters field point differentiable grade) point := by
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_norm_left
  have completedRemainder := (differentiable grade).hasFDerivAt.isLittleO.norm_left
  convert completedRemainder using 1
  funext input
  rw [← aGradeEta_norm parameters]
  change ‖aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (field input) -
    GradeCore.ofCoreLinear (field point) - GradeCore.ofCoreLinear
      (originalParameterDerivative parameters field point differentiable (input-point)))‖=_
  simp only [map_sub, originalParameterDerivative_component, completedCoreBranch]

end Grad.OriginalParameterEvaluation
