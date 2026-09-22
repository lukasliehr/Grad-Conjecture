import AKDN10SameNativeEulerGrades

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularWeightedSystem Grad.BoundaryLift

section Affine
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineEulerJets (constant slope : E) (rank : ℕ) (radius : ℝ) : E :=
  (if rank=0 then constant else 0)+radius • slope

theorem affineEulerJets_derivative (constant slope : E) (rank : ℕ)
    (domain : Set ℝ) (radius : ℝ) (nonzero : radius ≠ 0) :
    HasDerivWithinAt (affineEulerJets constant slope rank)
      (radius⁻¹ • affineEulerJets constant slope (rank+1) radius) domain radius := by
  have derivative := ((hasDerivWithinAt_id radius domain).smul_const slope).const_add
    (if rank=0 then constant else 0)
  change HasDerivWithinAt (affineEulerJets constant slope rank) ((1 : ℝ) • slope) domain radius at derivative
  simpa only [affineEulerJets,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,zero_add,one_smul,
    inv_smul_smul₀ nonzero] using derivative

theorem affineEulerJets_fidelity (constant slope : E) (domain : Set ℝ)
    (unique : UniqueDiffOn ℝ domain) (nonzero : ∀ radius ∈ domain, radius ≠ 0)
    (rank : ℕ) (radius : ℝ) (inside : radius ∈ domain) :
    vectorEulerWithinIteratedDerivative domain rank (fun point => constant+point • slope) radius =
      affineEulerJets constant slope rank radius :=
  vectorEulerWithinIteratedDerivative_tower domain unique nonzero (affineEulerJets constant slope)
    (fun order point member => affineEulerJets_derivative constant slope order domain point (nonzero point member)) rank inside

theorem affineEulerJets_bound (constant slope : E) (rank : ℕ) (radius : RadialPoint) :
    ‖affineEulerJets constant slope rank radius‖ ≤ ‖constant‖+‖slope‖ := by
  have left : ‖(if rank=0 then constant else (0 : E))‖ ≤ ‖constant‖ := by
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg constant
  have right : ‖radius.val • slope‖ ≤ ‖slope‖ := by
    rw [norm_smul,Real.norm_of_nonneg radius.property.1]
    exact mul_le_of_le_one_left (norm_nonneg slope) radius.property.2
  exact (norm_add_le _ _).trans (add_le_add left right)

end Affine

def balancedSevenInputSlope (parameters : PhaseParameters) : PhysicalHilbertPair →L[ℂ] CellL2 7 :=
  (hilbertSlotInjection parameters 2).comp ((hilbertFrequencyOperator parameters 1 (some true)).comp
    (ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1)))

theorem balancedSevenInput_affine (parameters : PhaseParameters) (radius : ℝ) :
    balancedSevenInput parameters radius = balancedSevenInput parameters 0+radius • balancedSevenInputSlope parameters := by
  have scalar : (radius : ℂ) • balancedSevenInputSlope parameters = radius • balancedSevenInputSlope parameters := by
    apply ContinuousLinearMap.ext
    intro field
    apply lp.ext
    funext mode
    change (radius : ℂ) • (balancedSevenInputSlope parameters field mode) = radius • (balancedSevenInputSlope parameters field mode)
    exact Complex.coe_smul radius _
  unfold balancedSevenInputSlope at scalar
  unfold balancedSevenInput balancedSevenInputSlope
  simp only [Complex.ofReal_zero,zero_smul,add_zero]
  rw [scalar]
  abel

def balancedSevenInputEuler (parameters : PhaseParameters) : ℕ → ℝ → (PhysicalHilbertPair →L[ℂ] CellL2 7) :=
  affineEulerJets (balancedSevenInput parameters 0) (balancedSevenInputSlope parameters)

theorem balancedSevenInputEuler_zero (parameters : PhaseParameters) (radius : ℝ) :
    balancedSevenInputEuler parameters 0 radius = balancedSevenInput parameters radius := by
  change balancedSevenInput parameters 0+radius • balancedSevenInputSlope parameters = _
  exact (balancedSevenInput_affine parameters radius).symm

theorem balancedSevenInputEuler_fidelity (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (rank : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    vectorEulerWithinIteratedDerivative (Icc lower 1) rank (balancedSevenInput parameters) radius =
      balancedSevenInputEuler parameters rank radius := by
  have same : balancedSevenInput parameters = fun point => balancedSevenInput parameters 0+point • balancedSevenInputSlope parameters :=
    funext (balancedSevenInput_affine parameters)
  rw [same]
  exact affineEulerJets_fidelity _ _ (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun point member => (positive.trans_le member.1).ne') rank radius inside

theorem balancedSevenInputEuler_bound (parameters : PhaseParameters) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ rank : ℕ, ∀ radius : RadialPoint,
      ‖balancedSevenInputEuler parameters rank radius‖ ≤ constant :=
  ⟨‖balancedSevenInput parameters 0‖+‖balancedSevenInputSlope parameters‖,
    add_nonneg (norm_nonneg _) (norm_nonneg _),fun rank radius => affineEulerJets_bound _ _ rank radius⟩

end Grad.OriginalCartesianTameEstimate
