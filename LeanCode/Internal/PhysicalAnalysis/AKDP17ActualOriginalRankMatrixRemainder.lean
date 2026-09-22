import AKDP16ActualOriginalMatrixTame

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate Grad.CartesianCoreRecovery Grad.TensorBootstrap
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- The literal flattened full ordered derivative tensor of the original
weighted core, with no chosen graph in its definition. -/
def startupOriginalRankField {dimension : ℕ} (parameters : PhaseParameters)
    (rank : ℕ) (core : ACore parameters dimension) : StartupL2 (startupTensorDimension dimension rank) :=
  startupTensorFieldEquiv dimension rank (WithLp.toLp 2
    (fun word : TensorBootstrap.DerivativeIndex rank => originalSourceOrderedJoint parameters core rank word))

theorem startupOriginalRankField_graph {dimension order rank weight : ℕ}
    (parameters : PhaseParameters) (core : ACore parameters dimension)
    (jet : GraphGrade dimension order weight openUnitDisk)
    (same : base dimension order openUnitDisk (fun _ => weight) jet = (originalSourceMoments parameters core).field)
    (bound : rank≤order) :
    startupTensorFieldEquiv dimension rank
      (orderedDerivative dimension order rank openUnitDisk (fun _ => weight) bound jet) =
      startupOriginalRankField parameters rank core := by
  apply congrArg (startupTensorFieldEquiv dimension rank)
  apply PiLp.ext
  intro word
  exact startupOrdered_originalCore parameters core jet same bound word

/-- Exact rank remainder of the genuine original matrix, represented by
the already constructed nonempty-allocation tensor. -/
theorem startupOriginalMatrix_rankRemainder_exact {input output rank weight : ℕ}
    (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (family : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output) (coherent : FamilyCoherent family)
    (core : ACore parameters input) (image : ACore parameters output)
    (same : (originalSourceMoments parameters image).field =
      originalMatrixKernel admissible family coherent (originalSourceMoments parameters core).field)
    (jet : GraphGrade input rank weight openUnitDisk)
    (jetSame : base input rank openUnitDisk (fun _ => weight) jet = (originalSourceMoments parameters core).field)
    (reserve : rank-1≤weight) :
    startupOriginalRankField parameters rank image-
      (StartupRankOperator.matrix admissible rank family coherent).coarse (startupOriginalRankField parameters rank core) =
    startupTensorFieldEquiv output rank (WithLp.toLp 2 (fun word : TensorBootstrap.DerivativeIndex rank =>
      startupMatrixOrderedRemainder admissible family coherent word le_rfl reserve jet)) := by
  let source : Tensor rank (StartupL2 input) := WithLp.toLp 2 (fun word => originalSourceOrderedJoint parameters core rank word)
  let target : Tensor rank (StartupL2 output) := WithLp.toLp 2 (fun word => originalSourceOrderedJoint parameters image rank word)
  let remainder : Tensor rank (StartupL2 output) := WithLp.toLp 2 (fun word =>
    startupMatrixOrderedRemainder admissible family coherent word le_rfl reserve jet)
  have tensorSame : target = hilbertLift (originalMatrixKernel admissible family coherent) source+remainder := by
    apply PiLp.ext
    intro word
    have actual := originalSourceOrderedJoint_weak parameters image rank word
    change HasWeakOrderedDerivative output openUnitDisk rank word (originalSourceMoments parameters image).field _ at actual
    rw [same] at actual
    have leading := startupActualMatrix_weakLeadingSplit admissible family coherent word le_rfl reserve jet
    rw [jetSame,startupOrdered_originalCore parameters core jet jetSame] at leading
    exact weakEquality output openUnitDisk openUnitDisk_isOpen rank word word (fun _ => rfl) _ _ _ actual leading
  change startupTensorFieldEquiv output rank target-
    (StartupRankOperator.entrywise rank (originalMatrixKernel admissible family coherent)
      (startupMatrixFirstGraphCLM admissible family coherent) (startupMatrixFirstGraph_compatible admissible family coherent)).coarse
        (startupTensorFieldEquiv input rank source) = startupTensorFieldEquiv output rank remainder
  rw [StartupRankOperator.entrywise_coarse,← map_sub,tensorSame,add_sub_cancel_left]

/-- Quantitative rank remainder for arbitrary actual original matrix
families. It preserves the SAME original core and uses only M_rank and
one coefficient of rank+offset times the independent M0. -/
theorem startupOriginalMatrix_rankRemainder_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (lengthNonzero : L≠0) (scaleNonzero : ell≠0)
    (offset rank : ℕ) (profile : EstimateProfile)
    (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧
    ∀ (input output : ℕ) (baseField : ACore parameters 3) (rho curvature : ℝ)
      (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
      (estimate : FamilyEstimate parameters baseField rho curvature offset profile family reference)
      (core : ACore parameters input) (image : ACore parameters output),
      (originalSourceMoments parameters image).field =
        originalMatrixKernel admissible family estimate.actualCoherent (originalSourceMoments parameters core).field →
      physicalBudget parameters baseField rho curvature offset≤1 →
      ‖startupOriginalRankField parameters rank image-
        (StartupRankOperator.matrix admissible rank family estimate.actualCoherent).coarse (startupOriginalRankField parameters rank core)‖ ≤
        epsilon*originalGradeNorm rank core+
          constant*((1+physicalBudget parameters baseField rho curvature (offset+rank))*originalGradeNorm 0 core) := by
  obtain ⟨constant,nonnegative,bound⟩ := startupMatrixTensorRemainder_oneHigh parameters admissible offset rank profile
    fixedNonnegative deviationNonnegative epsilon epsilonPositive
  refine ⟨constant,nonnegative,?_⟩
  intro input output baseField rho curvature family reference estimate core image same low
  obtain ⟨jet,jetSame⟩ := startupOriginal_reservedGraph parameters core lengthNonzero scaleNonzero rank rank
  rw [startupOriginalMatrix_rankRemainder_exact parameters admissible family estimate.actualCoherent core image same jet jetSame
    (by omega : rank-1≤rank),LinearIsometryEquiv.norm_map]
  exact bound input output rank rank baseField rho curvature family reference estimate core jet jetSame le_rfl (by omega) low

end Grad.CartesianStartup
