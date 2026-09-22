import AEM21CompletedPhysicalHighCrossRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularOmegaGraph Grad.AnnularTiltedReference Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.Ledger

/-- Literal BE low forcing: a_m j in the first normalized row, and
-mu^-1(L^-1 partial_zeta c + r^-1 R(rV)) in the second. -/
def crossLowSourceSymbol (parameters : PhaseParameters) (length radius : ℝ) (index : LowAnnularIndex)
    (j c rv : ComplexEuclidean 1) : ComplexEuclidean 1 :=
  (if index.1 = 0 then lowAmplitude length parameters.gamma index.2 • j else 0) +
  (if index.1 = 1 then (-Complex.I) • (((index.2.val.2 : ℝ) / length / lowMu length radius index.2.val.2) • c) else 0) +
  (if index.1 = 1 then (-Complex.I) • (((index.2.val.1 : ℝ) * radius⁻¹ / lowMu length radius index.2.val.2) • rv) else 0)

theorem crossLowSourceSymbol_smul (parameters : PhaseParameters) (length radius : ℝ) (index : LowAnnularIndex)
    (j c rv : ComplexEuclidean 1) (scalar : ℂ) :
    crossLowSourceSymbol parameters length radius index (scalar • j) (scalar • c) (scalar • rv) =
      scalar • crossLowSourceSymbol parameters length radius index j c rv := by
  rcases index with ⟨row, mode⟩
  apply PiLp.ext
  intro component
  fin_cases component
  fin_cases row <;> simp [crossLowSourceSymbol, Complex.real_smul] <;> ring

theorem highToLowBulkCross_stored_ae (parameters : PhaseParameters) (lower length compact : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (field : CrossHighSpace lower length positive lengthPositive)
    (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      highToLowBulkCross parameters lower length compact lengthPositive positive bounded state field index radius =
        crossLowSourceSymbol parameters length radius index
          (lowPhysicalRowAction parameters length compact lower positive bounded state 0
            (highCrossSevenInput lower length positive lengthPositive field) index.2.val radius)
          (lowPhysicalRowAction parameters length compact lower positive bounded state 1
            (highCrossSevenInput lower length positive lengthPositive field) index.2.val radius)
          (lowPhysicalRowAction parameters length compact lower positive bounded state 2
            (highCrossSevenInput lower length positive lengthPositive field) index.2.val radius) := by
  let rows := fun row => lowPhysicalRowAction parameters length compact lower positive bounded state row
    (highCrossSevenInput lower length positive lengthPositive field)
  let first := lowFirstOutput parameters lower length (rows 0)
  let second := lowCellOutput lower length positive (rows 1)
  let third := lowAngularOutput lower length positive (rows 2)
  filter_upwards [lowFirstOutput_ae parameters lower length (rows 0) index,
    lowCellOutput_ae lower length positive (rows 1) index,
    lowAngularOutput_ae lower length positive (rows 2) index,
    Lp.coeFn_add (first index + second index) (third index), Lp.coeFn_add (first index) (second index)]
    with radius firstLaw secondLaw thirdLaw totalSum firstSum
  change (first index + second index + third index) radius = _
  rw [totalSum]
  simp only [Pi.add_apply]
  rw [firstSum]
  simp only [Pi.add_apply]
  exact congrArg₂ (fun x y : ComplexEuclidean 1 => x + y)
    (congrArg₂ (fun x y : ComplexEuclidean 1 => x + y) firstLaw secondLaw) thirdLaw

theorem highToLowBulkCross_physical (parameters : PhaseParameters) (lower length compact : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (field : CrossHighSpace lower length positive lengthPositive)
    (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      highToLowBulkCross parameters lower length compact lengthPositive positive bounded state field index radius =
        (lowRhoPhysicalWeight parameters lower positive radius index.2.val : ℂ) •
        crossLowSourceSymbol parameters length radius index
          (highCrossOriginalRow parameters lower length compact positive bounded lengthPositive state field 0 radius index.2.val)
          (highCrossOriginalRow parameters lower length compact positive bounded lengthPositive state field 1 radius index.2.val)
          (highCrossOriginalRow parameters lower length compact positive bounded lengthPositive state field 2 radius index.2.val) := by
  filter_upwards [highToLowBulkCross_stored_ae parameters lower length compact positive bounded lengthPositive state field index]
    with radius actual
  rw [actual]
  unfold highCrossOriginalRow lowRhoPhysicalCoefficient
  rw [crossLowSourceSymbol_smul, smul_inv_smul₀]
  exact_mod_cast (lowRhoPhysicalWeight_pos parameters lower positive radius index.2.val).ne'

end Grad.AnnularCrossMaps
