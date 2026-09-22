import GC14WeightedSup

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set
open scoped BigOperators ContDiff Topology

namespace Grad.GaugeCoefficients.Physical

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

/-- The literal physical point `ell * Y`, with no analytic-width change. -/
def physicalScaledPoint (ell : ℝ) (ellNonnegative : 0 ≤ ell) (ellLe : ell ≤ 1)
    (point : ClosedDisk) : ClosedDisk :=
  ⟨ell • point.val, by
    change ‖ell • point.val‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg ellNonnegative]
    exact (mul_le_of_le_one_left (norm_nonneg point.val) ellLe).trans point.property⟩

theorem radialPoint_eq_physicalScaledPoint (ell : ℝ) (ellNonnegative : 0 ≤ ell)
    (ellLe : ell ≤ 1) (point : ClosedDisk) :
    radialPoint ell point = physicalScaledPoint ell ellNonnegative ellLe point := by
  apply Subtype.ext
  change unitClamp ell • point.val = ell • point.val
  rw [unitClamp_of_mem ⟨ellNonnegative, ellLe⟩]

def mappedClosedValue {dimension inputDimension outputDimension : ℕ}
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    C(ClosedDisk, OperatorValue inputDimension outputDimension) where
  toFun point := mapping (field point)
  continuous_toFun := mapping.continuous.comp field.continuous

theorem closedDiskLift_mappedClosedValue {dimension inputDimension outputDimension : ℕ}
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    closedDiskLift (mappedClosedValue mapping field) = mapping ∘ closedDiskLift field := by
  funext point
  by_cases membership : point ∈ closedUnitDisk <;>
    simp [closedDiskLift, mappedClosedValue, membership]

theorem mappedClosedDerivative_spec {dimension inputDimension outputDimension : ℕ}
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ClosedJet dimension) (index : CartesianMultiIndex) :
    IsOperatorDerivativeExtension (mappedClosedValue mapping field.value) index
      (mappedClosedValue mapping (closedMultiDerivative field index)) := by
  intro point inside
  rw [closedDiskLift_mappedClosedValue]
  change mapping (closedMultiDerivative field index point) =
    iteratedFDeriv ℝ (cartesianOrder index)
      ((mapping.restrictScalars ℝ) ∘ closedDiskLift field.value) point.val
      (fun position => spatialBasis (cartesianMultiIndexWord index position))
  rw [(mapping.restrictScalars ℝ).iteratedFDeriv_comp_left
    (field.smoothInterior.contDiffAt (openUnitDisk_isOpen.mem_nhds inside))
      (by exact_mod_cast (le_top : (cartesianOrder index : ℕ∞) ≤ ⊤))]
  exact congrArg mapping (closedDerivative_spec field (cartesianOrder index)
    (cartesianMultiIndexWord index) point inside)

def mappedSmoothOperatorJet {dimension inputDimension outputDimension : ℕ}
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ClosedJet dimension) : SmoothOperatorJet inputDimension outputDimension where
  value := mappedClosedValue mapping field.value
  smoothInterior := by
    rw [closedDiskLift_mappedClosedValue]
    exact (mapping.restrictScalars ℝ).contDiff.comp_contDiffOn field.smoothInterior
  derivativeExists index := ⟨mappedClosedValue mapping (closedMultiDerivative field index),
    mappedClosedDerivative_spec mapping field index⟩

theorem mappedSmoothOperatorJet_derivative {dimension inputDimension outputDimension : ℕ}
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ClosedJet dimension) (index : CartesianMultiIndex) (point : ClosedDisk) :
    smoothOperatorDerivative (mappedSmoothOperatorJet mapping field) index point =
      mapping (closedMultiDerivative field index point) := by
  rw [smoothOperatorDerivative_eq_of_spec _ _ _ (mappedClosedDerivative_spec mapping field index)]
  rfl

def scaledOriginalJet {dimension inputDimension outputDimension : ℕ} (ell : ℝ)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ClosedJet dimension) : SmoothOperatorJet inputDimension outputDimension :=
  radialSmoothOperatorJet ell (mappedSmoothOperatorJet mapping field)

theorem scaledOriginalJet_derivative {dimension inputDimension outputDimension : ℕ}
    {ell : ℝ} (ellNonnegative : 0 ≤ ell) (ellLe : ell ≤ 1)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ClosedJet dimension) (index : CartesianMultiIndex) (point : ClosedDisk) :
    smoothOperatorDerivative (scaledOriginalJet ell mapping field) index point =
      (ell ^ cartesianOrder index : ℂ) •
        mapping (closedMultiDerivative field index (radialPoint ell point)) := by
  unfold scaledOriginalJet
  rw [radialSmoothOperatorJet_derivative_apply, mappedSmoothOperatorJet_derivative,
    unitClamp_of_mem ⟨ellNonnegative, ellLe⟩, Complex.ofReal_pow]

theorem originalWeight_scaledPoint {ell : ℝ} (ellNonnegative : 0 ≤ ell) (ellLe : ell ≤ 1)
    (parameters : PhaseParameters) (cell : ℤ) (point : ClosedDisk) :
    originalWeight parameters.sigma0 parameters.gamma ell cell point.val =
      cartesianWeight parameters cell (radialPoint ell point).val := by
  unfold originalWeight cartesianWeight Grad.AnalyticWeights.Calculus.physicalWeight
  change Grad.AnalyticWeights.weight parameters.sigma0 parameters.gamma (ell * ‖point.val‖) cell =
    Grad.AnalyticWeights.weight parameters.sigma0 parameters.gamma
      (1 * ‖unitClamp ell • point.val‖) cell
  rw [unitClamp_of_mem ⟨ellNonnegative, ellLe⟩, norm_smul,
    Real.norm_of_nonneg ellNonnegative, one_mul]

theorem scaledCellWeight_le_frequency {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) :
    scaledCellWeight L ell cell ≤ cellFrequency cell := by
  have lengthPositive := admissible.1
  have ellPositive := admissible.2.2.2.1
  have ellLe : ell ≤ L := admissible.2.2.2.2.trans (min_le_right _ _)
  have ratioNonnegative : 0 ≤ ell / L := div_nonneg ellPositive.le lengthPositive.le
  have ratioLe : ell / L ≤ 1 := (div_le_one lengthPositive).2 ellLe
  have squareLe : ((cell : ℝ) * ell / L) ^ 2 ≤ (cell : ℝ) ^ 2 := by
    rw [mul_div_assoc, mul_pow]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ ratioNonnegative ratioLe)
      (sq_nonneg (cell : ℝ))).trans_eq (mul_one _)
  unfold scaledCellWeight cellFrequency
  exact Real.sqrt_le_sqrt (by linarith)

end Grad.GaugeCoefficients.Physical
