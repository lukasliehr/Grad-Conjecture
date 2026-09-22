import AEA7UniformNormalizedCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowReference
open Grad.ClosedJets Grad.CartesianState Grad.AnnularLowEnergy Grad.AnnularVariational
open Grad.AnnularGrades

def lowSwapIndex : LowAnnularIndex ≃ LowAnnularIndex :=
  Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl LowAnnularMode)

def lowSwapFamily (field : LowEnergyBoundary) : LowEnergyBoundary :=
  ⟨fun index => field (lowSwapIndex index), by
    have original := (memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp field)
    exact (memℓp_gen_iff (p := 2) (by norm_num)).mpr (lowSwapIndex.summable_iff.mpr original)⟩

theorem lowSwapFamily_norm (field : LowEnergyBoundary) : ‖lowSwapFamily field‖ = ‖field‖ := by
  have first := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (lowSwapFamily field)
  have second := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at first second
  have reindex := lowSwapIndex.tsum_eq (fun index => ‖field index‖ ^ 2)
  have square : ‖lowSwapFamily field‖ ^ 2 = ‖field‖ ^ 2 := first.trans (reindex.trans second.symm)
  nlinarith [norm_nonneg (lowSwapFamily field), norm_nonneg field]

def lowSwapLinear : LowEnergyBoundary →ₗ[ℂ] LowEnergyBoundary where
  toFun := lowSwapFamily
  map_add' first second := by apply lp.ext; funext index; rfl
  map_smul' scalar field := by apply lp.ext; funext index; rfl

def lowSwap : LowEnergyBoundary →L[ℂ] LowEnergyBoundary :=
  lowSwapLinear.mkContinuous 1 (fun field => by
    change ‖lowSwapFamily field‖ ≤ 1 * ‖field‖
    rw [one_mul]
    exact (lowSwapFamily_norm field).le)

theorem lowSwap_apply (field : LowEnergyBoundary) (index : LowAnnularIndex) :
    lowSwap field index = field (lowSwapIndex index) := rfl

theorem lowSwap_norm (field : LowEnergyBoundary) : ‖lowSwap field‖ = ‖field‖ := lowSwapFamily_norm field

def lowNormalizedReferenceCoefficient (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (row column : Fin 2) : ℝ :=
  lowReferenceMatrix parameters length radius mode row column / lowMu length radius mode.val.2

theorem lowNormalizedReferenceCoefficient_bound (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < radius) (bounded : radius ≤ 1)
    (mode : LowAnnularMode) (row column : Fin 2) :
    |lowNormalizedReferenceCoefficient parameters length radius mode row column| ≤
      lowReferenceCoefficientConstant parameters length := by
  rw [lowNormalizedReferenceCoefficient, abs_div, abs_of_pos (lowMu_pos length radius mode.val.2 positive)]
  exact (div_le_iff₀ (lowMu_pos length radius mode.val.2 positive)).mpr
    (lowReferenceMatrix_bound parameters length radius lengthPositive positive bounded mode row column)

/-- mu^-1 Gref on the literal ADY all-mode low Hilbert space. The off-diagonal
term swaps only the two components of the SAME physical Fourier mode. -/
def lowNormalizedReference (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < radius) (bounded : radius ≤ 1) :
    LowEnergyBoundary →L[ℂ] LowEnergyBoundary :=
  realLpDiagonal (fun index : LowAnnularIndex => lowNormalizedReferenceCoefficient parameters length radius index.2 index.1 index.1)
    (lowReferenceCoefficientConstant parameters length) (lowReferenceCoefficientConstant_pos parameters length lengthPositive).le
    (fun index => lowNormalizedReferenceCoefficient_bound parameters length radius lengthPositive positive bounded index.2 index.1 index.1) +
  (realLpDiagonal (fun index : LowAnnularIndex => lowNormalizedReferenceCoefficient parameters length radius index.2 index.1 (lowSwapIndex index).1)
    (lowReferenceCoefficientConstant parameters length) (lowReferenceCoefficientConstant_pos parameters length lengthPositive).le
    (fun index => lowNormalizedReferenceCoefficient_bound parameters length radius lengthPositive positive bounded index.2 index.1 (lowSwapIndex index).1)).comp lowSwap

theorem lowNormalizedReference_bound (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < radius) (bounded : radius ≤ 1) (field : LowEnergyBoundary) :
    ‖lowNormalizedReference parameters length radius lengthPositive positive bounded field‖ ≤
      (2 * lowReferenceCoefficientConstant parameters length) * ‖field‖ := by
  let diagonal := fun index : LowAnnularIndex =>
    lowNormalizedReferenceCoefficient parameters length radius index.2 index.1 index.1
  let offDiagonal := fun index : LowAnnularIndex =>
    lowNormalizedReferenceCoefficient parameters length radius index.2 index.1 (lowSwapIndex index).1
  have diagonalBound := realLpDiagonal_bound diagonal
    (lowReferenceCoefficientConstant parameters length)
    (lowReferenceCoefficientConstant_pos parameters length lengthPositive).le
    (fun index => lowNormalizedReferenceCoefficient_bound parameters length radius lengthPositive positive bounded index.2 index.1 index.1) field
  have offDiagonalBound := realLpDiagonal_bound offDiagonal
    (lowReferenceCoefficientConstant parameters length)
    (lowReferenceCoefficientConstant_pos parameters length lengthPositive).le
    (fun index => lowNormalizedReferenceCoefficient_bound parameters length radius lengthPositive positive bounded index.2 index.1 (lowSwapIndex index).1) (lowSwap field)
  exact (norm_add_le _ _).trans
    ((add_le_add diagonalBound offDiagonalBound).trans_eq (by rw [lowSwap_norm]; ring))

/-- Exact matrix action, including both signs and n=0 on the original carrier. -/
theorem lowNormalizedReference_apply (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < radius) (bounded : radius ≤ 1)
    (field : LowEnergyBoundary) (index : LowAnnularIndex) :
    lowNormalizedReference parameters length radius lengthPositive positive bounded field index =
      (lowReferenceMatrix parameters length radius index.2 index.1 0 / lowMu length radius index.2.val.2 : ℂ) • field (0, index.2) +
      (lowReferenceMatrix parameters length radius index.2 index.1 1 / lowMu length radius index.2.val.2 : ℂ) • field (1, index.2) := by
  change (lowNormalizedReferenceCoefficient parameters length radius index.2 index.1 index.1 : ℂ) • field index +
    (lowNormalizedReferenceCoefficient parameters length radius index.2 index.1 (lowSwapIndex index).1 : ℂ) • field (lowSwapIndex index) = _
  rcases index with ⟨row, mode⟩
  fin_cases row
  · simp [lowSwapIndex, lowNormalizedReferenceCoefficient]
  · simp [lowSwapIndex, lowNormalizedReferenceCoefficient, add_comm]

end Grad.AnnularLowReference
