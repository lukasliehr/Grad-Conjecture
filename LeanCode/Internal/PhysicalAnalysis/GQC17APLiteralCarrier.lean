import GQC16APSmoothCarrier

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

theorem apLiteral_mem {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (fields : ℤ → ClosedJet dimension)
    (summable : Memℓp (fun cell => apRowLinear (grade := grade) L sigma gamma ell cell (fields cell)) 2) :
    (⟨fun cell => apRowLinear (grade := grade) L sigma gamma ell cell (fields cell), summable⟩ : APAmbient dimension grade) ∈
      apGrade L sigma gamma ell dimension grade := by
  let ambient : APAmbient dimension grade := ⟨_, summable⟩
  have convergence := lp.hasSum_single (p := 2) (by norm_num) ambient
  apply (apSmoothCore L sigma gamma ell dimension grade).isClosed_topologicalClosure.mem_of_tendsto convergence
  exact Filter.Eventually.of_forall (fun support =>
    (apGrade L sigma gamma ell dimension grade).sum_mem (fun cell _ =>
      (apSmoothCore L sigma gamma ell dimension grade).le_topologicalClosure
        (Submodule.subset_span ⟨(cell, fields cell), rfl⟩)))

def apLiteralGrade {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (fields : ℤ → ClosedJet dimension)
    (summable : Memℓp (fun cell => apRowLinear (grade := grade) L sigma gamma ell cell (fields cell)) 2) :
    apGrade L sigma gamma ell dimension grade :=
  ⟨⟨_, summable⟩, apLiteral_mem L sigma gamma ell fields summable⟩

theorem apLiteralGrade_unscaled {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (fields : ℤ → ClosedJet dimension)
    (summable : Memℓp (fun cell => apRowLinear (grade := grade) L sigma gamma ell cell (fields cell)) 2)
    (cell : ℤ) (index : DerivativeIndex grade) :
    apUnscaledCoordinate L sigma gamma ell cell index (apLiteralGrade L sigma gamma ell fields summable) =
      closedDerivativeL2 (derivativeMultiIndex index) (apWeightedJet sigma gamma ell cell (fields cell)) := by
  change ((scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index))⁻¹ •
    (apRowLinear L sigma gamma ell cell (fields cell) index) = _
  rw [apRowLinear_apply, smul_smul, inv_mul_cancel₀, one_smul]
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
    (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell cell)).ne')

theorem apLiteralGrade_lowering {dimension low high : ℕ} (L sigma gamma ell : ℝ)
    (ordered : low ≤ high) (fields : ℤ → ClosedJet dimension)
    (lowSummable : Memℓp (fun cell => apRowLinear (grade := low) L sigma gamma ell cell (fields cell)) 2)
    (highSummable : Memℓp (fun cell => apRowLinear (grade := high) L sigma gamma ell cell (fields cell)) 2) :
    apLowering L sigma gamma ell ordered (apLiteralGrade L sigma gamma ell fields highSummable) =
      apLiteralGrade L sigma gamma ell fields lowSummable := by
  apply apGrade_ext L sigma gamma ell
  intro cell
  rw [apUnscaledCoordinate_lowering L sigma gamma ell ordered cell (zeroGradeIndex low) (zeroGradeIndex high) rfl,
    apLiteralGrade_unscaled, apLiteralGrade_unscaled]
  rfl

def apLiteralSmooth {dimension : ℕ} (L sigma gamma ell : ℝ) (fields : ℤ → ClosedJet dimension)
    (summable : ∀ grade : ℕ, Memℓp (fun cell => apRowLinear (grade := grade) L sigma gamma ell cell (fields cell)) 2) :
    APSmooth L sigma gamma ell dimension :=
  ⟨fun grade => apLiteralGrade L sigma gamma ell fields (summable grade),
    fun _low _high ordered => apLiteralGrade_lowering L sigma gamma ell ordered fields _ _⟩

theorem apSmoothJet_summable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) (grade : ℕ) :
    Memℓp (fun cell => apRowLinear (grade := grade) L sigma gamma ell cell (apSmoothJet admissible dimension cell field)) 2 := by
  simp_rw [apSmoothJet_row]
  exact (apSmoothGrade L sigma gamma ell dimension grade field).val.property

theorem apLiteralSmooth_reconstruction {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) :
    apLiteralSmooth L sigma gamma ell (fun cell => apSmoothJet admissible dimension cell field)
      (apSmoothJet_summable admissible field) = field := by
  apply Subtype.ext
  funext grade
  apply Subtype.ext
  apply lp.ext
  funext cell
  exact apSmoothJet_row admissible field grade cell

end Grad.GaugeCoefficients.Physical.Compensated
