import AXJ1RealAxisMaps

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 300000

namespace Grad.ChartAxisProjections

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.ChartAxisLift
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.PhysicalCoordinates

variable {parameters : PhaseParameters}

theorem planarJPair_eq_zero_iff (vector : ComplexEuclidean 2) :
    planarJPair vector = 0 ↔ vector = 0 := by
  constructor
  · intro zero
    apply PiLp.ext
    intro index
    fin_cases index
    · exact congrArg (fun v : ComplexEuclidean 2 => v 1) zero
    · have first := congrArg (fun v : ComplexEuclidean 2 => v 0) zero
      change -vector 1 = 0 at first
      exact neg_eq_zero.mp first
  · rintro rfl
    apply PiLp.ext
    intro index
    fin_cases index <;> simp [planarJPair, planarPair]

theorem sigmaExtraction_eq_zero_iff (source : QuotientRows parameters) (cell : ℤ) :
    sigmaExtraction source cell = 0 ↔
      originValue ((source 0).val cell) 0 = 0 ∧ originValue ((source 1).val cell) 0 = 0 := by
  constructor
  · intro zero
    have first := congrArg (fun v : ComplexEuclidean 2 => v 0) zero
    have second := congrArg (fun v : ComplexEuclidean 2 => v 1) zero
    change (_ + _) / (2 : ℂ) = 0 at first
    change (_ - _) / (2 * Complex.I) = 0 at second
    have plus := (div_eq_zero_iff.mp first).resolve_right (by norm_num)
    have minus := (div_eq_zero_iff.mp second).resolve_right (mul_ne_zero two_ne_zero Complex.I_ne_zero)
    constructor
    · linear_combination (1 / 2 : ℂ) * plus + (1 / 2 : ℂ) * minus
    · linear_combination (1 / 2 : ℂ) * plus - (1 / 2 : ℂ) * minus
  · intro ⟨first, second⟩
    apply PiLp.ext
    intro index
    fin_cases index <;> simp [sigmaExtraction, planarPair, first, second]

theorem etaExtraction_eq_zero_iff (cellLength : ℝ) (positive : 0 < cellLength)
    (source : QuotientRows parameters) (cell : ℤ) (sigma : sigmaExtraction source cell = 0) :
    etaExtraction cellLength source cell = 0 ↔ scalarOriginGradient (source 3) cell = 0 := by
  have nonzero : (cellLength : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr positive.ne')
  rw [etaExtraction, sigma, smul_zero, add_zero, smul_eq_zero]
  simp only [nonzero, false_or, planarJPair_eq_zero_iff]

theorem realExtraction_eq_zero_iff (cellLength : ℝ) (source : sourceSmoothRange parameters) :
    realExtraction parameters cellLength source = 0 ↔
      (∀ cell, sigmaExtraction source.val cell = 0) ∧
      (∀ cell, etaExtraction cellLength source.val cell = 0) := by
  constructor
  · intro zero
    constructor
    · intro cell
      exact congrArg (fun data : RealAxis parameters => data.val.1.val cell) zero
    · intro cell
      exact congrArg (fun data : RealAxis parameters => data.val.2.val cell) zero
  · intro ⟨sigma, eta⟩
    apply Subtype.ext
    apply axisData_ext
    apply Prod.ext
    · exact funext sigma
    · exact funext eta

/-- AL24 on the original real compatible source core; no source projection
or extra compatibility hypothesis is introduced. -/
theorem realSourceFlat_iff_jets (cellLength : ℝ) (positive : 0 < cellLength)
    (source : sourceSmoothRange parameters) :
    source ∈ LinearMap.ker (realExtraction parameters cellLength) ↔
      ∀ cell, originValue ((source.val 0).val cell) 0 = 0 ∧
        originValue ((source.val 1).val cell) 0 = 0 ∧
        scalarOriginGradient (source.val 3) cell = 0 := by
  change realExtraction parameters cellLength source = 0 ↔ _
  rw [realExtraction_eq_zero_iff]
  constructor
  · intro ⟨sigma, eta⟩ cell
    obtain ⟨plus, minus⟩ := (sigmaExtraction_eq_zero_iff source.val cell).mp (sigma cell)
    exact ⟨plus, minus, (etaExtraction_eq_zero_iff cellLength positive source.val cell (sigma cell)).mp (eta cell)⟩
  · intro jets
    have sigma (cell : ℤ) : sigmaExtraction source.val cell = 0 :=
      (sigmaExtraction_eq_zero_iff source.val cell).mpr ⟨(jets cell).1, (jets cell).2.1⟩
    exact ⟨sigma, fun cell =>
      (etaExtraction_eq_zero_iff cellLength positive source.val cell (sigma cell)).mpr (jets cell).2.2⟩

end Grad.ChartAxisProjections
