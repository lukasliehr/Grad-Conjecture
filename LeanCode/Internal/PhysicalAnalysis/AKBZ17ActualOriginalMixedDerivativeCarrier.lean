import AKBZ16SharpFullCellKernel

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.CartesianState Grad.NonlinearProduct Grad.BoundaryTrace Grad.GenericCarriers

/-- The physical scaled cell weight never exceeds the original lambda. -/
theorem scaledCellWeight_le_original {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) :
    scaledCellWeight L ell cell≤cellFrequency cell :=
  Grad.GaugeCoefficients.Physical.scaledCellWeight_le_frequency admissible cell

/-- One literal original phase-weighted derivative with exactly the chosen
scaled input moments. Its norm is paid by the corresponding total grade. -/
def originalMixedDerivativeCoordinate {dimension : ℕ} (parameters : PhaseParameters)
    (L ell : ℝ) (field : ACore parameters dimension) (rank moment : ℕ)
    (word : CartesianWord rank) (cell : ℤ) : DiskL2 dimension :=
  (scaledCellWeight L ell cell:ℂ)^moment •
    closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters cell (field.val cell)) rank word)

theorem originalMixedDerivativeCoordinate_bound {dimension : ℕ} (parameters : PhaseParameters)
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : ACore parameters dimension) (rank moment : ℕ) (word : CartesianWord rank) (cell : ℤ) :
    ‖originalMixedDerivativeCoordinate parameters L ell field rank moment word cell‖≤
      ‖cellGradeRowLinear (grade:=rank+moment) parameters cell (field.val cell)‖ := by
  have rankLe : rank≤rank+moment := Nat.le_add_right _ _
  have bound := Grad.Constraints.weighted_word_norm_le_row parameters cell (field.val cell) rankLe word
  rw [Nat.add_sub_cancel_left] at bound
  unfold originalMixedDerivativeCoordinate
  rw [norm_smul,Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg (scaledCellWeight_nonnegative L ell cell)]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (scaledCellWeight_nonnegative L ell cell)
    (scaledCellWeight_le_original admissible cell) moment) (norm_nonneg _)).trans bound

theorem originalMixedDerivativeCoordinate_summable {dimension : ℕ} (parameters : PhaseParameters)
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : ACore parameters dimension) (rank moment : ℕ) (word : CartesianWord rank) :
    Summable (fun cell => ‖originalMixedDerivativeCoordinate parameters L ell field rank moment word cell‖^2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun cell => pow_le_pow_left₀ (norm_nonneg _)
      (originalMixedDerivativeCoordinate_bound parameters admissible field rank moment word cell) 2)
    (original_rows_summable (grade:=rank+moment) parameters field)

/-- Full-cell L2 realization via the already accepted cell/space isometry. -/
def originalMixedDerivativeCarrier {dimension : ℕ} (parameters : PhaseParameters)
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : ACore parameters dimension) (rank moment : ℕ) (word : CartesianWord rank) :
    FieldL2 dimension openUnitDisk :=
  (Grad.FullCellKernel.exchange dimension openUnitDisk).symm
    ⟨originalMixedDerivativeCoordinate parameters L ell field rank moment word,
      (memlp_iff_summable_sq _).mpr (originalMixedDerivativeCoordinate_summable parameters admissible field rank moment word)⟩

theorem originalMixedDerivativeCarrier_coordinate {dimension : ℕ} (parameters : PhaseParameters)
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : ACore parameters dimension) (rank moment : ℕ) (word : CartesianWord rank) (cell : ℤ) :
    fieldCellProjection dimension openUnitDisk cell
      (originalMixedDerivativeCarrier parameters admissible field rank moment word)=
    originalMixedDerivativeCoordinate parameters L ell field rank moment word cell :=
  Grad.FullCellKernel.exchange_symm_coordinate dimension openUnitDisk _ cell

theorem originalMixedDerivativeCarrier_norm {dimension : ℕ} (parameters : PhaseParameters)
    {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : ACore parameters dimension) (rank moment : ℕ) (word : CartesianWord rank) :
    ‖originalMixedDerivativeCarrier parameters admissible field rank moment word‖≤originalGradeNorm (rank+moment) field := by
  apply (sq_le_sq₀ (norm_nonneg _) (originalGradeNorm_nonnegative _ field)).mp
  unfold originalMixedDerivativeCarrier
  rw [(Grad.FullCellKernel.exchange dimension openUnitDisk).symm.norm_map,
    Grad.SchurKernel.Discrete.lp_norm_sq]
  rw [show originalGradeNorm (rank+moment) field^2=∑' cell : ℤ,
      ‖cellGradeRowLinear (grade:=rank+moment) parameters cell (field.val cell)‖^2 by
    exact originalGrade_norm_sq_eq_rows parameters field]
  exact (originalMixedDerivativeCoordinate_summable parameters admissible field rank moment word).tsum_le_tsum
    (fun cell => pow_le_pow_left₀ (norm_nonneg _)
      (originalMixedDerivativeCoordinate_bound parameters admissible field rank moment word cell) 2)
    (original_rows_summable (grade:=rank+moment) parameters field)

end Grad.OriginalCartesianTameEstimate
