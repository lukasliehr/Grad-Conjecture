import AKAQ10ActualA4FourierDecay

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalFlatAxisDecay
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets Grad.COR12Extension
open Grad.COR13Completion Grad.SourceCollarDivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def weightedCellVector (values : ℤ → E)
    (member : Memℓp (fun cell => (cellFrequency cell : ℂ) • values cell) 2) :
    lp (fun _ : ℤ => E) 2 := ⟨_,member⟩

theorem weightedCellVector_bound (values : ℤ → E)
    (member : Memℓp (fun cell => (cellFrequency cell : ℂ) • values cell) 2)
    (constant radius size : ℝ) (constantNonnegative : 0 ≤ constant)
    (radiusNonnegative : 0 ≤ radius) (sizeNonnegative : 0 ≤ size)
    (energy : ∀ cells : Finset ℤ, ∑ cell ∈ cells, cellFrequency cell^2 * ‖values cell‖^2 ≤
      constant * radius^3 * size^2) :
    ‖weightedCellVector values member‖ ≤ Real.sqrt constant * radius^(3/2:ℝ) * size := by
  have radiusSquare : (radius^(3/2:ℝ))^2 = radius^3 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul radiusNonnegative]
    norm_num
  apply lp.norm_le_of_forall_sum_le (p := 2) (by norm_num) (by positivity)
  intro cells
  simp only [weightedCellVector,ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (cellFrequency_pos _),mul_pow]
  have bound := energy cells
  rw [Real.sq_sqrt constantNonnegative,radiusSquare]
  exact bound

variable {dimension : ℕ}

def originalFlatValueVector (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (point : ClosedDisk) :
    lp (fun _ : ℤ => ComplexEuclidean dimension) 2 :=
  weightedCellVector (fun cell => completedWeightedCell parameters (by omega) cell field point)
    (originalFlat_value_memlp parameters field flat point)

def originalFlatRotationVector (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (point : ClosedDisk) :
    lp (fun _ : ℤ => ComplexEuclidean dimension) 2 :=
  weightedCellVector (fun cell => cartesianWeight parameters cell point.val • originalRotationAt parameters cell point field)
    (originalFlat_rotation_memlp parameters field flat point)

def flatDecayConstant : ℝ :=
  (Real.sqrt (9 * Real.pi^3 * spatialDecayConstant) + Real.sqrt (4 * Real.pi^3 * spatialDecayConstant)) * sameGradeConstant 4

theorem flatDecayConstant_nonnegative : 0 ≤ flatDecayConstant :=
  mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (sameGradeConstant_nonnegative 4)

theorem originalFlatValueVector_norm (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (point : ClosedDisk) :
    ‖originalFlatValueVector parameters field flat point‖ ≤
      Real.sqrt (9 * Real.pi^3 * spatialDecayConstant) * ‖point.val‖^(3/2:ℝ) * ‖completedExtension parameters field‖ := by
  apply weightedCellVector_bound _ _ _ _ _ (by positivity [spatialDecayConstant_nonnegative]) (norm_nonneg _) (norm_nonneg _)
  intro cells
  have bound := originalFlat_value_finiteEnergy parameters field flat point cells
  nlinarith only [bound]

theorem originalFlatRotationVector_norm (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (point : ClosedDisk) :
    ‖originalFlatRotationVector parameters field flat point‖ ≤
      Real.sqrt (4 * Real.pi^3 * spatialDecayConstant) * ‖point.val‖^(3/2:ℝ) * ‖completedExtension parameters field‖ := by
  apply weightedCellVector_bound _ _ _ _ _ (by positivity [spatialDecayConstant_nonnegative]) (norm_nonneg _) (norm_nonneg _)
  intro cells
  have bound := originalFlat_rotation_finiteEnergy parameters field flat point cells
  nlinarith only [bound]

/-- Exact original-width A4 flat Taylor decay, including every axial cell.
The second vector is the literal W R U with R=y₁∂₂−y₂∂₁. No A5,
weighted exhaustion class, homogeneous PDE, or assumed Hölder field is used. -/
theorem originalA4_flat_decay (parameters : PhaseParameters) (field : AGrade parameters dimension 4)
    (flat : OriginalFirstJetFlat parameters field) (point : ClosedDisk) :
    ‖originalFlatValueVector parameters field flat point‖ + ‖originalFlatRotationVector parameters field flat point‖ ≤
      flatDecayConstant * ‖point.val‖^(3/2:ℝ) * ‖field‖ := by
  have first := originalFlatValueVector_norm parameters field flat point
  have second := originalFlatRotationVector_norm parameters field flat point
  have extension : ‖completedExtension parameters field‖ ≤ sameGradeConstant 4 * ‖field‖ :=
    (completedExtension parameters).le_of_opNorm_le (completedExtension_norm_le parameters) field
  calc
    _ ≤ (Real.sqrt (9 * Real.pi^3 * spatialDecayConstant) + Real.sqrt (4 * Real.pi^3 * spatialDecayConstant)) *
        ‖point.val‖^(3/2:ℝ) * ‖completedExtension parameters field‖ := by nlinarith only [first,second]
    _ ≤ (Real.sqrt (9 * Real.pi^3 * spatialDecayConstant) + Real.sqrt (4 * Real.pi^3 * spatialDecayConstant)) *
        ‖point.val‖^(3/2:ℝ) * (sameGradeConstant 4 * ‖field‖) :=
      mul_le_mul_of_nonneg_left extension (by positivity)
    _ = _ := by unfold flatDecayConstant; ring

end Grad.OriginalFlatAxisDecay
