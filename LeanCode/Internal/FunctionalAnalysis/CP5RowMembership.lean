import CP4PhysicalRow

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Gauges Grad.BoundaryTrace Grad.BoundaryLift

/-- Two-index specialization of the accepted square-summability bridge. -/
theorem memlp_pair_iff_summable_sq {Value : Type*} [NormedAddCommGroup Value]
    (coordinates : ℤ × ℤ → Value) :
    Memℓp coordinates 2 ↔
      Summable (fun mode : ℤ × ℤ => ‖coordinates mode‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using
    (memℓp_gen_iff (p := 2) (f := coordinates) (by norm_num))

/-- Every Euclidean component is dominated by the vector norm. -/
theorem component_norm_le {dimension : ℕ} (vector : ComplexEuclidean dimension)
    (index : Fin dimension) : ‖vector index‖ ≤ ‖vector‖ := by
  have squares : ‖vector index‖ ^ 2 ≤ ∑ other, ‖vector other‖ ^ 2 :=
    Finset.single_le_sum (f := fun other => ‖vector other‖ ^ 2)
      (fun other _ => sq_nonneg _) (Finset.mem_univ index)
  have normSq : ‖vector‖ = Real.sqrt (∑ other, ‖vector other‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
  rw [normSq]
  rw [show ‖vector index‖ = Real.sqrt (‖vector index‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt squares

/-- The scalar insertion into the one-dimensional carrier is isometric. -/
theorem single_norm_eq (value : ℂ) :
    ‖EuclideanSpace.single (0 : Fin 1) value‖ = ‖value‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one]
  rw [show (EuclideanSpace.single (0 : Fin 1) value) 0 = value by
    simp]
  exact Real.sqrt_sq (norm_nonneg _)

/-- The weighted coefficient family of a smooth core field is
square-summable at every positive grade: the accepted core trace element
realizes it inside the boundary Hilbert carrier. -/
theorem coreFamily_weighted_memlp {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (grade : ℕ) (gradePositive : 1 ≤ grade) :
    Memℓp (fun mode : ℤ × ℤ => (boundaryWeight parameters grade mode : ℂ) •
      originalBoundaryCoefficient parameters field mode) 2 := by
  have identify : (fun mode : ℤ × ℤ =>
      (boundaryWeight parameters grade mode : ℂ) •
        originalBoundaryCoefficient parameters field mode) =
      fun mode => (coreTraceLinear parameters grade gradePositive
        (GradeCore.ofCoreLinear (grade := grade) field)) mode := by
    funext mode
    have coefficientLaw := coreTraceLinear_coefficient parameters grade
      gradePositive (GradeCore.ofCoreLinear (grade := grade) field) mode
    have roundTrip : (GradeCore.ofCoreLinear (grade := grade) field).toCore = field := rfl
    rw [roundTrip] at coefficientLaw
    have unfoldCoefficient : boundaryCoefficient parameters grade
        (coreTraceLinear parameters grade gradePositive
          (GradeCore.ofCoreLinear (grade := grade) field)) mode =
        ((boundaryWeight parameters grade mode : ℂ))⁻¹ •
          (coreTraceLinear parameters grade gradePositive
            (GradeCore.ofCoreLinear (grade := grade) field)) mode := rfl
    rw [unfoldCoefficient] at coefficientLaw
    have weightNonzero : ((boundaryWeight parameters grade mode : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (boundaryWeight_pos parameters grade mode).ne'
    calc (boundaryWeight parameters grade mode : ℂ) •
          originalBoundaryCoefficient parameters field mode
        = (boundaryWeight parameters grade mode : ℂ) •
            (((boundaryWeight parameters grade mode : ℂ))⁻¹ •
              (coreTraceLinear parameters grade gradePositive
                (GradeCore.ofCoreLinear (grade := grade) field)) mode) := by
          rw [coefficientLaw]
      _ = _ := smul_inv_smul₀ weightNonzero _
  rw [identify]
  exact lp.memℓp _

end Grad.Cor18
