import FC3Coordinates

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- One nonnegative cell summand in the literal original Cartesian M2 grade. -/
def m2CellEnergy {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ClosedJet dimension) (cell : ℤ) : ℝ :=
  ∑ index : GradeMultiIndex grade,
    cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
      ‖closedContinuousToDiskL2
        (closedMultiDerivative (phaseWeightedJet parameters cell (coefficients cell))
          index.toCartesian)‖ ^ 2

theorem rawCartesianGradeCoordinates_norm_sq {dimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ClosedJet dimension) (cell : ℤ) :
    ‖rawCartesianGradeCoordinates parameters grade coefficients cell‖ ^ 2 =
      m2CellEnergy parameters grade coefficients cell := by
  exact cellGradeRow_norm_sq parameters cell (coefficients cell)

theorem memlp_iff_summable_sq {Value : Type*} [NormedAddCommGroup Value]
    (coordinates : ℤ → Value) :
    Memℓp coordinates 2 ↔ Summable (fun cell : ℤ => ‖coordinates cell‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using
    (memℓp_gen_iff (p := 2) (f := coordinates) (by norm_num))

theorem rawCartesianGradeCoordinates_memlp_iff {dimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ClosedJet dimension) :
    Memℓp (rawCartesianGradeCoordinates parameters grade coefficients) 2 ↔
      Summable (m2CellEnergy parameters grade coefficients) := by
  rw [memlp_iff_summable_sq]
  apply summable_congr
  intro cell
  exact rawCartesianGradeCoordinates_norm_sq parameters grade coefficients cell

/-- The one all-grade original coefficient core: literal M2 is finite at every grade. -/
def originalCoreSubmodule (parameters : PhaseParameters) (dimension : ℕ) :
    Submodule ℂ (ℤ → ClosedJet dimension) where
  carrier coefficients := ∀ grade : ℕ,
    Memℓp (rawCartesianGradeCoordinates parameters grade coefficients) 2
  zero_mem' := by
    intro grade
    have zeroMember : Memℓp (0 : ℤ → CartesianGradeRow dimension grade) 2 := zero_memℓp
    convert zeroMember using 1
    funext cell
    exact (cellGradeRowLinear (dimension := dimension) (grade := grade) parameters cell).map_zero
  add_mem' := by
    intro first second firstMember secondMember grade
    rw [rawCartesianGradeCoordinates_add]
    exact (firstMember grade).add (secondMember grade)
  smul_mem' := by
    intro scalar coefficients member grade
    rw [rawCartesianGradeCoordinates_smul]
    exact (member grade).const_smul scalar

/-- `A^∞`: sequences of actual closed jets for which every literal M2 grade is finite. -/
abbrev ACore (parameters : PhaseParameters) (dimension : ℕ) :=
  originalCoreSubmodule parameters dimension

theorem mem_originalCore_iff {dimension : ℕ} (parameters : PhaseParameters)
    (coefficients : ℤ → ClosedJet dimension) :
    coefficients ∈ originalCoreSubmodule parameters dimension ↔
      ∀ grade : ℕ, Summable (m2CellEnergy parameters grade coefficients) := by
  constructor
  · intro member grade
    exact (rawCartesianGradeCoordinates_memlp_iff parameters grade coefficients).mp
      (member grade)
  · intro summable grade
    exact (rawCartesianGradeCoordinates_memlp_iff parameters grade coefficients).mpr
      (summable grade)

/-- The exact linear Hilbert-coordinate map defining grade `q` on the all-grade core. -/
def cartesianGradeCoordinates {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ) :
    ACore parameters dimension →ₗ[ℂ]
      lp (fun _ : ℤ => CartesianGradeRow dimension grade) 2 where
  toFun coefficients :=
    ⟨rawCartesianGradeCoordinates parameters grade coefficients.1,
      coefficients.property grade⟩
  map_add' first second := by
    apply Subtype.ext
    exact rawCartesianGradeCoordinates_add parameters grade first.1 second.1
  map_smul' scalar coefficients := by
    apply Subtype.ext
    exact rawCartesianGradeCoordinates_smul parameters grade scalar coefficients.1

theorem cartesianGradeCoordinates_apply {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (coefficients : ACore parameters dimension) (cell : ℤ)
    (index : GradeMultiIndex grade) :
    cartesianGradeCoordinates parameters grade coefficients cell index =
      (cellFrequency cell : ℂ) ^ (grade - cartesianOrder index.toCartesian) •
        closedContinuousToDiskL2
          (closedMultiDerivative
            (phaseWeightedJet parameters cell (coefficients.1 cell)) index.toCartesian) := rfl

theorem cartesianGradeCoordinates_norm_sq {dimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ACore parameters dimension) :
    ‖cartesianGradeCoordinates parameters grade coefficients‖ ^ 2 =
      ∑' cell : ℤ, m2CellEnergy parameters grade coefficients.1 cell := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (cartesianGradeCoordinates parameters grade coefficients)
  norm_num at normFormula
  rw [normFormula]
  exact tsum_congr (fun cell =>
    rawCartesianGradeCoordinates_norm_sq parameters grade coefficients.1 cell)

theorem cartesianGradeCoordinates_norm_sq_expanded {dimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ACore parameters dimension) :
    ‖cartesianGradeCoordinates parameters grade coefficients‖ ^ 2 =
      ∑' cell : ℤ, ∑ index : GradeMultiIndex grade,
        cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
          ∫ point : SpatialPlane,
            ‖closedDiskLift
              (closedMultiDerivative
                (phaseWeightedJet parameters cell (coefficients.1 cell))
                index.toCartesian) point‖ ^ 2
              ∂volume.restrict openUnitDisk := by
  rw [cartesianGradeCoordinates_norm_sq]
  apply tsum_congr
  intro cell
  unfold m2CellEnergy
  apply Finset.sum_congr rfl
  intro index _
  congr 1
  exact closedDerivativeL2_norm_sq
    (phaseWeightedJet parameters cell (coefficients.1 cell)) index.toCartesian

end Grad.CartesianState

