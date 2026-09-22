import FT1Torus
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

universe valueUniverse

namespace Grad.FourierGrade

open Grad.ClosedJets

/-- The P15 mixed derivative index `(α₁,α₂,b)`, counted without word permutations. -/
abbrev FourierMultiIndex := DiskCellMultiIndex

/-- Four slots encode `(α₁,α₂,b,slack)`, with total exactly `grade`.  The slack
coordinate turns the paper's `≤ grade` condition into the standard stars-and-bars set. -/
def augmentedFourierIndices (grade : ℕ) : Finset (Fin 4 →₀ ℕ) :=
  Finset.univ.finsuppAntidiag grade

/-- Drop the uniquely determined slack coordinate. -/
def augmentedToFourier (index : Fin 4 →₀ ℕ) : FourierMultiIndex :=
  ((index 0, index 1), index 2)

/-- Add the unique slack coordinate to a mixed multi-index of order at most `grade`. -/
def augmentedIndex (grade : ℕ) (index : FourierMultiIndex) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![index.1.1, index.1.2, index.2, grade - diskCellOrder index]

@[simp] theorem augmentedToFourier_augmentedIndex (grade : ℕ) (index : FourierMultiIndex) :
    augmentedToFourier (augmentedIndex grade index) = index := by
  rcases index with ⟨⟨first, second⟩, cell⟩
  simp [augmentedToFourier, augmentedIndex]

/-- All mixed multi-indices of total order at most `grade`, each appearing exactly once. -/
def fourierMultiIndices (grade : ℕ) : Finset FourierMultiIndex :=
  (augmentedFourierIndices grade).image augmentedToFourier

theorem augmentedToFourier_injOn (grade : ℕ) :
    Set.InjOn augmentedToFourier (augmentedFourierIndices grade) := by
  intro first firstMembership second secondMembership equality
  have firstSum : ∑ coordinate : Fin 4, first coordinate = grade :=
    (Finset.mem_finsuppAntidiag.mp firstMembership).1
  have secondSum : ∑ coordinate : Fin 4, second coordinate = grade :=
    (Finset.mem_finsuppAntidiag.mp secondMembership).1
  have coordinateZero : first 0 = second 0 := by
    simpa [augmentedToFourier] using congrArg (fun index => index.1.1) equality
  have coordinateOne : first 1 = second 1 := by
    simpa [augmentedToFourier] using congrArg (fun index => index.1.2) equality
  have coordinateTwo : first 2 = second 2 := by
    simpa [augmentedToFourier] using congrArg (fun index => index.2) equality
  have expandedFirst : first 0 + (first 1 + (first 2 + first 3)) = grade := by
    simpa [Fin.sum_univ_succ] using firstSum
  have expandedSecond : second 0 + (second 1 + (second 2 + second 3)) = grade := by
    simpa [Fin.sum_univ_succ] using secondSum
  have coordinateThree : first 3 = second 3 := by
    omega
  apply Finsupp.ext
  intro coordinate
  fin_cases coordinate
  · exact coordinateZero
  · exact coordinateOne
  · exact coordinateTwo
  · simpa using coordinateThree

theorem mem_fourierMultiIndices {grade : ℕ} {index : FourierMultiIndex} :
  index ∈ fourierMultiIndices grade ↔
      index.1.1 ≤ grade ∧ index.1.2 ≤ grade ∧ index.2 ≤ grade ∧
        diskCellOrder index ≤ grade := by
  constructor
  · intro membership
    obtain ⟨augmented, augmentedMembership, rfl⟩ := Finset.mem_image.mp membership
    have total : ∑ coordinate : Fin 4, augmented coordinate = grade :=
      (Finset.mem_finsuppAntidiag.mp augmentedMembership).1
    have expanded : augmented 0 + (augmented 1 + (augmented 2 + augmented 3)) = grade := by
      simpa [Fin.sum_univ_succ] using total
    simp only [augmentedToFourier, diskCellOrder]
    omega
  · rintro ⟨firstBound, secondBound, cellBound, orderBound⟩
    apply Finset.mem_image.mpr
    refine ⟨augmentedIndex grade index, ?_, augmentedToFourier_augmentedIndex grade index⟩
    unfold augmentedFourierIndices
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    have completion : index.1.1 +
        (index.1.2 + (index.2 + (grade - diskCellOrder index))) = grade := by
      simp only [diskCellOrder] at orderBound ⊢
      omega
    simpa [augmentedIndex, Fin.sum_univ_succ] using completion

theorem zero_mem_fourierMultiIndices (grade : ℕ) :
    ((0, 0), 0) ∈ fourierMultiIndices grade := by
  rw [mem_fourierMultiIndices]
  simp [diskCellOrder]

theorem firstPure_mem_fourierMultiIndices (grade : ℕ) :
    ((grade, 0), 0) ∈ fourierMultiIndices grade := by
  rw [mem_fourierMultiIndices]
  simp [diskCellOrder]

theorem secondPure_mem_fourierMultiIndices (grade : ℕ) :
    ((0, grade), 0) ∈ fourierMultiIndices grade := by
  rw [mem_fourierMultiIndices]
  simp [diskCellOrder]

theorem cellPure_mem_fourierMultiIndices (grade : ℕ) :
    ((0, 0), grade) ∈ fourierMultiIndices grade := by
  rw [mem_fourierMultiIndices]
  simp [diskCellOrder]

/-- Squared modulus of the Fourier multiplier for one mixed derivative. -/
def derivativeMultiplier (index : FourierMultiIndex) (mode : FourierMode) : ℝ :=
  |frequencyVector mode 0| ^ (2 * index.1.1) *
    |frequencyVector mode 1| ^ (2 * index.1.2) *
      |frequencyVector mode 2| ^ (2 * index.2)

theorem derivativeMultiplier_nonneg (index : FourierMultiIndex) (mode : FourierMode) :
    0 ≤ derivativeMultiplier index mode := by
  unfold derivativeMultiplier
  positivity

@[simp] theorem derivativeMultiplier_zero (mode : FourierMode) :
    derivativeMultiplier ((0, 0), 0) mode = 1 := by
  simp [derivativeMultiplier]

@[simp] theorem derivativeMultiplier_firstPure (grade : ℕ) (mode : FourierMode) :
    derivativeMultiplier ((grade, 0), 0) mode =
      |frequencyVector mode 0| ^ (2 * grade) := by
  simp [derivativeMultiplier]

@[simp] theorem derivativeMultiplier_secondPure (grade : ℕ) (mode : FourierMode) :
    derivativeMultiplier ((0, grade), 0) mode =
      |frequencyVector mode 1| ^ (2 * grade) := by
  simp [derivativeMultiplier]

@[simp] theorem derivativeMultiplier_cellPure (grade : ℕ) (mode : FourierMode) :
    derivativeMultiplier ((0, 0), grade) mode =
      |frequencyVector mode 2| ^ (2 * grade) := by
  simp [derivativeMultiplier]

/-- The squared magnitude of one physical frequency coordinate. -/
def coordinateSquare (mode : FourierMode) (coordinate : Fin 3) : ℝ :=
  |frequencyVector mode coordinate| ^ 2

/-- A single square dominating the inhomogeneous constant and all three frequency squares. -/
def dominantSquare (mode : FourierMode) : ℝ :=
  max 1 (max (coordinateSquare mode 0)
    (max (coordinateSquare mode 1) (coordinateSquare mode 2)))

/-- Pointwise multiplier of the exact derivative Sobolev square-sum. -/
def derivativeWeight (grade : ℕ) (mode : FourierMode) : ℝ :=
  ∑ index ∈ fourierMultiIndices grade, derivativeMultiplier index mode

/-- P15's exact number of unordered three-dimensional multi-indices through `grade`. -/
def derivativeCount (grade : ℕ) : ℕ := (fourierMultiIndices grade).card

/-- The literal combinatorial constant `d_q = binom(q+3,3)` in P15. -/
theorem derivativeCount_eq_choose (grade : ℕ) :
    derivativeCount grade = Nat.choose (grade + 3) 3 := by
  calc
    derivativeCount grade = (augmentedFourierIndices grade).card := by
      rw [derivativeCount, fourierMultiIndices]
      exact Finset.card_image_iff.mpr (augmentedToFourier_injOn grade)
    _ = Nat.choose (4 + grade - 1) grade := by
      exact Finset.card_finsuppAntidiag_nat_eq_choose grade
    _ = Nat.choose (grade + 3) grade := by
      congr 2
      omega
    _ = Nat.choose (grade + 3) ((grade + 3) - grade) := by
      exact (Nat.choose_symm (by omega)).symm
    _ = Nat.choose (grade + 3) 3 := by
      congr 2
      omega

theorem derivativeWeight_nonneg (grade : ℕ) (mode : FourierMode) :
    0 ≤ derivativeWeight grade mode := by
  exact Finset.sum_nonneg fun index _ => derivativeMultiplier_nonneg index mode

theorem frequencyWeight_sq_expanded (mode : FourierMode) :
    frequencyWeight mode ^ 2 = 1 +
      (coordinateSquare mode 0 +
        (coordinateSquare mode 1 + coordinateSquare mode 2)) := by
  rw [frequencyWeight_sq]
  have normExpansion :=
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (frequencyVector mode)
  rw [normExpansion]
  simp [coordinateSquare, Fin.sum_univ_succ, Real.norm_eq_abs, mul_pow, sq_abs]

theorem frequencyWeight_sq_le_four_dominant (mode : FourierMode) :
    frequencyWeight mode ^ 2 ≤ 4 * dominantSquare mode := by
  have oneBound : (1 : ℝ) ≤ dominantSquare mode :=
    le_max_left _ _
  have firstBound : coordinateSquare mode 0 ≤ dominantSquare mode :=
    (le_max_left _ _).trans (le_max_right _ _)
  have secondBound : coordinateSquare mode 1 ≤ dominantSquare mode :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have cellBound : coordinateSquare mode 2 ≤ dominantSquare mode :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  rw [frequencyWeight_sq_expanded]
  linarith

theorem one_le_derivativeWeight (grade : ℕ) (mode : FourierMode) :
    1 ≤ derivativeWeight grade mode := by
  calc
    1 = derivativeMultiplier ((0, 0), 0) mode := by simp
    _ ≤ ∑ index ∈ fourierMultiIndices grade, derivativeMultiplier index mode :=
      Finset.single_le_sum
        (fun index _ => derivativeMultiplier_nonneg index mode)
        (zero_mem_fourierMultiIndices grade)
    _ = derivativeWeight grade mode := rfl

theorem firstSquare_pow_le_derivativeWeight (grade : ℕ) (mode : FourierMode) :
    coordinateSquare mode 0 ^ grade ≤ derivativeWeight grade mode := by
  calc
    coordinateSquare mode 0 ^ grade =
        derivativeMultiplier ((grade, 0), 0) mode := by
      rw [coordinateSquare, ← pow_mul]
      simp
    _ ≤ ∑ index ∈ fourierMultiIndices grade, derivativeMultiplier index mode :=
      Finset.single_le_sum
        (fun index _ => derivativeMultiplier_nonneg index mode)
        (firstPure_mem_fourierMultiIndices grade)
    _ = derivativeWeight grade mode := rfl

theorem secondSquare_pow_le_derivativeWeight (grade : ℕ) (mode : FourierMode) :
    coordinateSquare mode 1 ^ grade ≤ derivativeWeight grade mode := by
  calc
    coordinateSquare mode 1 ^ grade =
        derivativeMultiplier ((0, grade), 0) mode := by
      rw [coordinateSquare, ← pow_mul]
      simp
    _ ≤ ∑ index ∈ fourierMultiIndices grade, derivativeMultiplier index mode :=
      Finset.single_le_sum
        (fun index _ => derivativeMultiplier_nonneg index mode)
        (secondPure_mem_fourierMultiIndices grade)
    _ = derivativeWeight grade mode := rfl

theorem cellSquare_pow_le_derivativeWeight (grade : ℕ) (mode : FourierMode) :
    coordinateSquare mode 2 ^ grade ≤ derivativeWeight grade mode := by
  calc
    coordinateSquare mode 2 ^ grade =
        derivativeMultiplier ((0, 0), grade) mode := by
      rw [coordinateSquare, ← pow_mul]
      simp
    _ ≤ ∑ index ∈ fourierMultiIndices grade, derivativeMultiplier index mode :=
      Finset.single_le_sum
        (fun index _ => derivativeMultiplier_nonneg index mode)
        (cellPure_mem_fourierMultiIndices grade)
    _ = derivativeWeight grade mode := rfl

theorem dominantSquare_pow_le_derivativeWeight (grade : ℕ) (mode : FourierMode) :
    dominantSquare mode ^ grade ≤ derivativeWeight grade mode := by
  unfold dominantSquare
  rcases le_total (1 : ℝ)
      (max (coordinateSquare mode 0)
        (max (coordinateSquare mode 1) (coordinateSquare mode 2))) with outer | outer
  · rw [max_eq_right outer]
    rcases le_total (coordinateSquare mode 0)
        (max (coordinateSquare mode 1) (coordinateSquare mode 2)) with first | first
    · rw [max_eq_right first]
      rcases le_total (coordinateSquare mode 1) (coordinateSquare mode 2) with second | second
      · rw [max_eq_right second]
        exact cellSquare_pow_le_derivativeWeight grade mode
      · rw [max_eq_left second]
        exact secondSquare_pow_le_derivativeWeight grade mode
    · rw [max_eq_left first]
      exact firstSquare_pow_le_derivativeWeight grade mode
  · rw [max_eq_left outer]
    simpa using one_le_derivativeWeight grade mode

/-- The reverse P15 pointwise comparison, with the paper's dimension-only factor `4^q`. -/
theorem gradeWeight_le_four_pow_mul_derivativeWeight (grade : ℕ) (mode : FourierMode) :
    frequencyWeight mode ^ (2 * grade) ≤
      (4 : ℝ) ^ grade * derivativeWeight grade mode := by
  have powered := pow_le_pow_left₀ (sq_nonneg (frequencyWeight mode))
    (frequencyWeight_sq_le_four_dominant mode) grade
  calc
    frequencyWeight mode ^ (2 * grade) = (frequencyWeight mode ^ 2) ^ grade := by
      rw [pow_mul]
    _ ≤ (4 * dominantSquare mode) ^ grade := powered
    _ = (4 : ℝ) ^ grade * dominantSquare mode ^ grade := by
      rw [mul_pow]
    _ ≤ (4 : ℝ) ^ grade * derivativeWeight grade mode :=
      mul_le_mul_of_nonneg_left (dominantSquare_pow_le_derivativeWeight grade mode) (by positivity)

theorem frequencyVector_abs_le_weight (mode : FourierMode) (coordinate : Fin 3) :
    |frequencyVector mode coordinate| ≤ frequencyWeight mode := by
  have coordinateLeNorm : |frequencyVector mode coordinate| ≤ ‖frequencyVector mode‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (frequencyVector mode) coordinate
  have normLeWeight : ‖frequencyVector mode‖ ≤ frequencyWeight mode := by
    rw [frequencyWeight]
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by
      nlinarith [sq_nonneg ‖frequencyVector mode‖])
  exact coordinateLeNorm.trans normLeWeight

theorem derivativeMultiplier_le_gradeWeight {grade : ℕ} {index : FourierMultiIndex}
    (membership : index ∈ fourierMultiIndices grade) (mode : FourierMode) :
    derivativeMultiplier index mode ≤ frequencyWeight mode ^ (2 * grade) := by
  have orderBound : diskCellOrder index ≤ grade := (mem_fourierMultiIndices.mp membership).2.2.2
  unfold derivativeMultiplier
  have weightNonneg : 0 ≤ frequencyWeight mode :=
    zero_le_one.trans (frequencyWeight_one_le mode)
  have firstPower : |frequencyVector mode 0| ^ (2 * index.1.1) ≤
      frequencyWeight mode ^ (2 * index.1.1) :=
    pow_le_pow_left₀ (abs_nonneg _) (frequencyVector_abs_le_weight mode 0) _
  have secondPower : |frequencyVector mode 1| ^ (2 * index.1.2) ≤
      frequencyWeight mode ^ (2 * index.1.2) :=
    pow_le_pow_left₀ (abs_nonneg _) (frequencyVector_abs_le_weight mode 1) _
  have cellPower : |frequencyVector mode 2| ^ (2 * index.2) ≤
      frequencyWeight mode ^ (2 * index.2) :=
    pow_le_pow_left₀ (abs_nonneg _) (frequencyVector_abs_le_weight mode 2) _
  calc
    |frequencyVector mode 0| ^ (2 * index.1.1) *
          |frequencyVector mode 1| ^ (2 * index.1.2) *
            |frequencyVector mode 2| ^ (2 * index.2) ≤
        frequencyWeight mode ^ (2 * index.1.1) *
          (frequencyWeight mode ^ (2 * index.1.2) *
            frequencyWeight mode ^ (2 * index.2)) := by
      rw [mul_assoc]
      exact mul_le_mul firstPower
        (mul_le_mul secondPower cellPower (by positivity) (pow_nonneg weightNonneg _))
        (by positivity) (pow_nonneg weightNonneg _)
    _ = frequencyWeight mode ^ (2 * diskCellOrder index) := by
      rw [← pow_add, ← pow_add]
      congr 1
      simp [diskCellOrder]
      omega
    _ ≤ frequencyWeight mode ^ (2 * grade) :=
      pow_le_pow_right₀ (frequencyWeight_one_le mode) (Nat.mul_le_mul_left 2 orderBound)

theorem derivativeWeight_upper (grade : ℕ) (mode : FourierMode) :
    derivativeWeight grade mode ≤
      (derivativeCount grade : ℝ) * frequencyWeight mode ^ (2 * grade) := by
  calc
    derivativeWeight grade mode =
        ∑ index ∈ fourierMultiIndices grade, derivativeMultiplier index mode := rfl
    _ ≤ ∑ _index ∈ fourierMultiIndices grade,
        frequencyWeight mode ^ (2 * grade) := by
      apply Finset.sum_le_sum
      intro index membership
      exact derivativeMultiplier_le_gradeWeight membership mode
    _ = (derivativeCount grade : ℝ) * frequencyWeight mode ^ (2 * grade) := by
      simp [derivativeCount]

/-- Coefficient realization of the exact sum of squared derivative `L²` norms. -/
def derivativeSequenceEnergy {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (grade : ℕ) (values : FourierMode → Value) : ℝ :=
  ∑' mode : FourierMode, derivativeWeight grade mode * ‖values mode‖ ^ 2

/-- The literal P14 weighted coefficient square-sum. -/
def gradeSequenceEnergy {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (grade : ℕ) (values : FourierMode → Value) : ℝ :=
  ∑' mode : FourierMode, frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2

theorem derivativeSequenceTerm_nonneg {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (grade : ℕ) (values : FourierMode → Value) (mode : FourierMode) :
    0 ≤ derivativeWeight grade mode * ‖values mode‖ ^ 2 :=
  mul_nonneg (derivativeWeight_nonneg grade mode) (sq_nonneg _)

theorem gradeSequenceTerm_nonneg {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (grade : ℕ) (values : FourierMode → Value) (mode : FourierMode) :
    0 ≤ frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2 :=
  mul_nonneg (pow_nonneg (frequencyWeight_pos mode).le _) (sq_nonneg _)

theorem derivativeSequence_summable_of_grade {Value : Type valueUniverse}
    [NormedAddCommGroup Value] (grade : ℕ) (values : FourierMode → Value)
    (gradeSummable : Summable (fun mode : FourierMode =>
      frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2)) :
    Summable (fun mode : FourierMode =>
      derivativeWeight grade mode * ‖values mode‖ ^ 2) := by
  have scaledGrade := gradeSummable.mul_left (derivativeCount grade : ℝ)
  apply Summable.of_nonneg_of_le
    (fun mode => derivativeSequenceTerm_nonneg grade values mode) _ scaledGrade
  intro mode
  calc
    derivativeWeight grade mode * ‖values mode‖ ^ 2 ≤
        ((derivativeCount grade : ℝ) * frequencyWeight mode ^ (2 * grade)) *
          ‖values mode‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (derivativeWeight_upper grade mode) (sq_nonneg _)
    _ = (derivativeCount grade : ℝ) *
        (frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2) := by ring

/-- The upper half of P15 after summing the exact pointwise multiplier comparison. -/
theorem derivativeSequenceEnergy_le_choose_mul_gradeSequenceEnergy
    {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (grade : ℕ) (values : FourierMode → Value)
    (gradeSummable : Summable (fun mode : FourierMode =>
      frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2)) :
    derivativeSequenceEnergy grade values ≤
      (Nat.choose (grade + 3) 3 : ℝ) * gradeSequenceEnergy grade values := by
  have derivativeSummable :=
    derivativeSequence_summable_of_grade grade values gradeSummable
  have scaledGrade := gradeSummable.mul_left (derivativeCount grade : ℝ)
  have comparison := derivativeSummable.tsum_le_tsum (fun mode => by
    calc
      derivativeWeight grade mode * ‖values mode‖ ^ 2 ≤
          ((derivativeCount grade : ℝ) * frequencyWeight mode ^ (2 * grade)) *
            ‖values mode‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (derivativeWeight_upper grade mode) (sq_nonneg _)
      _ = (derivativeCount grade : ℝ) *
          (frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2) := by ring)
    scaledGrade
  calc
    derivativeSequenceEnergy grade values ≤
        ∑' mode : FourierMode, (derivativeCount grade : ℝ) *
          (frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2) := comparison
    _ = (derivativeCount grade : ℝ) * gradeSequenceEnergy grade values := by
      exact (gradeSummable.hasSum.mul_left (derivativeCount grade : ℝ)).tsum_eq
    _ = (Nat.choose (grade + 3) 3 : ℝ) * gradeSequenceEnergy grade values := by
      rw [derivativeCount_eq_choose]

/-- The lower half of P15 before dividing by `4^q`. -/
theorem gradeSequenceEnergy_le_four_pow_mul_derivativeSequenceEnergy
    {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (grade : ℕ) (values : FourierMode → Value)
    (gradeSummable : Summable (fun mode : FourierMode =>
      frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2)) :
    gradeSequenceEnergy grade values ≤
      (4 : ℝ) ^ grade * derivativeSequenceEnergy grade values := by
  have derivativeSummable :=
    derivativeSequence_summable_of_grade grade values gradeSummable
  have scaledDerivative := derivativeSummable.mul_left ((4 : ℝ) ^ grade)
  have comparison := gradeSummable.tsum_le_tsum (fun mode => by
    calc
      frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2 ≤
          ((4 : ℝ) ^ grade * derivativeWeight grade mode) * ‖values mode‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (gradeWeight_le_four_pow_mul_derivativeWeight grade mode) (sq_nonneg _)
      _ = (4 : ℝ) ^ grade *
          (derivativeWeight grade mode * ‖values mode‖ ^ 2) := by ring)
    scaledDerivative
  calc
    gradeSequenceEnergy grade values ≤
        ∑' mode : FourierMode, (4 : ℝ) ^ grade *
          (derivativeWeight grade mode * ‖values mode‖ ^ 2) := comparison
    _ = (4 : ℝ) ^ grade * derivativeSequenceEnergy grade values := by
      exact (derivativeSummable.hasSum.mul_left ((4 : ℝ) ^ grade)).tsum_eq

/-- The literal inverse-factor form of the lower P15 comparison. -/
theorem inverse_four_pow_mul_gradeSequenceEnergy_le_derivativeSequenceEnergy
    {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (grade : ℕ) (values : FourierMode → Value)
    (gradeSummable : Summable (fun mode : FourierMode =>
      frequencyWeight mode ^ (2 * grade) * ‖values mode‖ ^ 2)) :
    ((4 : ℝ) ^ grade)⁻¹ * gradeSequenceEnergy grade values ≤
      derivativeSequenceEnergy grade values := by
  apply (inv_mul_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 4) grade)).mpr
  exact gradeSequenceEnergy_le_four_pow_mul_derivativeSequenceEnergy
    grade values gradeSummable

theorem gradeCoefficientEnergy_summable {Value : Type valueUniverse}
    [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (grade : ℕ) (field : JGrade Value grade) :
    Summable (fun mode : FourierMode =>
      frequencyWeight mode ^ (2 * grade) * ‖coefficient grade field mode‖ ^ 2) := by
  have weightedSummable := field.2.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  norm_num at weightedSummable
  apply weightedSummable.congr
  intro mode
  rw [← weighted_coefficient grade field mode, norm_smul, Complex.norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (frequencyWeight_pos mode)]
  ring

/-- The coefficient realization of the exact derivative square-sum for a P14 grade. -/
def derivativeCoefficientEnergy {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) (field : JGrade Value grade) : ℝ :=
  derivativeSequenceEnergy grade (coefficient grade field)

/-- P15 at the weighted-coordinate level, with both literal constants. -/
theorem derivativeCoefficientEnergy_comparison {Value : Type valueUniverse}
    [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (grade : ℕ) (field : JGrade Value grade) :
    ((4 : ℝ) ^ grade)⁻¹ * ‖field‖ ^ 2 ≤ derivativeCoefficientEnergy grade field ∧
      derivativeCoefficientEnergy grade field ≤
        (Nat.choose (grade + 3) 3 : ℝ) * ‖field‖ ^ 2 := by
  have summable := gradeCoefficientEnergy_summable grade field
  have gradeEnergy : gradeSequenceEnergy grade (coefficient grade field) = ‖field‖ ^ 2 := by
    exact (norm_sq_eq_weighted_tsum grade field).symm
  constructor
  · have lower := inverse_four_pow_mul_gradeSequenceEnergy_le_derivativeSequenceEnergy
      grade (coefficient grade field) summable
    rw [gradeEnergy] at lower
    exact lower
  · have upper := derivativeSequenceEnergy_le_choose_mul_gradeSequenceEnergy
      grade (coefficient grade field) summable
    rw [gradeEnergy] at upper
    exact upper

end Grad.FourierGrade
