import AAZ3ActualPhysicalWeakFamilies
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRadialJets
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularPhysicalWeak_real (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (scalar : ℝ) (value derivative : AnnularRawFamily lower)
    (weak : AnnularPhysicalWeakDerivative parameters lower positive value derivative) :
    AnnularPhysicalWeakDerivative parameters lower positive (scalar • value) (scalar • derivative) := by
  intro mode test smooth compact supported vector
  change collarPairing lower _ vector (annularDecodeMode parameters lower positive mode (scalar • derivative mode)) =
    -collarPairing lower _ vector (annularDecodeMode parameters lower positive mode (scalar • value mode))
  rw [(annularDecodeMode parameters lower positive mode).map_smul_of_tower scalar (derivative mode),
    (annularDecodeMode parameters lower positive mode).map_smul_of_tower scalar (value mode),
    map_smul, map_smul, weak mode test smooth compact supported vector, smul_neg]

theorem annularPhysicalWeak_nsmul (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (scalar : ℕ) (value derivative : AnnularRawFamily lower)
    (weak : AnnularPhysicalWeakDerivative parameters lower positive value derivative) :
    AnnularPhysicalWeakDerivative parameters lower positive (scalar • value) (scalar • derivative) := by
  induction scalar with
  | zero => simpa only [zero_nsmul] using annularPhysicalWeak_zero parameters lower positive
  | succ scalar previous =>
    simpa only [succ_nsmul] using annularPhysicalWeak_add parameters lower positive _ _ _ _ previous weak

theorem annularPhysicalWeak_sum (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    {Index : Type*} (support : Finset Index) (value derivative : Index → AnnularRawFamily lower)
    (weak : ∀ index ∈ support, AnnularPhysicalWeakDerivative parameters lower positive (value index) (derivative index)) :
    AnnularPhysicalWeakDerivative parameters lower positive (∑ index ∈ support, value index) (∑ index ∈ support, derivative index) := by
  classical
  induction support using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using annularPhysicalWeak_zero parameters lower positive
  | @insert index support missing previous =>
    rw [Finset.sum_insert missing, Finset.sum_insert missing]
    exact annularPhysicalWeak_add parameters lower positive _ _ _ _
      (weak index (Finset.mem_insert_self index support))
      (previous (fun other member => weak other (Finset.mem_insert_of_mem member)))

/-- Explicit derivative coefficient of r^-base. This recursion records
all factorial factors without introducing a parameter-dependent constant. -/
def annularReciprocalCoefficient (base : ℕ) : ℕ → ℝ :=
  Nat.rec 1 (fun order previous => -((base + order : ℕ) : ℝ) * previous)

theorem annularReciprocalCoefficient_zero (base : ℕ) :
    annularReciprocalCoefficient base 0 = 1 := rfl

theorem annularReciprocalCoefficient_succ (base order : ℕ) :
    annularReciprocalCoefficient base (order + 1) =
      -((base + order : ℕ) : ℝ) * annularReciprocalCoefficient base order := rfl

def annularReciprocalJet (lower : ℝ) (positive : 0 < lower) (base order : ℕ)
    (field : AnnularRawFamily lower) : AnnularRawFamily lower :=
  annularReciprocalCoefficient base order • annularRawRadiusPower lower positive (base + order) field

/-- Coefficient differentiation and physical weak differentiation obey the
actual product rule, with the exact next reciprocal coefficient. -/
theorem annularReciprocalJet_weak (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (base order : ℕ) (value derivative : AnnularRawFamily lower)
    (weak : AnnularPhysicalWeakDerivative parameters lower positive value derivative) :
    AnnularPhysicalWeakDerivative parameters lower positive (annularReciprocalJet lower positive base order value)
      (annularReciprocalJet lower positive base order derivative +
        annularReciprocalJet lower positive base (order + 1) value) := by
  have differentiated := annularPhysicalWeak_radiusPower parameters lower positive (base + order) value derivative weak
  have scaled := annularPhysicalWeak_real parameters lower positive (annularReciprocalCoefficient base order) _ _ differentiated
  have algebra : annularReciprocalCoefficient base order •
      (annularRawRadiusPower lower positive (base + order) derivative -
        ((base + order : ℕ) : ℝ) • annularRawRadiusPower lower positive (base + order + 1) value) =
      annularReciprocalJet lower positive base order derivative + annularReciprocalJet lower positive base (order + 1) value := by
    unfold annularReciprocalJet
    rw [annularReciprocalCoefficient_succ, ← Nat.add_assoc]
    module
  exact (congrArg (AnnularPhysicalWeakDerivative parameters lower positive
    (annularReciprocalJet lower positive base order value)) algebra).mp scaled

def annularLeibniz (lower : ℝ) (positive : 0 < lower) (base order : ℕ)
    (jet : ℕ → AnnularRawFamily lower) : AnnularRawFamily lower :=
  ∑ index ∈ Finset.range (order + 1), order.choose index •
    annularReciprocalJet lower positive base index (jet (order - index))

/-- Distributional Leibniz formula for every reciprocal coefficient and
physical derivative order. Every derivative premise concerns an already
constructed lower jet. -/
theorem annularLeibniz_weak (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (base order : ℕ) (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ index ≤ order, AnnularPhysicalWeakDerivative parameters lower positive (jet index) (jet (index + 1))) :
    AnnularPhysicalWeakDerivative parameters lower positive (annularLeibniz lower positive base order jet)
      (annularLeibniz lower positive base (order + 1) jet) := by
  have terms := annularPhysicalWeak_sum parameters lower positive (Finset.range (order + 1))
    (fun index => order.choose index • annularReciprocalJet lower positive base index (jet (order - index)))
    (fun index => order.choose index • (annularReciprocalJet lower positive base index (jet (order - index + 1)) +
      annularReciprocalJet lower positive base (index + 1) (jet (order - index)))) (by
        intro index member
        exact annularPhysicalWeak_nsmul parameters lower positive (order.choose index) _ _
          (annularReciprocalJet_weak parameters lower positive base index _ _ (weak (order - index) (Nat.sub_le _ _))))
  have algebra : (∑ index ∈ Finset.range (order + 1), order.choose index •
      (annularReciprocalJet lower positive base index (jet (order - index + 1)) +
        annularReciprocalJet lower positive base (index + 1) (jet (order - index)))) =
      annularLeibniz lower positive base (order + 1) jet := by
    unfold annularLeibniz
    have split := Finset.sum_choose_succ_nsmul
      (fun first second => annularReciprocalJet lower positive base first (jet second)) order
    apply Eq.trans ?_ split.symm
    simp only [smul_add, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro index member
    have bound : index ≤ order := Nat.le_of_lt_succ (Finset.mem_range.mp member)
    rw [Nat.sub_add_comm bound]
  exact (congrArg (AnnularPhysicalWeakDerivative parameters lower positive (annularLeibniz lower positive base order jet)) algebra).mp terms

end Grad.AnnularRadialJets
