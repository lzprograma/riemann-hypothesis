module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

namespace UpperTheory.Reformulated.B.InvolutionInvariants

noncomputable def Jm : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
  fun {_} ε => Matrix.diagonal fun a => if ε a = Bool.true then 1 else -1

noncomputable def inUJ : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
  fun {_} ε g =>
    g.conjTranspose * Jm ε * g =
      Jm ε

theorem aux3 : ∀ {n : ℕ} (ε : Fin n → Bool)
  {g h : (Matrix (Fin n) (Fin n) ℂ)ˣ},
  g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} →
    h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} →
      g * h ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} := by
  intro n ε g h hg hh
  change inUJ ε _ at hg hh ⊢
  unfold inUJ at hg hh ⊢
  rw [Units.val_mul, Matrix.conjTranspose_mul]
  calc _ = (h.val).conjTranspose * ((g.val).conjTranspose * Jm ε * g.val) * h.val := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem aux4 : ∀ {n : ℕ} (ε : Fin n → Bool),
  (1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * 1 =
    Jm ε := by
  intro n ε
  simp

theorem aux5 : ∀ {n : ℕ} (ε : Fin n → Bool)
  {g : (Matrix (Fin n) (Fin n) ℂ)ˣ},
  g ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} →
    g⁻¹ ∈ {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val} := by
  intro n ε g hg
  change inUJ ε _ at hg ⊢
  unfold inUJ at hg ⊢
  have h1 : g.val * (g⁻¹).val = 1 := Units.mul_inv g
  calc _ = ((g⁻¹).val).conjTranspose * ((g.val).conjTranspose * Jm ε * g.val)
          * (g⁻¹).val := by rw [hg]
    _ = (g.val * (g⁻¹).val).conjTranspose * Jm ε * (g.val * (g⁻¹).val) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

noncomputable def UJ : {n : ℕ} →
  (Fin n → Bool) → Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  fun {n} ε =>
    { carrier := {g : (Matrix (Fin n) (Fin n) ℂ)ˣ | inUJ ε g.val},
      mul_mem' := @aux3 n ε,
      one_mem' := aux4 ε,
      inv_mem' := @aux5 n ε }

@[reducible] noncomputable def instMeasurableSpaceUJ : (n : ℕ) →
  (ε : Fin n → Bool) → MeasurableSpace ↥(UJ ε) :=
  fun _ ε => borel ↥(UJ ε)

attribute [local instance] instMeasurableSpaceUJ

theorem aux8 : ∀ {n : ℕ} (ε : Fin n → Bool),
  IsTopologicalGroup ↥(UJ ε) := by
  intro n ε
  infer_instance

theorem aux9 : ∀ (n : ℕ) (ε : Fin n → Bool),
  BorelSpace ↥(UJ ε) := by
  intro n ε
  exact ⟨rfl⟩

theorem laurent_T_neg_one_mul_T_one : ∀ (n : ℕ) (ε : Fin n → Bool),
  LocallyCompactSpace ↥(UJ ε) := by
  intro n ε
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  have hc : IsClosed {g : (Matrix (Fin n) (Fin n) ℂ)ˣ |
      (g.val).conjTranspose * Jm ε * g.val = Jm ε} :=
    isClosed_eq ((Units.continuous_val.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      Units.continuous_val) continuous_const
  exact hc.locallyCompactSpace

noncomputable def muG : {n : ℕ} →
  (ε : Fin n → Bool) → MeasureTheory.Measure ↥(UJ ε) :=
  fun {n} ε => by
    letI := aux8 ε
    letI := aux9 n ε
    letI := laurent_T_neg_one_mul_T_one n ε
    exact MeasureTheory.Measure.haar

noncomputable def Unimodular : Prop :=
∀ (n : ℕ) (ε : Fin n → Bool) (g : ↥(UJ ε)),
  MeasureTheory.Measure.map (fun x => x * g) (muG ε) =
    muG ε

noncomputable def InvInvariant : Prop :=
∀ (n : ℕ) (ε : Fin n → Bool),
  MeasureTheory.Measure.map (fun x => x⁻¹) (muG ε) =
    muG ε

open scoped Pointwise in
open MeasureTheory MeasureTheory.Measure in
private theorem haar_map_inv {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (h : ∀ g : G, Measure.map (fun x => x * g) (haar : Measure G) = haar) :
    Measure.map (fun x => x⁻¹) (haar : Measure G) = haar := by
  haveI : (haar : Measure G).IsMulRightInvariant := ⟨h⟩
  haveI : (haar : Measure G).Regular := regular_haarMeasure
  obtain ⟨c, hc⟩ : ∃ c : ENNReal, (haar : Measure G).inv = c • haar :=
    ⟨haarScalarFactor (haar : Measure G).inv haar,
      isMulLeftInvariant_eq_smul_of_regular (haar : Measure G).inv haar⟩
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h0 : (haar : Measure G) K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have ht : (haar : Measure G) K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h1 : ∀ s : Set G, (haar : Measure G) s⁻¹ = c * haar s := fun s => by
    rw [← MeasureTheory.Measure.inv_apply, hc, Measure.smul_apply, smul_eq_mul]
  have h2 : c ^ 2 * (haar : Measure G) K = 1 ^ 2 * (haar : Measure G) K := by
    rw [pow_two, mul_assoc, ← h1, ← h1, inv_inv, one_pow, one_mul]
  have h3 : c = 1 :=
    (ENNReal.pow_right_strictMono two_ne_zero).injective ((ENNReal.mul_left_inj h0 ht).1 h2)
  rw [h3, one_smul] at hc
  exact hc

theorem invInvariant_of : Unimodular →
  InvInvariant := by
  intro h n ε
  haveI := aux8 ε
  haveI := aux9 n ε
  haveI := laurent_T_neg_one_mul_T_one n ε
  exact haar_map_inv (G := ↥(UJ ε)) (h n ε)

end UpperTheory.Reformulated.B.InvolutionInvariants
