module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [Field F] → [Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [Field F] →
          [Field Ω] →
            [Algebra F Ω] → (l : ℕ) → [Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycBar :
    (E Ω : Type) →
      [Field E] →
        [Field Ω] →
          [Algebra E Ω] →
            (l : ℕ) → [Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cont_cyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ)
      [Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous (fun x : ℤ_[l] ↦ algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l])) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
