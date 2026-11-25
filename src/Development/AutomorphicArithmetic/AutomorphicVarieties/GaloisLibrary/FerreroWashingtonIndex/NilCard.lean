module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

@[expose] public section

open UpperTheory.V.FW

private theorem card_le_card_ker_mul_card_map {V : Type} [AddCommGroup V] [Finite V] (f : V →+ V)
    (H : AddSubgroup V) :
    Nat.card H ≤ Nat.card (AddMonoidHom.ker f) * Nat.card (H.map f) := by
  have h1 := AddSubgroup.card_ker_mul_card_range (f.comp H.subtype)
  rw [← AddMonoidHom.map_range, AddSubgroup.range_subtype] at h1
  refine h1.symm.trans_le (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective
    (fun x : (f.comp H.subtype).ker => (⟨x.1.1, x.2⟩ : f.ker))
    fun _ _ e => Subtype.ext (Subtype.ext (congrArg (fun y : f.ker => y.1) e))))

theorem UpperTheory.V.FW.nilCard :
    ∀ (V : Type) [AddCommGroup V] [Finite V] (T : AddMonoid.End V) (N : ℕ), T ^ N = 0 → Nat.card V ≤ (AddMonoidHom.range T).index ^ N := by
  intro V _ _ T N hN
  set K := Nat.card (AddMonoidHom.ker (T : V →+ V)) with hK
  have hidx : (AddMonoidHom.range (T : V →+ V)).index = K :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (by
      rw [AddSubgroup.card_mul_index, hK, mul_comm,
        AddSubgroup.card_ker_mul_card_range (T : V →+ V)])
  have step : ∀ k : ℕ, Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V))
      ≤ K * Nat.card (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V)) := by
    intro k
    have h := card_le_card_ker_mul_card_map (T : V →+ V) (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V))
    have e : (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)).map (T : V →+ V)
        = AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V) := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        refine ⟨x, ?_⟩
        rw [pow_succ']
        rfl
      · rintro ⟨x, rfl⟩
        refine ⟨(T ^ k) x, ⟨x, rfl⟩, ?_⟩
        rw [pow_succ']
        rfl
    rw [e] at h
    exact h
  have main : ∀ k : ℕ, Nat.card V
      ≤ K ^ k * Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, Nat.one_mul]
      refine Nat.card_le_card_of_injective
        (fun x => (⟨x, x, by rw [pow_zero]; rfl⟩ :
          AddMonoidHom.range ((T ^ 0 : AddMonoid.End V) : V →+ V))) ?_
      intro a b hab
      simpa using congrArg Subtype.val hab
    | succ k ih =>
      calc Nat.card V
          ≤ K ^ k * Nat.card (AddMonoidHom.range ((T ^ k : AddMonoid.End V) : V →+ V)) := ih
        _ ≤ K ^ k * (K * Nat.card
            (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V))) :=
          Nat.mul_le_mul_left _ (step k)
        _ = K ^ (k + 1) * Nat.card
            (AddMonoidHom.range ((T ^ (k + 1) : AddMonoid.End V) : V →+ V)) := by ring
  have hN1 : Nat.card (AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V)) ≤ 1 := by
    have hinj : Function.Injective
        (fun _ : AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V) => ()) := by
      rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩ _
      apply Subtype.ext
      show (T ^ N) x = (T ^ N) y
      rw [hN]
      rfl
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  rw [hidx]
  calc Nat.card V
      ≤ K ^ N * Nat.card (AddMonoidHom.range ((T ^ N : AddMonoid.End V) : V →+ V)) := main N
    _ ≤ K ^ N * 1 := Nat.mul_le_mul_left _ hN1
    _ = K ^ N := Nat.mul_one _
