module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CoarseMultAt
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.WeightWLet
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockMonomial
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TopOddNeEnd

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem leading_exponent_weighted_homog (b : SegBlock (segS X.TT j) X.m) (ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ)
    (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ) (hB : Balanced X.m (X.seg C0 CE1 CE2 j) ω' ωL) :
    IsWeightedHomogeneous ω' (monomial (mu0 C0 CE1 CE2 X j b) (1 : KK ℤ))
      (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω' ωL) := by
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ (fun i c => c • ω' i) (fun _ => zero_smul _ _)]
  simpa [smul_eq_mul] using leading_exponent_homogeneous C0 CE1 CE2 X j b ω' ωL hB

theorem tdeg_eq (b : SegBlock (segS X.TT j) X.m) (hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (ho : b.oPlus ≤ segAPlus X.TT X.aT j) (x : X.TT × Bool) :
    tdeg C0 CE1 CE2 X j b x = (if segNext X.TT j = x.1.val then hhDegs X.TT X.aT X.bT x else 0) +
        ∑ i, (if segPos X.TT j i = x.1.val then hhDegs X.TT X.aT X.bT x else 0) := by
  have hwh := ioBlock_wh C0 CE1 CE2 X j ℤ b (wLet X x) (fun _ _ _ => rfl) (fun _ => rfl) rfl
    (monomial (mu0 C0 CE1 CE2 X j b) 1)
    (fun ω' ωL h1 h2 h3 => leading_exponent_weighted_homog C0 CE1 CE2 X j b ω' ωL ⟨h1, h2, h3⟩)
  rw [ioBlock_monomial] at hwh
  have h1 := hwh (by rw [coeff_monomial, ite_eq_left rfl]; exact one_ne_zero)
  rw [weight_wLet] at h1
  unfold tdeg
  rw [h1, TD_wLet_of_bounds C0 CE1 CE2 X j x b hk.1
      (fun i h => (hk.2.2.1 i h).2.1) (fun i h => (hk.2.2.1 i h).2.2.1)
      (fun i h => (hk.2.1 i h).1) ho]

theorem segPos_inj : Function.Injective (segPos X.TT j) := by
  intro i i' h
  exact topOdd_inj X j (Subtype.ext h)

@[to_additive]
theorem prod_tdeg {M : Type} [CommMonoid M] (g : ℕ → M) (hg : g 0 = 1) (b : SegBlock (segS X.TT j) X.m)
    (hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (ho : b.oPlus ≤ segAPlus X.TT X.aT j) :
    ∏ x : X.TT × Bool, g (tdeg C0 CE1 CE2 X j b x) =
      (∏ i : Fin (segS X.TT j), g (X.bT (segPos X.TT j i)) * g (X.aT (segPos X.TT j i))) *
        g (X.aT (segNext X.TT j)) * g (X.bT (segNext X.TT j)) := by
  classical
  set T : Fin X.n' → Bool → ℕ := fun t β => (if segNext X.TT j = t then hhDeg X.aT X.bT t β else 0) +
    ∑ i, (if segPos X.TT j i = t then hhDeg X.aT X.bT t β else 0) with hT
  have e : ∀ x : X.TT × Bool, tdeg C0 CE1 CE2 X j b x = T x.1.val x.2 := fun x => tdeg_eq C0 CE1 CE2 X j b hk ho x
  simp only [e]
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool]
  rw [Finset.prod_coe_sort X.TT (fun t => g (T t true) * g (T t false))]
  have hnp : ∀ i, segPos X.TT j i ≠ segNext X.TT j := fun i h => (pos_mem X.TT j i).2 (h ▸ (next_mem X.TT j).2)
  have hS : insert (segNext X.TT j) (Finset.univ.image (segPos X.TT j)) ⊆ X.TT := by
    intro t ht
    rcases Finset.mem_insert.1 ht with h | h
    · rw [h]; exact (next_mem X.TT j).1
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 h
      exact (pos_mem X.TT j i).1
  rw [← Finset.prod_subset hS (fun t _ ht => by
    have h1 : segNext X.TT j ≠ t := fun h => ht (h ▸ Finset.mem_insert_self _ _)
    have h2 : ∀ i, segPos X.TT j i ≠ t := fun i h => ht (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩))
    simp only [hT, ite_eq_right h1, ite_eq_right (h2 _), Finset.sum_const_zero, add_zero, hg, mul_one])]
  rw [Finset.prod_insert (fun h => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h
    exact hnp i hi), Finset.prod_image (fun i _ i' _ h => segPos_inj X j h)]
  have hnext : ∀ β, T (segNext X.TT j) β = hhDeg X.aT X.bT (segNext X.TT j) β := by
    intro β
    show (if segNext X.TT j = segNext X.TT j then hhDeg X.aT X.bT (segNext X.TT j) β else 0) +
      ∑ i, (if segPos X.TT j i = segNext X.TT j then hhDeg X.aT X.bT (segNext X.TT j) β else 0) = _
    rw [ite_eq_left rfl, Finset.sum_eq_zero (fun i _ => ite_eq_right (hnp i)), add_zero]
  have hpos : ∀ i β, T (segPos X.TT j i) β = hhDeg X.aT X.bT (segPos X.TT j i) β := by
    intro i β
    show (if segNext X.TT j = segPos X.TT j i then hhDeg X.aT X.bT (segPos X.TT j i) β else 0) +
      ∑ i', (if segPos X.TT j i' = segPos X.TT j i then hhDeg X.aT X.bT (segPos X.TT j i) β else 0) = _
    rw [ite_eq_right (fun h : segNext X.TT j = segPos X.TT j i => hnp i h.symm), zero_add]
    rw [Finset.sum_eq_single i (fun i' _ hi' => ite_eq_right (fun h => hi' (segPos_inj X j h))) (fun h => absurd (Finset.mem_univ _) h),
      ite_eq_left rfl]
  have hev := (next_mem X.TT j).2
  simp only [hnext, hpos, hhDeg, ite_true, Bool.false_eq_true, ite_false, ite_eq_left hev]
  have hodd : ∀ i, ¬ Even (segPos X.TT j i).val := fun i => (pos_mem X.TT j i).2
  simp only [hodd, ite_false]
  rw [mul_comm (g (X.aT (segNext X.TT j)) * g (X.bT (segNext X.TT j))), mul_assoc]

end

theorem trueDegAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hO : OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    TrueDegAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD1 hH hc j b hb
  have ho := hO X hD1 hH hc j b hb
  constructor
  · rw [prod_tdeg C0 CE1 CE2 X j Nat.factorial rfl b hb ho]
    rfl
  · rw [sum_tdeg C0 CE1 CE2 X j (Nat.log X.p) (Nat.log_zero_right _) b hb ho]
    unfold lgSeg
    rw [Finset.sum_add_distrib]

end Formalism.MainNotions.ColumnSystems.Pf
