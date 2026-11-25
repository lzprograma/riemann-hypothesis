module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ExistsNatLocal
public import Lemmata.NatMulIsIntegral.ExistsNatMulIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties

@[expose] public section

noncomputable section

namespace PI.WAU.B

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.UG Matrix
open scoped TensorProduct

theorem exists_gen {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Lb) :
    ∃ (k : ℕ) (m : Fin k → Fin n → E), (∀ i, m i ∈ Lb) ∧
      (∀ l ∈ Lb, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) := by
  have : Module.Finite ℤ Lb := Module.Finite.trans (𝓞 E) Lb
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Lb)
  refine ⟨k, fun i => (s i : Fin n → E), fun i => (s i).2, fun l hl => ?_⟩
  have hmem : (⟨l, hl⟩ : Lb) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
  refine ⟨z, ?_⟩
  have h2 := congrArg Subtype.val hz
  simp only [Submodule.coe_sum] at h2
  exact h2.symm

theorem exists_nat_E {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ c : ℕ, 0 < c ∧ ∃ t : 𝓞 E, (c : E) * e = algebraMap (𝓞 E) E t := by
  apply _root_.GlobalTheory.CoordinateBasisBounds.nat_mul_integral <;> assumption

theorem common_nat {ι : Type} [Fintype ι] (P : ι → ℕ → Prop)
    (hP : ∀ i N M, P i N → P i (N * M)) (h : ∀ i, ∃ N, 0 < N ∧ P i N) :
    ∃ N, 0 < N ∧ ∀ i, P i N := by
  classical
  choose f hf0 hf using h
  refine ⟨∏ i, f i, Finset.prod_pos fun i _ => hf0 i, fun i => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  rw [hk]
  exact hP i _ _ (hf i)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

abbrev incA (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a : Af F) :
    E ⊗[F] Af F :=
  (Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F) a

abbrev ivec (x : Fin n → E) : Fin n → E ⊗[F] Af F := fun i => inclE (F := F) (Af F) (x i)

theorem left_mem (t : 𝓞 E) : ((algebraMap (𝓞 E) E t) ⊗ₜ[F] (1 : Af F)) ∈ IntAf F E :=
  Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E t, ⟨t, rfl⟩⟩, rfl⟩)

theorem incA_mem {a : Af F} (ha : a ∈ intAd F) : incA F E a ∈ IntAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem ivec_mem {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} (hx : x ∈ L) :
    ivec (F := F) x ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

theorem smulO_mem {L : Submodule (𝓞 E) (Fin n → E)} {o : E ⊗[F] Af F} (ho : o ∈ IntAf F E)
    {w : Fin n → E ⊗[F] Af F} (hw : w ∈ lamAf (F := F) L) : o • w ∈ lamAf (F := F) L :=
  Submodule.smul_mem _ (⟨o, ho⟩ : IntAf F E) hw

theorem nsmul_lam {L : Submodule (𝓞 E) (Fin n → E)} {w : Fin n → E ⊗[F] Af F} {N : ℕ}
    (hw : N • w ∈ lamAf (F := F) L) (M : ℕ) : (N * M) • w ∈ lamAf (F := F) L := by
  rw [mul_comm, mul_smul]
  exact nsmul_mem hw M

def Tset {k : ℕ} (m : Fin k → Fin n → E) : Set (Fin n → E ⊗[F] Af F) :=
  {w | ∃ a : Fin k → Af F, (∀ j, a j ∈ intAd F) ∧ w = ∑ j, incA F E (a j) • ivec (F := F) (m j)}

section T

variable {k : ℕ} {m : Fin k → Fin n → E}

theorem T_zero : (0 : Fin n → E ⊗[F] Af F) ∈ Tset (F := F) m :=
  ⟨0, fun _ => zero_mem _, by simp⟩

theorem T_add {w w' : Fin n → E ⊗[F] Af F} (hw : w ∈ Tset (F := F) m) (hw' : w' ∈ Tset (F := F) m) :
    w + w' ∈ Tset (F := F) m := by
  obtain ⟨a, ha, rfl⟩ := hw
  obtain ⟨a', ha', rfl⟩ := hw'
  refine ⟨a + a', fun j => add_mem (ha j) (ha' j), ?_⟩
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, map_add (f := _), add_smul]

theorem T_neg {w : Fin n → E ⊗[F] Af F} (hw : w ∈ Tset (F := F) m) : -w ∈ Tset (F := F) m := by
  obtain ⟨a, ha, rfl⟩ := hw
  refine ⟨-a, fun j => neg_mem (ha j), ?_⟩
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.neg_apply, map_neg, neg_smul]

theorem T_smulA {b : Af F} (hb : b ∈ intAd F) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ Tset (F := F) m) : incA F E b • w ∈ Tset (F := F) m := by
  obtain ⟨a, ha, rfl⟩ := hw
  refine ⟨fun j => b * a j, fun j => mul_mem hb (ha j), ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [smul_smul]

theorem T_sum {ι : Type} (s : Finset ι) (f : ι → Fin n → E ⊗[F] Af F)
    (h : ∀ i ∈ s, f i ∈ Tset (F := F) m) : ∑ i ∈ s, f i ∈ Tset (F := F) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using T_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact T_add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem ivec_zsum (z : Fin k → ℤ) :
    ivec (F := F) (∑ i, z i • m i) = ∑ i, incA F E (z i : Af F) • ivec (F := F) (m i) := by
  funext r

  simp [ivec, Finset.sum_apply, map_sum, Int.cast_smul_eq_zsmul]

theorem T_gen {L : Submodule (𝓞 E) (Fin n → E)}
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) {x : Fin n → E} (hx : x ∈ L) :
    ivec (F := F) x ∈ Tset (F := F) m := by
  obtain ⟨z, rfl⟩ := hgen x hx
  exact ⟨fun i => (z i : Af F), fun i => intCast_mem _ _, ivec_zsum z⟩

theorem left_smul_ivec (t : 𝓞 E) (x : Fin n → E) :
    ((algebraMap (𝓞 E) E t) ⊗ₜ[F] (1 : Af F)) • ivec (F := F) x = ivec (F := F) (t • x) := by
  funext r
  simp [ivec, inclE, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]

theorem T_smul_left {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) (t : 𝓞 E) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ Tset (F := F) m) :
    ((algebraMap (𝓞 E) E t) ⊗ₜ[F] (1 : Af F)) • w ∈ Tset (F := F) m := by
  obtain ⟨a, ha, rfl⟩ := hw
  rw [Finset.smul_sum]
  refine T_sum _ _ fun j _ => ?_
  rw [smul_comm, left_smul_ivec]
  exact T_smulA (ha j) (T_gen hgen (L.smul_mem t (hm j)))

theorem T_smulO {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) {o : E ⊗[F] Af F}
    (ho : o ∈ IntAf F E) : ∀ w ∈ Tset (F := F) m, o • w ∈ Tset (F := F) m := by
  unfold IntAf tensInt at ho
  induction ho using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨s, hs⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
    · obtain ⟨t, rfl⟩ := hs
      intro w hw
      exact T_smul_left hm hgen t hw
    · intro w hw
      exact T_smulA ha hw
  | zero => intro w _; rw [zero_smul]; exact T_zero
  | one => intro w hw; rwa [one_smul]
  | add x y _ _ hx hy => intro w hw; rw [add_smul]; exact T_add (hx w hw) (hy w hw)
  | neg x _ hx => intro w hw; rw [neg_smul]; exact T_neg (hx w hw)
  | mul x y _ _ hx hy => intro w hw; rw [mul_smul]; exact hx _ (hy w hw)

theorem lam_sub_alt {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ lamAf (F := F) L) : w ∈ Tset (F := F) m := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨y, hy⟩, rfl⟩ := hx
    exact T_gen hgen hy
  | zero => exact T_zero
  | add x y _ _ hx hy => exact T_add hx hy
  | smul o x _ hx => exact T_smulO hm hgen o.2 x hx

theorem mulVec_lam {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    (P : Matrix (Fin n) (Fin n) (E ⊗[F] Af F))
    (hP : ∀ j, P *ᵥ ivec (F := F) (m j) ∈ lamAf (F := F) L) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ lamAf (F := F) L) : P *ᵥ w ∈ lamAf (F := F) L := by
  obtain ⟨a, ha, rfl⟩ := lam_sub_alt hm hgen hw
  rw [Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Matrix.mulVec_smul]
  exact smulO_mem (incA_mem (ha j)) (hP j)

end T

theorem exists_nat_R (r : E ⊗[F] Af F) : ∃ N : ℕ, 0 < N ∧ (N : E ⊗[F] Af F) * r ∈ IntAf F E := by
  apply _root_.GlobalTheory.St.G.IntAd.exists_nat_denom <;> assumption

theorem exists_nat_L {L : Submodule (𝓞 E) (Fin n → E)}
    {z : Fin n → E} (hz : z ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ N : ℕ, 0 < N ∧ N • z ∈ L := by
  first | (apply Bl.NatMulIsIntegral.goal1 <;> assumption)

theorem exists_nat_vec {L : Submodule (𝓞 E) (Fin n → E)}
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E ⊗[F] Af F) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ lamAf (F := F) L := by
  classical
  have hi : ∀ i, ∃ N, 0 < N ∧ N • ((w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F)) ∈
      lamAf (F := F) L := by
    intro i
    obtain ⟨A, hA0, hA⟩ := exists_nat_R (F := F) (E := E) (w i)
    obtain ⟨B, hB0, hB⟩ := _root_.Bl.NatMulIsIntegral.goal1 (L := L) (z := Pi.single i 1)
      (by rw [hspan]; exact Submodule.mem_top)
    refine ⟨A * B, Nat.mul_pos hA0 hB0, ?_⟩
    have e1 : ivec (F := F) (B • (Pi.single i 1 : Fin n → E)) =
        (B : E ⊗[F] Af F) • (Pi.single i 1 : Fin n → E ⊗[F] Af F) := by
      funext j
      by_cases h : j = i
      · subst h; simp [ivec]
      · simp [ivec, h]
    have e2 : (A * B) • ((w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F)) =
        ((A : E ⊗[F] Af F) * w i) • ivec (F := F) (B • (Pi.single i 1 : Fin n → E)) := by
      rw [e1, smul_smul, ← Nat.cast_smul_eq_nsmul (E ⊗[F] Af F), smul_smul]
      congr 1
      push_cast; ring
    rw [e2]
    exact smulO_mem hA (ivec_mem hB)
  obtain ⟨N, hN0, hN⟩ := common_nat
    (fun i N => N • ((w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F)) ∈ lamAf (F := F) L)
    (fun i N M h => nsmul_lam h M) hi
  refine ⟨N, hN0, ?_⟩
  have ew : w = ∑ i, (w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [ew, Finset.smul_sum]
  exact Submodule.sum_mem _ fun i _ => hN i

end PI.WAU.B
