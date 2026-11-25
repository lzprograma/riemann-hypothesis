module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CoreLat

variable {D : D7}

def SelfDualFor {ι : Type} [Fintype ι] (G : Matrix ι ι D.host.E) (Λ : Submodule (𝓞 D.host.E) (ι → D.host.E)) : Prop :=
  Submodule.IsLattice D.host.E Λ ∧ ∀ y : ι → D.host.E, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star x ⬝ᵥ (G *ᵥ y)

theorem form_eq {ι : Type} [Fintype ι] (G : Matrix ι ι D.host.E) (x y : ι → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem isSelfDualC_iff (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) :
    IsSelfDualC S Λ ↔ SelfDualFor S.gram Λ := by
  unfold IsSelfDualC SelfDualFor
  simp only [form_eq]

theorem integral_sign {s b : D.host.E} (hs : s = 1 ∨ s = -1) :
    (∃ o : 𝓞 D.host.E, (o : D.host.E) = s * b) ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = b := by
  rcases hs with rfl | rfl
  · simp
  · constructor
    · rintro ⟨o, ho⟩; exact ⟨-o, by push_cast; linear_combination -ho⟩
    · rintro ⟨o, ho⟩; exact ⟨-o, by push_cast; linear_combination -ho⟩

theorem selfDualFor_map {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {G' : Matrix ι ι D.host.E} {G : Matrix κ κ D.host.E} (Q : Matrix ι κ D.host.E) {s : D.host.E} (hs : s = 1 ∨ s = -1)
    (hG : G = s • (Qᴴ * G' * Q)) (hdet : IsUnit G.det) (hcard : Fintype.card κ = Fintype.card ι)
    {Λ : Submodule (𝓞 D.host.E) (κ → D.host.E)} (hΛ : SelfDualFor G Λ) :
    SelfDualFor G' (Λ.map ((Matrix.mulVecLin Q).restrictScalars (𝓞 D.host.E))) := by
  set P : Matrix κ ι D.host.E := G⁻¹ * (s • (Qᴴ * G')) with hPdef
  have hPQ : P * Q = 1 := by
    rw [hPdef, Matrix.mul_assoc, Matrix.smul_mul, ← hG]
    exact Matrix.nonsing_inv_mul G hdet
  have hQP : Q * P = 1 := (Matrix.mul_eq_one_comm_of_card_eq κ ι D.host.E hcard).1 hPQ
  have mem : ∀ y, y ∈ Λ.map ((Matrix.mulVecLin Q).restrictScalars (𝓞 D.host.E)) ↔ P *ᵥ y ∈ Λ := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
      exact hx
    · intro hy
      refine ⟨P *ᵥ y, hy, ?_⟩
      simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  have form : ∀ x y, star x ⬝ᵥ (G *ᵥ (P *ᵥ y)) = s * (star (Q *ᵥ x) ⬝ᵥ (G' *ᵥ y)) := by
    intro x y
    have h1 : G *ᵥ (P *ᵥ y) = s • (Qᴴ *ᵥ (G' *ᵥ y)) := by
      rw [hG, Matrix.mulVec_mulVec, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hQP,
        Matrix.mul_one, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    rw [h1, dotProduct_smul, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, smul_eq_mul]
  refine ⟨⟨hΛ.1.fg.map _, ?_⟩, ?_⟩
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · intro y
    rw [mem, hΛ.2]
    constructor
    · intro h x' hx'
      rcases hx' with ⟨x, hx, rfl⟩
      have := h x hx
      rw [form, integral_sign hs] at this
      simpa only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] using this
    · intro h x hx
      rw [form, integral_sign hs]
      have := h (Q *ᵥ x) ⟨x, hx, rfl⟩
      exact this

end GlobalTheory.CoreLat

namespace GlobalTheory.CoreLat

variable {D : D7}

def extL (ι κ : Type) : (ι → D.host.E) →ₗ[D.host.E] (ι ⊕ κ → D.host.E) where
  toFun v := Sum.elim v (fun _ => 0)
  map_add' v w := by ext (i | i) <;> simp
  map_smul' c v := by ext (i | i) <;> simp

def extR (ι κ : Type) : (κ → D.host.E) →ₗ[D.host.E] (ι ⊕ κ → D.host.E) where
  toFun v := Sum.elim (fun _ => 0) v
  map_add' v w := by ext (i | i) <;> simp
  map_smul' c v := by ext (i | i) <;> simp

def sumLat {ι κ : Type} (ΛA : Submodule (𝓞 D.host.E) (ι → D.host.E)) (ΛB : Submodule (𝓞 D.host.E) (κ → D.host.E)) :
    Submodule (𝓞 D.host.E) (ι ⊕ κ → D.host.E) :=
  ΛA.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E Sum.inl) ⊓ ΛB.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E Sum.inr)

theorem mem_sumLat {ι κ : Type} {ΛA : Submodule (𝓞 D.host.E) (ι → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (κ → D.host.E)}
    (y : ι ⊕ κ → D.host.E) : y ∈ sumLat ΛA ΛB ↔ y ∘ Sum.inl ∈ ΛA ∧ y ∘ Sum.inr ∈ ΛB := by
  simp [sumLat, LinearMap.funLeft]

theorem split_vec {ι κ : Type} (y : ι ⊕ κ → D.host.E) :
    y = extL (D := D) ι κ (y ∘ Sum.inl) + extR (D := D) ι κ (y ∘ Sum.inr) := by
  ext (i | i) <;> simp [extL, extR]

theorem form_sum {ι κ : Type} [Fintype ι] [Fintype κ] (GA : Matrix ι ι D.host.E) (GB : Matrix κ κ D.host.E)
    (x y : ι ⊕ κ → D.host.E) :
    star x ⬝ᵥ (fromBlocks GA 0 0 GB *ᵥ y) =
      star (x ∘ Sum.inl) ⬝ᵥ (GA *ᵥ (y ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (GB *ᵥ (y ∘ Sum.inr)) := by
  rw [Matrix.fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, zero_add, add_zero,
    Pi.star_apply, Function.comp_apply]

theorem selfDualFor_sum {ι κ : Type} [Fintype ι] [Fintype κ] {GA : Matrix ι ι D.host.E} {GB : Matrix κ κ D.host.E}
    {ΛA : Submodule (𝓞 D.host.E) (ι → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (κ → D.host.E)}
    (hA : SelfDualFor GA ΛA) (hB : SelfDualFor GB ΛB) : SelfDualFor (fromBlocks GA 0 0 GB) (sumLat ΛA ΛB) := by
  have heq : sumLat ΛA ΛB = ΛA.map ((extL (D := D) ι κ).restrictScalars (𝓞 D.host.E)) ⊔
      ΛB.map ((extR (D := D) ι κ).restrictScalars (𝓞 D.host.E)) := by
    apply le_antisymm
    · intro y hy
      rw [mem_sumLat] at hy
      rw [split_vec (D := D) y]
      exact Submodule.add_mem_sup ⟨_, hy.1, rfl⟩ ⟨_, hy.2, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        rw [mem_sumLat]
        refine ⟨by simpa [extL, extR] using hx, ?_⟩
        have : (extL (D := D) ι κ x) ∘ Sum.inr = 0 := by ext i; simp [extL]
        simp only [LinearMap.coe_restrictScalars] at this ⊢
        rw [this]; exact ΛB.zero_mem
      · rintro _ ⟨x, hx, rfl⟩
        rw [mem_sumLat]
        refine ⟨?_, by simpa [extL, extR] using hx⟩
        have : (extR (D := D) ι κ x) ∘ Sum.inl = 0 := by ext i; simp [extR]
        simp only [LinearMap.coe_restrictScalars] at this ⊢
        rw [this]; exact ΛA.zero_mem
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [heq]; exact (hA.1.fg.map _).sup (hB.1.fg.map _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · intro y
    rw [mem_sumLat, hA.2, hB.2]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rw [mem_sumLat] at hx
      obtain ⟨b1, hb1⟩ := h1 _ hx.1
      obtain ⟨b2, hb2⟩ := h2 _ hx.2
      exact ⟨b1 + b2, by rw [form_sum, ← hb1, ← hb2]; norm_cast⟩
    · intro h
      constructor
      · intro x hx
        have hm : extL (D := D) ι κ x ∈ sumLat ΛA ΛB := by
          rw [mem_sumLat]
          refine ⟨by simpa [extL, extR] using hx, ?_⟩
          have : (extL (D := D) ι κ x) ∘ Sum.inr = 0 := by ext i; simp [extL]
          rw [this]; exact ΛB.zero_mem
        obtain ⟨b, hb⟩ := h _ hm
        refine ⟨b, ?_⟩
        rw [hb, form_sum]
        have e1 : (extL (D := D) ι κ x) ∘ Sum.inl = x := by ext i; simp [extL]
        have e2 : (extL (D := D) ι κ x) ∘ Sum.inr = 0 := by ext i; simp [extL]
        rw [e1, e2]; simp
      · intro x hx
        have hm : extR (D := D) ι κ x ∈ sumLat ΛA ΛB := by
          rw [mem_sumLat]
          refine ⟨?_, by simpa [extL, extR] using hx⟩
          have : (extR (D := D) ι κ x) ∘ Sum.inl = 0 := by ext i; simp [extR]
          rw [this]; exact ΛA.zero_mem
        obtain ⟨b, hb⟩ := h _ hm
        refine ⟨b, ?_⟩
        rw [hb, form_sum]
        have e1 : (extR (D := D) ι κ x) ∘ Sum.inl = 0 := by ext i; simp [extR]
        have e2 : (extR (D := D) ι κ x) ∘ Sum.inr = x := by ext i; simp [extR]
        rw [e1, e2]; simp

theorem line_mat_eq {κ : Type} [Fintype κ] (hk : Fintype.card κ = 1) {M N : Matrix κ κ D.host.E} {ζ : κ → D.host.E}
    (hζ : star ζ ⬝ᵥ (M *ᵥ ζ) ≠ 0) (h : star ζ ⬝ᵥ (M *ᵥ ζ) = star ζ ⬝ᵥ (N *ᵥ ζ)) : M = N := by
  obtain ⟨k, hk'⟩ := Fintype.card_eq_one_iff.1 hk
  have hu : (Finset.univ : Finset κ) = {k} := by ext i; simp [hk' i]
  have ev : ∀ A : Matrix κ κ D.host.E, star ζ ⬝ᵥ (A *ᵥ ζ) = star (ζ k) * (A k k * ζ k) := by
    intro A; simp [dotProduct, Matrix.mulVec, hu]
  rw [ev, ev] at h
  rw [ev] at hζ
  have h0 : star (ζ k) ≠ 0 := fun h0 => hζ (by rw [h0, zero_mul])
  have h1 : ζ k ≠ 0 := fun h1 => hζ (by rw [h1, mul_zero, mul_zero])
  have hkk : M k k = N k k := by
    have := mul_left_cancel₀ h0 h
    exact mul_right_cancel₀ h1 this
  exact Matrix.ext fun i j => by rw [hk' i, hk' j]; exact hkk

end GlobalTheory.CoreLat

namespace GlobalTheory.CoreLat

theorem exists_prime_not_mem (K : Type) [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ((n : 𝓞 K)) ∉ p.asIdeal := by
  obtain ⟨q, hqn, hq⟩ := Nat.exists_infinite_primes (n + 1)
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  haveI hP : (Ideal.span {(q : ℤ)}).IsPrime := (Ideal.span_singleton_prime hq0).2 hqZ
  have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := by
    intro a b hab
    simpa using hab
  obtain ⟨Q, -, hQ, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(q : ℤ)}) ⊥ (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := hinj (by rw [hx, map_zero])
    rw [this]; exact Ideal.zero_mem _)
  rw [Ideal.under_def] at hcomap
  have hqQ : algebraMap ℤ (𝓞 K) (q : ℤ) ∈ Q := by
    rw [← Ideal.mem_comap, hcomap]; exact Ideal.subset_span rfl
  have hne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hqQ
    exact hq0 (hinj (by rw [hqQ, map_zero]))
  refine ⟨⟨Q, hQ, hne⟩, ?_⟩
  intro hmem
  have : algebraMap ℤ (𝓞 K) (n : ℤ) ∈ Q := by simpa using hmem
  rw [← Ideal.mem_comap, hcomap, Ideal.mem_span_singleton] at this
  have hdvd : q ∣ n := by exact_mod_cast this
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  omega

end GlobalTheory.CoreLat

namespace GlobalTheory.CoreLat

variable {D : D7}

theorem quad_mul {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix ι κ D.host.E) (G : Matrix ι ι D.host.E) (x : κ → D.host.E) :
    star x ⬝ᵥ ((Aᴴ * (G * A)) *ᵥ x) = star (A *ᵥ x) ⬝ᵥ (G *ᵥ (A *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec]

theorem quad_smul {κ : Type} [Fintype κ] (c : D.host.E) (G : Matrix κ κ D.host.E) (x : κ → D.host.E) :
    star (c • x) ⬝ᵥ (G *ᵥ (c • x)) = star c * c * (star x ⬝ᵥ (G *ᵥ x)) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem quad_smul_mat {κ : Type} [Fintype κ] (c : D.host.E) (G : Matrix κ κ D.host.E) (x : κ → D.host.E) :
    star x ⬝ᵥ ((c • G) *ᵥ x) = c * (star x ⬝ᵥ (G *ᵥ x)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

end GlobalTheory.CoreLat
