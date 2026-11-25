module

public import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorsDisjointColumnsHarmonic

@[expose] public section

noncomputable section

namespace GlobalTheory.ThetaClaimsCompare

theorem gaps_sum (b : ℕ → ℕ) (hb : Antitone b) (N i : ℕ) (hi : i ≤ N) :
    ∑ s ∈ Finset.range N, (if i ≤ s then b s - b (s + 1) else 0) = b i - b N := by
  induction N, hi using Nat.le_induction with
  | base =>
    rw [Nat.sub_self]
    exact Finset.sum_eq_zero fun s hs => ite_eq_right (by simpa using hs)
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ih, ite_eq_left hN]
    have := hb hN
    have := hb (Nat.le_succ N)
    simp only [Nat.succ_eq_add_one] at this
    omega

end GlobalTheory.ThetaClaimsCompare

namespace GlobalTheory.BlockProdEx

section Minors

open MvPolynomial Formalism.L2.Pj

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k]
  (col : ∀ σ, ∀ s : Fin (r σ), Fin (s + 1) → Fin n)

def minor (R : Type) [CommRing R] (σ : T) (s : Fin (r σ)) : MvPolynomial (Letter T r n) R :=
  (Matrix.of fun i j : Fin (s + 1) =>
    (X ⟨σ, Fin.castLE s.isLt i, col σ s j⟩ : MvPolynomial (Letter T r n) R)).det

def minorsP (R : Type) [CommRing R] (a : T → ℕ → ℕ) : MvPolynomial (Letter T r n) R :=
  ∏ σ, ∏ s : Fin (r σ), minor r n col R σ s ^ (a σ s - a σ (s + 1))

theorem minorMonomial_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : T → ℕ → ℕ) :
    MvPolynomial.map φ (minorsP r n col R a) = minorsP r n col R' a := by
  simp only [minorsP, map_prod, map_pow, minor, RingHom.map_det]
  refine Finset.prod_congr rfl fun σ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext1 i j
  simp

theorem minorMonomial_coeff_mem (a : T → ℕ → ℕ) (O : Subring k) (m : Letter T r n →₀ ℕ) :
    (minorsP r n col k a).coeff m ∈ O := by
  rw [← minorMonomial_map r n col (Int.castRingHom k), coeff_map]
  exact intCast_mem O _

omit [Fintype T] in
theorem minor_ne_zero (hcol : ∀ σ s, Function.Injective (col σ s)) (σ : T) (s : Fin (r σ)) :
    minor r n col k σ s ≠ 0 := by
  classical
  intro h
  have h1 : MvPolynomial.eval (fun ℓ : Letter T r n =>
      if ∃ j : Fin (s + 1), (j : ℕ) = ℓ.2.1 ∧ ℓ.2.2 = col σ s j then (1 : k) else 0)
      (minor r n col k σ s) = 1 := by
    simp only [minor, RingHom.map_det]
    rw [show (MvPolynomial.eval _).mapMatrix _ = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) k) from ?_,
      Matrix.det_one]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_X, Matrix.one_apply,
      (hcol σ s).eq_iff, Fin.val_castLE, Fin.val_inj, exists_eq_left]
    exact if_congr eq_comm rfl rfl
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem minorMonomial_ne_zero (hcol : ∀ σ s, Function.Injective (col σ s)) (a : T → ℕ → ℕ) :
    minorsP r n col k a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun σ _ => Finset.prod_ne_zero_iff.2 fun s _ =>
    pow_ne_zero _ (minor_ne_zero r n k col hcol σ s)

theorem minorMonomial_mem_harmonic (cc : T → T) (isX : T → Prop)
    (hdis : ∀ τ, isX τ → ∀ s s' i j, col τ s i ≠ col (cc τ) s' j) (a : T → ℕ → ℕ) :
    minorsP r n col k a ∈ harmK r n k cc isX (fun _ => 1) := by
  classical
  let S : Set (Letter T r n) := {v | ∃ s j, col v.1 s j = v.2.2}
  have hS : minorsP r n col k a ∈ MvPolynomial.supported k S := by
    refine Subalgebra.prod_mem _ fun t _ => Subalgebra.prod_mem _ fun s _ => Subalgebra.pow_mem _ ?_ _
    rw [minor, Matrix.det_apply']
    refine Subalgebra.sum_mem _ fun g _ => Subalgebra.mul_mem _ (intCast_mem _ _)
      (Subalgebra.prod_mem _ fun a _ => ?_)
    exact Algebra.subset_adjoin ⟨_, ⟨_, _, rfl⟩, rfl⟩
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ hτ i i'
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Derivation.coeFn_coe]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  by_cases hbb : b = b'
  · subst hbb
    by_cases hb : ∃ s j, col (cc τ) s j = b
    · obtain ⟨s', j', hj'⟩ := hb
      rw [minorHarm_pderiv_comm, minorHarm_pderiv_eq_zero hS, map_zero, smul_zero]
      rintro ⟨s, j, hj⟩
      exact hdis τ hτ s s' j j' (hj.trans hj'.symm)
    · rw [minorHarm_pderiv_eq_zero hS (v := ⟨cc τ, i', b⟩) hb, map_zero, smul_zero]
  · rw [Matrix.one_apply_ne hbb, zero_smul]

omit [Fintype T] in
theorem rowShift_minor (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : k) (σ' : T) (s : Fin (r σ')) :
    rowShift r n k σ i i' t (minor r n col k σ' s) = minor r n col k σ' s := by
  classical
  rw [minor, AlgHom.map_det]
  by_cases h : ∃ u : Fin (s + 1), (⟨σ', Fin.castLE s.isLt u⟩ : Σ σ, Fin (r σ)) = ⟨σ, i⟩
  · obtain ⟨u, hu⟩ := h
    obtain ⟨rfl, hu'⟩ := Sigma.mk.inj_iff.1 hu
    have hu'' : Fin.castLE s.isLt u = i := eq_of_heq hu'
    subst hu''
    have hi' : (i' : ℕ) < u := hi
    let u' : Fin (s + 1) := ⟨i', hi'.trans u.isLt⟩
    have hne : u ≠ u' := fun e => by
      have := congrArg Fin.val e
      simp only [u'] at this
      omega
    refine Eq.trans ?_ (Matrix.det_updateRow_add_smul_self _ hne (C t))
    congr 1
    ext1 x y
    by_cases hx : x = u
    · subst hx
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X,
        Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [ite_eq_left ⟨_, rfl⟩]
      rfl
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X,
        Matrix.updateRow_ne hx]
      rw [ite_eq_right]
      rintro ⟨b, hb⟩
      have := eq_of_heq (Sigma.mk.inj_iff.1 hb).2
      exact hx (Fin.castLE_injective s.isLt (congrArg Prod.fst this))
  · congr 1
    ext1 x y
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X]
    rw [ite_eq_right]
    rintro ⟨b, hb⟩
    obtain ⟨rfl, hb'⟩ := Sigma.mk.inj_iff.1 hb
    exact h ⟨x, by rw [show Fin.castLE s.isLt x = i from congrArg Prod.fst (eq_of_heq hb')]⟩

theorem minorMonomial_rowInvariant (a : T → ℕ → ℕ) : RowInv r n k (minorsP r n col k a) := by
  intro σ i i' hi t
  simp only [minorsP, map_prod, map_pow, rowShift_minor r n k col σ i i' hi t]

omit [Fintype T] in
theorem minor_weighted (w : (Σ σ, Fin (r σ)) → ℕ) (σ : T) (s : Fin (r σ)) :
    (minor r n col k σ s).IsWeightedHomogeneous (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
      (∑ j : Fin (s + 1), w ⟨σ, Fin.castLE s.isLt j⟩) := by
  rw [minor, Matrix.det_apply']
  refine IsWeightedHomogeneous.sum _ _ _ fun g _ => ?_
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
    (Finset.univ : Finset (Fin (s + 1)))
    (fun j => (X ⟨σ, Fin.castLE s.isLt (g j), col σ s j⟩ : MvPolynomial (Letter T r n) k))
    (fun j => w ⟨σ, Fin.castLE s.isLt (g j)⟩) (fun j _ => isWeightedHomogeneous_X _ _ _)
  rw [Equiv.sum_comp g (fun j => w ⟨σ, Fin.castLE s.isLt j⟩)] at h
  have h2 := (isWeightedHomogeneous_C (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
    (((Equiv.Perm.sign g : ℤˣ) : ℤ) : k)).mul h
  simpa using h2

theorem minorMonomial_rowDegree (a : T → ℕ → ℕ) (ha : ∀ σ, Antitone (a σ)) (h0 : ∀ σ, a σ (r σ) = 0) :
    RowDeg r n k a (minorsP r n col k a) := by
  classical
  intro m hm σ i
  let w : (Σ σ, Fin (r σ)) → ℕ := fun ℓ => if ℓ = ⟨σ, i⟩ then 1 else 0
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) Finset.univ _ _
    fun σ' _ => IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) Finset.univ _ _
      fun (s : Fin (r σ')) _ => (minor_weighted r n k col w σ' s).pow (a σ' s - a σ' (s + 1))
  have h1 := h (mem_support_iff.1 hm)
  have hL : Finsupp.weight (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
      Finset.sum_eq_single σ, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp [w]
    · intro j _ hj
      simp [w, hj]
    · simp
    · intro σ' _ hσ
      simp [w, hσ]
    · simp
  rw [← hL, h1, Finset.sum_eq_single σ]
  · have e : ∀ s : Fin (r σ), (a σ s - a σ (s + 1)) • ∑ j : Fin (s + 1), w ⟨σ, Fin.castLE s.isLt j⟩ =
        if (i : ℕ) ≤ s then a σ s - a σ (s + 1) else 0 := by
      intro s
      split_ifs with his
      · rw [Finset.sum_eq_single ⟨i, Nat.lt_succ_of_le his⟩]
        · simp [w]
        · intro j _ hj
          simp only [w]
          rw [ite_eq_right]
          intro e
          have e' : Fin.castLE s.isLt j = i := eq_of_heq (Sigma.mk.inj_iff.1 e).2
          exact hj (Fin.ext (congrArg Fin.val e' :))
        · simp
      · rw [Finset.sum_eq_zero, smul_zero]
        intro j _
        simp only [w]
        rw [ite_eq_right]
        intro e
        have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.1 e).2)
        have := j.isLt
        simp only [Fin.val_castLE] at *
        omega
    rw [Finset.sum_congr rfl fun s _ => e s,
      Fin.sum_univ_eq_sum_range (fun s => if (i : ℕ) ≤ s then a σ s - a σ (s + 1) else 0),
      ThetaClaimsCompare.gaps_sum _ (ha σ) _ _ i.isLt.le, h0, Nat.sub_zero]
  · intro σ' _ hσ
    simp [w, hσ]
  · simp

end Minors

end GlobalTheory.BlockProdEx
