module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.ObjModel
variable {E : Type} [Field E] [NumberField E]

theorem coord_ne (y : (Af E)ˣ) (v : HeightOneSpectrum (𝓞 E)) : Valued.v ((y : Af E) v) ≠ 0 := by
  exact GlobalTheory.CMVal.IdeleModule.coord_ne y v

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  exact GlobalTheory.CMVal.IdeleModule.absNorm_pos v

theorem modF_mul (y y' : (Af E)ˣ) : modF (y * y') = modF y * modF y' := by
  exact GlobalTheory.CMVal.IdeleModule.modF_mul y y'

theorem modF_pos (y : (Af E)ˣ) : 0 < modF y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (absNorm_pos v) _

theorem modF_princ (k : Eˣ) :
    modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|((Algebra.norm ℚ (k : E) : ℚ) : ℝ)|)⁻¹ := by
  apply _root_.GlobalTheory.CMVal.IdeleModule.modF_princ

theorem hatO_integral {c : Ideal (OF E)} {y : Af E} (hy : y ∈ hatO c) (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v (y v) ≤ 1 := by
  have hc : IsClosed {y : Af E | y v ∈ v.adicCompletionIntegers E} :=
    (Valued.isClosed_valuationSubring (v.adicCompletion E)).preimage (RestrictedProduct.continuous_eval v)
  have : y ∈ {y : Af E | y v ∈ v.adicCompletionIntegers E} := by
    refine closure_minimal ?_ hc hy
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
    have : algebraMap (OF E) E a + algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by
      rw [map_add (f := _)]; rfl
    rw [this]
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one _)
  exact this

theorem modF_unit {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) : modF u = 1 := by
  unfold modF
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  have h1 : Valued.v ((u : Af E) v) ≤ 1 := hatO_integral hu.1 v
  have h2 : Valued.v ((↑u⁻¹ : Af E) v) ≤ 1 := hatO_integral hu.2 v
  have h3 : Valued.v ((u : Af E) v) * Valued.v ((↑u⁻¹ : Af E) v) = 1 := by
    rw [← map_mul]
    have : (u : Af E) v * (↑u⁻¹ : Af E) v = 1 := (coord v u).val_inv
    rw [this, map_one]
  have h4 : Valued.v ((u : Af E) v) = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ Valued.v ((u : Af E) v) * 1 := by gcongr
      _ = _ := mul_one _
  simp [h4]

variable {I : Type}

theorem prod_normSq [Fintype I] [_root_.NumberField.IsTotallyComplex E] {φ : I → E →+* ℂ}
    (h : IsCMType φ) (x : E) :
    ∏ i, ‖φ i x‖ ^ 2 = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h1 := InfinitePlace.prod_eq_abs_norm x
  push_cast at h1
  rw [← h1]
  refine Fintype.prod_bijective (fun i => InfinitePlace.mk (φ i)) ⟨fun i j hij => ?_, fun w => ?_⟩ _ _ fun i => ?_
  · obtain ⟨l, -, hl⟩ := h (φ i)
    have h2 := InfinitePlace.mk_eq_iff.1 hij.symm
    rw [hl i (Or.inl rfl), hl j (h2.imp Eq.symm Eq.symm)]
  · obtain ⟨l, hl, -⟩ := h w.embedding
    refine ⟨l, ?_⟩
    rw [← w.mk_embedding]
    exact InfinitePlace.mk_eq_iff.2 (hl.imp Eq.symm Eq.symm)
  · rw [IsTotallyComplex.mult_eq, InfinitePlace.apply]

theorem prod_cpow (t : Finset I) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) (z : ℂ) :
    ∏ i ∈ t, ((r i : ℝ) : ℂ) ^ z = ((∏ i ∈ t, r i : ℝ) : ℂ) ^ z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hr a) (Finset.prod_nonneg fun i _ => hr i)]

end GlobalTheory.CMVal.ObjModel
