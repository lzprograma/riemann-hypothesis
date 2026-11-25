module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IKDiscrete
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Lemma
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofTorMkCIsQuotientMap

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem z_eq_inner {ι : Type} [Fintype ι] (K : Submodule ℝ (EuclideanSpace ℂ ι)) (k : Fin (dK K))
    (v : EuclideanSpace ℂ ι) : z K k v = innerSL ℂ (e K k) v := by
  unfold z e Hf
  rw [innerSL_apply_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply]

theorem zmG_differentiable {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    Differentiable ℂ (zmG I s) := by
  unfold zmG
  have hs' : Differentiable ℂ s := (show Differentiable ℂ s ∧ _ from hs).1
  have h1 : Differentiable ℂ fun v : Vsp X.dim => s fun _ => v :=
    hs'.comp (differentiable_pi.2 fun _ => differentiable_id)
  refine h1.mul (Differentiable.cexp (Differentiable.const_mul ?_ _))
  unfold S
  have hz : ∀ k, Differentiable ℂ fun v : Vsp X.dim => z (IR I) k v ^ 2 := by
    intro k
    refine Differentiable.pow ?_ 2
    have hk : z (IR I) k = ⇑(innerSL ℂ (e (IR I) k)) :=
      funext fun v => z_eq_inner _ _ _
    rw [hk]
    exact (innerSL ℂ (e (IR I) k)).differentiable
  first
    | exact Differentiable.fun_sum fun k _ => hz k

theorem zmG_continuous {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    Continuous (zmG I s) := (zmG_differentiable hs).continuous

def tb (hI : IsSplit P I) (t : Fin (Module.finrank ℝ (IR I)) → ℝ) : Vsp X.dim :=
  ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim)

theorem tb_mem (hI : IsSplit P I) (t : Fin (Module.finrank ℝ (IR I)) → ℝ) : tb hI t ∈ IR I :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Ib hI i).2

theorem tb_add (hI : IsSplit P I) (t t' : Fin (Module.finrank ℝ (IR I)) → ℝ) :
    tb hI (t + t') = tb hI t + tb hI t' := by
  simp only [tb, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem tb_int (hI : IsSplit P I) (n : Fin (Module.finrank ℝ (IR I)) → ℤ) :
    tb hI (fun i => (n i : ℝ)) ∈ I := by
  unfold tb
  refine Submodule.sum_mem _ fun i _ => ?_
  have hK : (Ib hI i : IR I) ∈ IK I := by
    simp only [Ib, Module.Basis.reindex_apply, Module.Basis.ofZLatticeBasis_apply]
    exact SetLike.coe_mem _
  have hmem : ((Ib hI i : IR I) : Vsp X.dim) ∈ I := hK
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ hmem

theorem zmC_eq (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) (n) (v : Vsp X.dim) :
    zmC hI s n v = ∫ t in zmBox (Module.finrank ℝ (IR I)),
      Complex.exp (-(2 * Real.pi * Complex.I * ∑ i, (n i : ℂ) * (t i : ℂ))) * zmG I s (v + tb hI t) := rfl

theorem fib_continuous (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) : Continuous fun t : Fin (Module.finrank ℝ (IR I)) → ℝ => zmG I s (v + tb hI t) := by
  refine (zmG_continuous hs).comp (continuous_const.add ?_)
  unfold tb
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

private lemma Hf_eq_inner_swap {ι : Type} [Fintype ι] (x y : EuclideanSpace ℂ ι) : Hf y x = inner ℂ x y := by
  unfold Hf
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply]

private lemma zmG_add_mem_of_isSplit (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (w γ : Vsp X.dim) (hγI : γ ∈ I) : zmG I s (w + γ) = zmG I s w := by
  have hγR : γ ∈ IR I := Submodule.subset_span hγI
  have hreal : ∀ x ∈ IR I, ∀ y ∈ IR I, (inner ℂ x y).im = 0 := fun x hx y hy => by
    rw [← Hf_eq_inner_swap]
    exact Hf_im_span_iso (I : Set (Vsp X.dim)) hI.iso y hy x hx
  have hz : ∀ k u, z (IR I) k u = inner ℂ (e (IR I) k) u := by
    intro k u
    rw [z_eq_inner, innerSL_apply_apply]
  have hzadd : ∀ k (u u' : Vsp X.dim), z (IR I) k (u + u') = z (IR I) k u + z (IR I) k u' := by
    intro k u u'
    rw [hz, hz, hz, inner_add_right]
  let b := stdOrthonormalBasis ℝ (IR I)
  have heb : ∀ k : Fin (dK (IR I)), e (IR I) k = ((b k : IR I) : Vsp X.dim) := fun k => rfl
  have he_mem : ∀ k : Fin (dK (IR I)), e (IR I) k ∈ IR I := fun k => (b k).2
  obtain ⟨γ', hγ'⟩ : ∃ γ' : IR I, (γ' : Vsp X.dim) = γ := ⟨⟨γ, hγR⟩, rfl⟩
  have hexp : γ = ∑ k : Fin (dK (IR I)), (b.repr γ' k) • ((b k : IR I) : Vsp X.dim) := by
    have h := congrArg (fun x : IR I => (x : Vsp X.dim)) (b.sum_repr γ')
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← hγ', ← h]
  have hzγ : ∀ k : Fin (dK (IR I)), z (IR I) k γ = ((b.repr γ' k : ℝ) : ℂ) := by
    intro k
    rw [hz]
    apply Complex.ext
    · rw [Complex.ofReal_re, OrthonormalBasis.repr_apply_apply, ← hγ', Submodule.coe_inner, heb,
        real_inner_eq_Hf, Hf_eq_inner_swap]
    · rw [Complex.ofReal_im]
      exact hreal _ (he_mem k) _ hγR
  have hstar : ∀ u : Vsp X.dim, ∑ k : Fin (dK (IR I)), z (IR I) k u * z (IR I) k γ = Hf u γ := by
    intro u
    rw [Hf_eq_inner_swap]
    conv_rhs => rw [hexp]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    first
      | (rw [hzγ, hz, heb, ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, mul_comm])
  have hS : ∀ u : Vsp X.dim, S (IR I) (u + γ) = S (IR I) u + 2 * Hf u γ + Hf γ γ := by
    intro u
    unfold S
    rw [← hstar u, ← hstar γ, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hzadd]
    ring
  have hHC : ∀ a c : Vsp X.dim, HC (fun _ : Fin 1 => a) (fun _ => c) = Hf a c := by
    intro a c
    unfold HC Hf
    simp
  have hsec : s (fun _ => w + γ) =
      Complex.exp (↑Real.pi * Hf w γ + ↑Real.pi * Hf γ γ / 2) * s (fun _ => w) := by
    have h := (show Differentiable ℂ s ∧ _ from hs).2 (fun _ => γ) (fun _ => hI.le hγI) (fun _ => w)
    simpa [hHC, hI.eps γ hγI, Pi.add_def] using h
  unfold zmG
  rw [hsec, hS w]
  rw [show ∀ (a c d : ℂ), Complex.exp a * c * Complex.exp d = c * Complex.exp (a + d) from
    fun a c d => by rw [Complex.exp_add]; ring]
  congr 2
  ring

theorem fib_periodic (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) (t : Fin (Module.finrank ℝ (IR I)) → ℝ) (n : Fin (Module.finrank ℝ (IR I)) → ℤ) :
    zmG I s (v + tb hI (t + fun i => (n i : ℝ))) = zmG I s (v + tb hI t) := by
  rw [tb_add, ← add_assoc]
  exact zmG_add_mem_of_isSplit hI hs _ _ (tb_int hI n)

theorem zeroMode_add_realSpan (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    (v : Vsp X.dim) {a : Vsp X.dim} (ha : a ∈ IR I) : zmC hI s 0 (v + a) = zmC hI s 0 v := by
  set c := (Ib hI).repr ⟨a, ha⟩ with hc
  have hac : a = tb hI (fun i => c i) := by
    have h := congrArg Subtype.val ((Ib hI).sum_repr ⟨a, ha⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [tb]; exact h.symm
  simp only [zmC_eq, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, mul_zero,
    neg_zero, Complex.exp_zero, one_mul]
  have hsh := tof_box_shift (fun t => zmG I s (v + tb hI t)) (fib_continuous hI hs v)
    (fun t n => fib_periodic hI hs v t n) (fun i => c i)
  rw [zmBox]
  rw [← hsh]
  congr 1
  funext t
  rw [hac, add_assoc, ← tb_add, add_comm t]

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
