module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric MeasureTheory
open scoped Pointwise

instance instHaarMat (N N' : ℕ) : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

instance instHaarVC (D : D7) (N N' : ℕ) : (volume : Measure (VC D N N')).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

variable {D : D7} {N N' : ℕ}

private def sS (z w : VC D N N') : ℂ := ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)

private theorem Hf_eq (T : Tor D) (z w : VC D N N') : Hf D T z w = sS z w / (area T.abelian₂ : ℂ) := rfl

private theorem sS_swap (z w : VC D N N') : sS w z = (starRingEnd ℂ) (sS z w) := by

  simp only [sS, map_sum, map_mul, starRingEnd_self_apply]
  exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem sS_add (z x : VC D N N') :
    sS (z + x) (z + x) = sS z z + sS z x + sS x z + sS x x := by
  simp only [sS, Pi.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib]
  ring

private theorem re_Hf_add (T : Tor D) (z x : VC D N N') :
    (Hf D T (z + x) (z + x)).re =
      (Hf D T z z).re + 2 * (Hf D T z x).re + (Hf D T x x).re := by
  rw [Hf_eq, Hf_eq, Hf_eq, Hf_eq, sS_add, sS_swap z x]
  simp only [Complex.div_ofReal_re, Complex.add_re, Complex.conj_re]
  ring

def dens (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) (z : VC D N N') : ℝ :=
  ‖G z‖ ^ 2 * Real.exp (-Real.pi * (Hf D T z z).re)

theorem dens_U (T : Tor D) (G : VC D N N' → ℂ) (x z : VC D N N') :
    dens D T (U D T x G) z = dens D T G (z + x) := by
  have h := re_Hf_add T z x
  simp only [dens, U, norm_mul, Complex.norm_exp, mul_pow]
  rw [h, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  congr 1
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_ofNat_re, zero_mul, sub_zero, Complex.neg_im, neg_zero]
  push_cast
  ring

theorem norm_al (T : Tor D) (x : VC D N N') : ‖al D T x‖ = 1 := by
  simp [al, norm_zpow]

theorem dens_periodic (T : Tor D) (La' : AddSubgroup (VC D N N')) (G : VC D N N' → ℂ)
    (hG : G ∈ ThSp D T La') (y : VC D N N') (hy : y ∈ La') (z : VC D N N') :
    dens D T G (z + y) = dens D T G z := by
  rw [← dens_U]
  simp only [dens]
  rw [← hG.2 y hy z, norm_mul, norm_al, one_mul]

theorem normSq_U_of_fd (T : Tor D) (La' : AddSubgroup (VC D N N')) [Countable La']
    (hfd : ∃ Fd : Set (VC D N N'), IsAddFundamentalDomain La' Fd volume)
    (G : VC D N N' → ℂ) (hG : G ∈ ThSp D T La') (x : VC D N N') :
    normSq D T La' (U D T x G) = normSq D T La' G := by
  have : (volume : Measure (VC D N N')).IsAddLeftInvariant :=
    (instHaarVC D N N').toIsAddLeftInvariant
  have : VAddInvariantMeasure (VC D N N') (VC D N N') volume :=
    Measure.IsAddLeftInvariant.vaddInvariantMeasure
  have hF := Classical.epsilon_spec hfd
  show (⨍ z in _, dens D T (U D T x G) z) = ⨍ z in _, dens D T G z
  simp_rw [dens_U]
  set F := Classical.epsilon fun Fd : Set (VC D N N') => IsAddFundamentalDomain La' Fd volume
  have hper : ∀ (g : La') (z : VC D N N'), dens D T G ((g +ᵥ z) + x) = dens D T G (z + x) := by
    intro g z
    show dens D T G ((g : VC D N N') + z + x) = dens D T G (z + x)
    rw [show (g : VC D N N') + z + x = z + x + g by abel]
    exact dens_periodic T La' G hG g g.2 (z + x)
  have h1 : ∫ z in F, dens D T G (z + x) = ∫ z in (-x) +ᵥ F, dens D T G (z + x) :=
    hF.setIntegral_eq (hF.vadd_of_comm (-x)) hper
  have h2 : ∫ z in (-x) +ᵥ F, dens D T G (z + x) = ∫ z in F, dens D T G z := by
    rw [← Set.preimage_vadd]
    simp_rw [add_comm _ x]
    exact (measurePreserving_vadd x volume).setIntegral_preimage_emb
      (MeasurableEquiv.vadd x).measurableEmbedding (dens D T G) F
  rw [setAverage_eq, setAverage_eq, h1, h2]

def FullLat {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (La' : AddSubgroup V) : Prop :=
  DiscreteTopology La' ∧ Submodule.span ℝ (La' : Set V) = ⊤

theorem normSq_U_of_full (T : Tor D) (La' : AddSubgroup (VC D N N')) (hL : FullLat La')
    (G : VC D N N' → ℂ) (hG : G ∈ ThSp D T La') (x : VC D N N') :
    normSq D T La' (U D T x G) = normSq D T La' G := by
  obtain ⟨hd, hs⟩ := hL
  haveI := hd
  haveI : Countable La' := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : DiscreteTopology (AddSubgroup.toIntSubmodule La') := hd
  haveI : IsZLattice ℝ (AddSubgroup.toIntSubmodule La') := ⟨hs⟩
  refine normSq_U_of_fd T La' ⟨_, ZLattice.isAddFundamentalDomain
    (Module.Free.chooseBasis ℤ (AddSubgroup.toIntSubmodule La')) volume⟩ G hG x

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

theorem galE_sigmaOf (g : D.R.GG) :
    D.host.galE (D.host.sigmaOf g) = g := by
  exact D.host.gal.apply_symm_apply g

theorem embT_K (τ : D.what₂.Tau) (x : D.host.E) (hx : x ∈ D.host.K) :
    embT D τ x = D.host.φ₀ x :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.embT_K (Formalism.L2.Ker.Car.ofRec D) τ x hx

theorem emb_cases (φ : D.host.E →+* ℂ) :
    ∃ τ : D.what₂.Tau, φ = embT D τ ∨ φ = (starRingEnd ℂ).comp (embT D τ) :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.emb_cases (Formalism.L2.Ker.Car.ofRec D) φ

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

def embP (x : D.host.E) : D.what₂.Tau → ℂ := fun τ => embT D τ x

theorem card_tau : Fintype.card D.what₂.Tau = 2 * D.R.ord := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr D.eTau, Formalism.HC.Frame.natCard_Psi]

theorem span_embP :
    Submodule.span ℝ (Set.range (fun b : 𝓞 D.host.E => embP D (b : D.host.E))) = ⊤ :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.span_embP (Formalism.L2.Ker.Car.ofRec D)

theorem finite_ball (r : ℝ) : {x : 𝓞 D.host.E | ∀ τ, ‖embT D τ (x : D.host.E)‖ ≤ r}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le D.host.E ℂ r
  refine Set.Finite.of_finite_image (hfin.subset ?_)
    NumberField.RingOfIntegers.coe_injective.injOn
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨NumberField.RingOfIntegers.isIntegral_coe x, fun φ => ?_⟩
  obtain ⟨τ, rfl | rfl⟩ := emb_cases D φ
  · exact hx τ
  · simpa using hx τ

theorem finite_mat (N N' : ℕ) (r : ℝ) :
    {A : Fin N' → Fin N → 𝓞 D.host.E | ∀ τ i j, ‖embT D τ (A i j : D.host.E)‖ ≤ r}.Finite := by
  have hF := finite_ball D r
  have h2 : {A : Fin N' → Fin N → 𝓞 D.host.E | ∀ τ i j, ‖embT D τ (A i j : D.host.E)‖ ≤ r} =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
        {x : 𝓞 D.host.E | ∀ τ, ‖embT D τ (x : D.host.E)‖ ≤ r} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_pi]
    exact ⟨fun h i _ j _ τ => h τ i j, fun h τ i j => h i (Set.mem_univ _) j (Set.mem_univ _) τ⟩
  rw [h2]
  exact Set.Finite.pi fun _ => Set.Finite.pi fun _ => hF

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

theorem natMul_of (b : 𝓞 D.host.E) (hb : b ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ t : 𝓞 D.host.E, (n : 𝓞 D.host.E) = t * b :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.natMul_of (Formalism.L2.Ker.Car.ofRec D) b hb

theorem exists_int_mul (T : Finset D.host.E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ T, IsIntegral ℤ ((m : D.host.E) * x) :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.exists_int_mul (Formalism.L2.Ker.Car.ofRec D) T

theorem one_mem_inverse_halfDifferent : (1 : D.host.E) ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.one_mem_inverse_halfDifferent (Formalism.L2.Ker.Car.ofRec D)

theorem exists_int_clearing_order_denominators : ∃ k : ℤ, k ≠ 0 ∧ ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
    IsIntegral ℤ ((k : D.host.E) * a) :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.exists_int_clearing_order_denominators (Formalism.L2.Ker.Car.ofRec D)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits MeasureTheory

variable (D : D7)

theorem YY_lower {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L') :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, IsIntegral ℤ (A i j)) →
      ((M : D.host.E) • A) ∈ YYl D L L' :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.YY_lower (Formalism.L2.Ker.Car.ofRec D) L L' hL hL'

theorem intK (c : 𝓞 D.host.K) : IsIntegral ℤ (((c : D.host.K) : D.host.E)) := by
  exact IsIntegral.algebraMap (B := D.host.E) (NumberField.RingOfIntegers.isIntegral_coe c)

theorem lam_mem (cc : Ideal (𝓞 D.host.K)) (δ w : ℂ) (hw : w ∈ lamOf D cc δ) :
    ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.lam_mem (Formalism.L2.Ker.Car.ofRec D) cc δ w hw

def Phi {N N' : ℕ} (u : ℂ) : (Fin N' → Fin N → 𝓞 D.host.E) →+ VC D N N' where
  toFun A := fun τ i j => u * embT D τ (A i j : D.host.E)
  map_zero' := by funext τ i j; simp
  map_add' A B := by funext τ i j; simp [mul_add]

theorem La_upper {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∃ M : ℤ, M ≠ 0 ∧ La D (tor0 D cc δ) L L' ≤ (Phi D (N := N) (N' := N') (δ / M)).range :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.La_upper (Formalism.L2.Ker.Car.ofRec D) L L' hA cc δ

theorem disc_of_finite {V : Type*} [NormedAddCommGroup V] (S : AddSubgroup V)
    (h : ∀ r : ℝ, {x | x ∈ S ∧ ‖x‖ ≤ r}.Finite) : DiscreteTopology S := by
  apply discreteTopology_of_isOpen_singleton_zero
  have hT : (({x | x ∈ S ∧ ‖x‖ ≤ 1} : Set V) \ {0}).Finite := (h 1).subset fun x hx => hx.1
  refine isOpen_induced_iff.2 ⟨Metric.ball (0 : V) 1 ∩ (({x | x ∈ S ∧ ‖x‖ ≤ 1} : Set V) \ {0})ᶜ,
    Metric.isOpen_ball.inter hT.isClosed.isOpen_compl, ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
    Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    exact h2 ⟨⟨y.2, h1.le⟩, fun h0 => hne (Subtype.ext h0)⟩
  · rintro rfl
    simp

theorem La_finite {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hδ : δ ≠ 0) (r : ℝ) :
    {x | x ∈ La D (tor0 D cc δ) L L' ∧ ‖x‖ ≤ r}.Finite := by
  obtain ⟨M, hM, hle⟩ := La_upper D L L' hA cc δ
  have hu : (δ / M : ℂ) ≠ 0 := div_ne_zero hδ (by exact_mod_cast hM)
  refine ((finite_mat D N N' (r / ‖(δ / M : ℂ)‖)).image
    (Phi D (N := N) (N' := N') (δ / M))).subset ?_
  rintro x ⟨hx, hxr⟩
  obtain ⟨A, rfl⟩ := hle hx
  refine ⟨A, fun τ i j => ?_, rfl⟩
  have h2 : ‖Phi D (N := N) (N' := N') (δ / M) A τ i j‖ ≤ r :=
    ((norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans (norm_le_pi_norm _ τ))).trans hxr
  change ‖(δ / M : ℂ) * embT D τ (A i j : D.host.E)‖ ≤ r at h2
  rw [norm_mul] at h2
  rw [le_div_iff₀ (norm_pos_iff.2 hu), mul_comm]
  exact h2

def ins {N N' : ℕ} (i0 : Fin N') (j0 : Fin N) (w : D.what₂.Tau → ℂ) : VC D N N' :=
  fun τ i j => if i = i0 ∧ j = j0 then w τ else 0

theorem La_lower {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ (i0 : Fin N') (j0 : Fin N) (b : 𝓞 D.host.E),
      ins D i0 j0 (fun τ => δ * n * embT D τ (b : D.host.E)) ∈ La D (tor0 D cc δ) L L' :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL.La_lower (Formalism.L2.Ker.Car.ofRec D) L L' hA cc hcc δ

theorem span_La {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) (hδ : δ ≠ 0) :
    Submodule.span ℝ (La D (tor0 D cc δ) L L' : Set (VC D N N')) = ⊤ := by
  obtain ⟨n, hn, hmem⟩ := La_lower D L L' hA cc hcc δ
  have hc : (δ * n : ℂ) ≠ 0 := mul_ne_zero hδ (by exact_mod_cast hn)
  have key : ∀ (i0 : Fin N') (j0 : Fin N) (w : D.what₂.Tau → ℂ),
      ins D i0 j0 w ∈ Submodule.span ℝ (La D (tor0 D cc δ) L L' : Set (VC D N N')) := by
    intro i0 j0 w
    let Ψ : (D.what₂.Tau → ℂ) →ₗ[ℝ] VC D N N' :=
      { toFun := fun u => ins D i0 j0 (fun τ => δ * n * u τ)
        map_add' := fun u u' => by
          funext τ i j
          simp only [ins, Pi.add_apply]
          split_ifs <;> ring
        map_smul' := fun c u => by
          funext τ i j
          simp only [ins, Pi.smul_apply, RingHom.id_apply]
          split_ifs <;> simp [Complex.real_smul] <;> ring }
    have h1 : Submodule.map Ψ (Submodule.span ℝ
        (Set.range fun b : 𝓞 D.host.E => embP D (b : D.host.E))) ≤
        Submodule.span ℝ (La D (tor0 D cc δ) L L' : Set (VC D N N')) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
      exact hmem i0 j0 b
    have hw : (fun τ => (δ * n)⁻¹ * w τ) ∈ Submodule.span ℝ
        (Set.range fun b : 𝓞 D.host.E => embP D (b : D.host.E)) := by
      rw [span_embP D]
      exact Submodule.mem_top
    have h2 := h1 (Submodule.mem_map_of_mem hw)
    have h3 : Ψ (fun τ => (δ * n)⁻¹ * w τ) = ins D i0 j0 w := by
      show ins D i0 j0 (fun τ => δ * n * ((δ * n)⁻¹ * w τ)) = ins D i0 j0 w
      simp only [mul_inv_cancel_left₀ hc]
    rwa [h3] at h2
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ i0, ∑ j0, ins D i0 j0 (fun τ => v τ i0 j0) := by
    funext τ i j
    simp only [Finset.sum_apply]
    rw [Fintype.sum_eq_single i, Fintype.sum_eq_single j]
    · simp [ins]
    · intro j0 hj
      simp [ins, Ne.symm hj]
    · intro i0 hi
      exact Finset.sum_eq_zero fun j0 _ => by simp [ins, Ne.symm hi]
  rw [hv]
  exact Submodule.sum_mem _ fun i0 _ => Submodule.sum_mem _ fun j0 _ => key i0 j0 _

theorem fullLat {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) (hδ : δ ≠ 0) :
    FullLat (La D (tor0 D cc δ) L L') := by
  exact ⟨disc_of_finite _ (La_finite D L L' hA cc δ hδ), span_La D L L' hA cc hcc δ hδ⟩

theorem La_zero {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (cc : Ideal (𝓞 D.host.K)) :
    La D (tor0 D cc 0) L L' = ⊥ := by
  rw [eq_bot_iff]
  show AddSubgroup.closure _ ≤ ⊥
  rw [AddSubgroup.closure_le]
  rintro z ⟨w, hw, A, -, rfl⟩
  obtain ⟨c, -, rfl⟩ := lam_mem D cc 0 w hw
  simp

theorem fd_bot {V : Type*} [AddGroup V] [MeasurableSpace V] (μ : Measure V) :
    IsAddFundamentalDomain (⊥ : AddSubgroup V) Set.univ μ := by
  refine ⟨nullMeasurableSet_univ, Filter.Eventually.of_forall fun _ => ⟨0, Set.mem_univ _⟩, ?_⟩
  intro a b hab
  exact absurd (Subtype.ext ((AddSubgroup.mem_bot.mp a.2).trans
    (AddSubgroup.mem_bot.mp b.2).symm)) hab

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric MeasureTheory

theorem theta_unitary_linkage : LinkThU := by
  intro D cc hcc δ hδ N N' L L' hA G hG x
  by_cases h0 : δ = 0
  · subst h0
    have hc : Countable (La D (tor0 D cc 0) L L') := by
      rw [FL.La_zero D L L' cc]
      exact Function.Injective.countable (f := fun _ => (0 : ℕ)) fun a b _ =>
        Subtype.ext ((AddSubgroup.mem_bot.1 a.2).trans (AddSubgroup.mem_bot.1 b.2).symm)
    exact normSq_U_of_fd (tor0 D cc 0) _
      ⟨Set.univ, by rw [FL.La_zero D L L' cc]; exact FL.fd_bot _⟩ G hG x
  · exact normSq_U_of_full (tor0 D cc δ) _ (FL.fullLat D L L' hA cc hcc δ h0) G hG x

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
