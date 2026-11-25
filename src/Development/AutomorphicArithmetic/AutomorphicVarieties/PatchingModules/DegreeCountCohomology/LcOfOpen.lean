module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Linter.Style
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem lc_of_open {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ))
    (h : ∀ m, IsLocallyConstant fun g : H => ρ g m) : LC ρ := by
  intro m
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hU : IsOpen ((Subtype.val : H → Γ) '' {z : H | ρ z m = m}) :=
    hH.isOpenMap_subtype_val _ ((h m).isOpen_fiber m)
  have h1 : (1 : Γ) ∈ (Subtype.val : H → Γ) '' {z : H | ρ z m = m} := ⟨1, by simp, rfl⟩
  have ht : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) := by
    have h0 := (continuous_const_mul x⁻¹).tendsto x
    simpa using h0
  filter_upwards [ht (hU.mem_nhds h1)] with y hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hz' : ρ z m = m := hz
  have hy : y = x * z := by rw [hzy]; group
  rw [hy, map_mul]
  show ρ x (ρ z m) = ρ x m
  rw [hz']

private theorem lc_padic {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R) (hl : (l : R) = 0) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ᶠ y in nhds x, ‖y - x‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    simpa [dist_eq_norm] using hy
  filter_upwards [hev] with y hy
  obtain ⟨z, hz⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hy
  have hyz : y = x + (l : ℤ_[l]) * z := by rw [← hz]; ring
  rw [hyz, map_add (f := _), map_mul, map_natCast, hl, zero_mul, add_zero]

private theorem isLocallyConstant_comp_of_adicCont_of_pow_eq_zero {Γ A B : Type} [TopologicalSpace Γ] [CommRing A] [CommRing B] (s : A) (N : ℕ)
    (φ : A →+* B) (hs : φ s ^ N = 0) (f : Γ → A) (hf : AdicCont (Ideal.span {s}) f) :
    IsLocallyConstant fun g => φ (f g) := by
  have hI : ∀ a ∈ Ideal.span {s} ^ N, φ a = 0 := by
    intro a ha
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_pow, hs, mul_zero]
  have h2 := (hf N).comp (Ideal.Quotient.lift (Ideal.span {s} ^ N) φ hI)
  convert h2 using 1
  funext g
  exact (Ideal.Quotient.lift_mk (Ideal.span {s} ^ N) φ hI).symm

theorem UpperTheory.V.Pa.lc1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ), (IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g)) ∧ (IsLocallyConstant fun g : G.Γ => epsD k (x.Am m) (h.p g)) ∧ ∀ (χ : G.Γ → DD (x.Am m) k.g) (V : Submodule x.A (Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))) (rep : Representation x.A G.Γ V), IsLocallyConstant χ → IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) χ V rep → LC rep := by
  intro l _ L G G0 h n x k m
  obtain ⟨-, -, -, -, hlD, htA, htD, -, -⟩ := finAm l G0.frame n x m k.g
  have hp0 : Continuous h.p₀ := continuous_induced_rng.2 (h.cont.comp continuous_subtype_val)
  have hE : IsLocallyConstant fun g : G0.G₀ =>
      DD.epM (fun j => (k.κ j g).map (algebraMap x.A (x.Am m))) :=
    (LocallyConstant.unflip fun a => LocallyConstant.unflip fun b =>
      (LocallyConstant.unflip fun j =>
        ⟨_, isLocallyConstant_comp_of_adicCont_of_pow_eq_zero (algebraMap x.A x.A x.t) m
          (algebraMap x.A (x.Am m)) (by simpa using htA) _ ((k.mem j).2.1 a b)⟩).map
        fun v => ({ a := 0, ep := v, ep' := 0, eta := 0 } : DD (x.Am m) k.g)).isLocallyConstant
  have hR : IsLocallyConstant fun g : G0.G₀ => x.ρX (DD (x.Am m) k.g) g :=
    (LocallyConstant.unflip fun a => LocallyConstant.unflip fun b =>
      ⟨_, isLocallyConstant_comp_of_adicCont_of_pow_eq_zero x.t m
        (algebraMap x.A (DD (x.Am m) k.g)) htD _
        (PowerSeries.maximalIdeal_eq_span_X (k := x.K) ▸ x.cont a b)⟩).isLocallyConstant
  have hρ : IsLocallyConstant fun g : G0.G₀ => k.ρ1 (x.Am m) g :=
    (hE.comp (fun M => 1 + M)).comp₂ hR (· * ·)
  have hρ' : IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g) := hρ.comp_continuous hp0
  refine ⟨hρ', ?_, ?_⟩
  · have hl' : ((l : ℕ) : DD (x.Am m) k.g) = 0 := by simpa using hlD 1
    exact (lc_padic ((algebraMap x.A (DD (x.Am m) k.g)).comp (algebraMap ℤ_[l] x.A)) hl').comp_continuous
      (Units.continuous_val.comp (G0.ε_cont.comp h.cont))
  · intro χ V rep hχ hAd
    apply lc_of_open rep G.η.ker G.η_open
    intro Z
    have hinv : IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g⁻¹) :=
      hρ'.comp_continuous continuous_inv
    have hχ' : IsLocallyConstant fun g : G.G₀ => χ g := hχ.comp_continuous continuous_subtype_val
    have key : IsLocallyConstant fun g : G.G₀ => ((rep g Z : V) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) := by
      have e : (fun g : G.G₀ => ((rep g Z : V) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))) =
          fun g : G.G₀ => χ g • (k.ρ1 (x.Am m) (h.p₀ g) * (Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) *
            k.ρ1 (x.Am m) (h.p₀ g⁻¹)) := by
        funext g
        exact hAd.1 g Z
      rw [e]
      exact hχ'.comp₂ (hρ'.comp₂ hinv fun A B => A * (Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * B)
        fun c M => c • M
    exact (IsLocallyConstant.iff_eventually_eq _).2 fun g =>
      (key.eventually_eq g).mono fun y hy => Subtype.ext hy
