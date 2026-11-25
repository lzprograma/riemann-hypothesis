module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

namespace PI.VolStabSW

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Res

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

abbrev iO (a : 𝓞 F) : Fv F v := algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)

theorem vcoe (x : F) : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem v_iO_le (a : 𝓞 F) : Valued.v (iO v a) ≤ 1 := by
  show Valued.v (algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)) ≤ 1
  rw [vcoe]
  exact v.valuation_le_one a

theorem v_iO_lt_iff (a : 𝓞 F) : Valued.v (iO v a) < 1 ↔ a ∈ v.asIdeal := by
  show Valued.v (algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)) < 1 ↔ _
  rw [vcoe]
  exact v.valuation_lt_one_iff_mem a

private theorem appr_unit_lemma (m c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ a : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c -
      algebraMap (𝓞 F) F a) < 1 := by
  obtain ⟨c', hc'⟩ : ∃ c' : 𝓞 F, c * c' - 1 ∈ v.asIdeal := by
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    letI := Ideal.Quotient.field v.asIdeal
    have hne : Ideal.Quotient.mk v.asIdeal c ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) (Ideal.Quotient.mk v.asIdeal c)⁻¹
    refine ⟨c', ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc', mul_inv_cancel₀ hne, map_one, sub_self]
  refine ⟨m * c', ?_⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc v.asIdeal.zero_mem
  have hcF : algebraMap (𝓞 F) F c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hc0
  have hvc : v.valuation F (algebraMap (𝓞 F) F c) = 1 :=
    le_antisymm (v.valuation_le_one c) (not_lt.mp fun h => hc ((v.valuation_lt_one_iff_mem c).mp h))
  have heq : algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c - algebraMap (𝓞 F) F (m * c') =
      algebraMap (𝓞 F) F m * algebraMap (𝓞 F) F (1 - c * c') / algebraMap (𝓞 F) F c := by
    rw [map_mul, map_sub, map_one, map_mul]
    first
      | (field_simp; ring)
      | field_simp
  have h1 : v.valuation F (algebraMap (𝓞 F) F (1 - c * c')) < 1 := by
    rw [v.valuation_lt_one_iff_mem]
    have h2 : 1 - c * c' = -(c * c' - 1) := by ring
    rw [h2]
    exact v.asIdeal.neg_mem hc'
  have hm1 := v.valuation_le_one (K := F) m
  rw [heq, map_div₀, hvc, div_one, map_mul]
  calc v.valuation F (algebraMap (𝓞 F) F m) * v.valuation F (algebraMap (𝓞 F) F (1 - c * c'))
      ≤ 1 * v.valuation F (algebraMap (𝓞 F) F (1 - c * c')) := by gcongr
    _ < 1 := by rw [one_mul]; exact h1

theorem exists_appr {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 := by
  have hx1 : Valued.v x ≤ 1 := hx
  have hnhds : {y : Fv F v | Valued.v (y - x) < 1} ∈ 𝓝 x :=
    Valued.mem_nhds.mpr ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨_, hy, k, rfl⟩ :=
    mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap F v x) _ hnhds
  have hy' : Valued.v (x - algebraMap F (Fv F v) k) < 1 := by
    have h := hy
    rwa [Set.mem_setOf_eq, ← neg_sub, Valuation.map_neg] at h
  have hk1 : Valued.v (algebraMap F (Fv F v) k) ≤ 1 := by
    have h := Valuation.map_add_le Valued.v (le_of_lt hy) hx1
    rwa [sub_add_cancel] at h
  rw [vcoe] at hk1
  obtain ⟨m, ⟨c, hc⟩, hmc⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v k hk1
  have hcF : algebraMap (𝓞 F) F c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr fun h => hc (h ▸ v.asIdeal.zero_mem)
  obtain rfl : k = algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c := eq_div_of_mul_eq hcF hmc
  obtain ⟨a, ha⟩ := appr_unit_lemma v m c hc
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap F (Fv F v) (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c) - iO v a) < 1 := by
    show Valued.v (algebraMap F (Fv F v) _ - algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)) < 1
    rw [← map_sub, vcoe]
    exact ha
  have h3 : x - iO v a = (x - algebraMap F (Fv F v) (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c)) +
      (algebraMap F (Fv F v) (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c) - iO v a) := by
    ring
  rw [h3]
  exact Valuation.map_add_lt Valued.v hy' h2


open Classical in
def appr (x : Fv F v) : 𝓞 F :=
  if h : ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 then h.choose else 0

theorem appr_spec {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v (x - iO v (appr v x)) < 1 := by
  have h := exists_appr v hx
  rw [appr, dite_eq_left h]
  exact h.choose_spec

def red (x : Fv F v) : 𝓞 F ⧸ v.asIdeal := Ideal.Quotient.mk _ (appr v x)

theorem red_eq_mk_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (a : 𝓞 F) :
    red v x = Ideal.Quotient.mk _ a ↔ Valued.v (x - iO v a) < 1 := by
  rw [red, Ideal.Quotient.eq, ← v_iO_lt_iff]
  have h1 := appr_spec v hx
  have e1 : iO v (appr v x - a) = (x - iO v a) + -(x - iO v (appr v x)) := by
    simp only [iO, map_sub]
    ring
  have e2 : x - iO v a = (x - iO v (appr v x)) + iO v (appr v x - a) := by
    simp only [iO, map_sub]
    ring
  constructor
  · intro h
    rw [e2]
    exact Valuation.map_add_lt _ h1 h
  · intro h
    rw [e1]
    refine Valuation.map_add_lt _ h ?_
    rw [Valuation.map_neg]
    exact h1

theorem mem_O_iO (a : 𝓞 F) : iO v a ∈ v.adicCompletionIntegers F := v_iO_le v a

theorem red_iO (a : 𝓞 F) : red v (iO v a) = Ideal.Quotient.mk _ a := (red_eq_mk_iff v (mem_O_iO v a) a).mpr (by simp)

theorem red_add {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x + y) = red v x + red v y := by
  have hxy : x + y ∈ v.adicCompletionIntegers F := add_mem hx hy
  rw [show red v x + red v y = Ideal.Quotient.mk _ (appr v x + appr v y) by simp only [red, map_add (f := _)]]
  rw [red_eq_mk_iff v hxy]
  have e : x + y - iO v (appr v x + appr v y) = (x - iO v (appr v x)) + (y - iO v (appr v y)) := by
    simp only [iO, map_add (f := _)]
    ring
  rw [e]
  exact Valuation.map_add_lt _ (appr_spec v hx) (appr_spec v hy)

theorem red_mul {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x * y) = red v x * red v y := by
  have hxy : x * y ∈ v.adicCompletionIntegers F := mul_mem hx hy
  rw [show red v x * red v y = Ideal.Quotient.mk _ (appr v x * appr v y) by simp only [red, map_mul]]
  rw [red_eq_mk_iff v hxy]
  have e : x * y - iO v (appr v x * appr v y) =
      (x - iO v (appr v x)) * y + iO v (appr v x) * (y - iO v (appr v y)) := by
    simp only [iO, map_mul]
    ring
  rw [e]
  have hy1 : Valued.v y ≤ 1 := hy
  apply Valuation.map_add_lt
  · rw [Valuation.map_mul]
    calc _ ≤ Valued.v (x - iO v (appr v x)) * 1 := by gcongr
      _ < 1 := by
        rw [mul_one]
        exact appr_spec v hx
  · rw [Valuation.map_mul]
    calc _ ≤ 1 * Valued.v (y - iO v (appr v y)) := by
          have h2 := v_iO_le v (appr v x)
          gcongr
      _ < 1 := by
        rw [one_mul]
        exact appr_spec v hy

theorem red_one : red v 1 = 1 := by
  have h : (1 : Fv F v) = iO v 1 := by simp [iO]
  rw [h, red_iO, map_one]

theorem red_eq_zero_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    red v x = 0 ↔ Valued.v x < 1 := by
  rw [← map_zero (Ideal.Quotient.mk v.asIdeal), red_eq_mk_iff v hx 0]
  simp [iO]

theorem red_zero : red v 0 = 0 := (red_eq_zero_iff v (zero_mem _)).mpr (by simp)

theorem red_surj (t : 𝓞 F ⧸ v.asIdeal) : ∃ x ∈ v.adicCompletionIntegers F, red v x = t := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  exact ⟨iO v a, mem_O_iO v a, red_iO v a⟩

end Res

end PI.VolStabSW
