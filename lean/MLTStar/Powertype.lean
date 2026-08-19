import MLTStar.Basic

/-!
# Theorems on powertypes

The conjectures `t1_basetypeUnique`, `t2_powertypeUnique`, `t3`, `t4`, `t5` and
`powertypeNotFirstOrder` of `tptp/mlt-star.p`, verified in Lean.

`t1` and `t2` had their formulae interchanged with respect to their names in
`tptp/mlt-star.p`; that has been corrected there.  Both are proved here, so the
Lean statements were unaffected either way.
-/

namespace MLTStar

universe u

variable {E : Type u} [Domain E]

/-! ## Elementary facts about Cardelli powertypes -/

theorem IsPowertypeOf.isType_left {p t : E} (h : IsPowertypeOf p t) : IsType p := h.1

/-- The base type of a powertype is itself a type: `p` has an instance, that
instance specializes `t`, and a type that is specialized has instances. -/
theorem IsPowertypeOf.isType_base {p t : E} (h : IsPowertypeOf p t) : IsType t := by
  obtain ⟨t₃, ht₃⟩ := h.1
  exact ((h.2 t₃).mp ht₃).isType_right

/-- A base type is always an instance of its own powertype, since every type
specializes itself. -/
theorem IsPowertypeOf.iof_base {p t : E} (h : IsPowertypeOf p t) : iof t p :=
  (h.2 t).mpr (Specializes.refl h.isType_base)

/-! ## The conjectures of `tptp/mlt-star.p` -/

/-- `t1_basetypeUnique`: a base type determines its Cardelli powertype
uniquely. -/
theorem t1_basetypeUnique [Extensional E] {p t : E} (h : IsPowertypeOf p t) :
    ¬ ∃ p', p' ≠ p ∧ IsPowertypeOf p' t := by
  rintro ⟨p', hne, h'⟩
  exact hne (typeExtensionality h'.1 h.1 fun x => (h'.2 x).trans (h.2 x).symm)

/-- `t2_powertypeUnique`: a Cardelli powertype determines its base type
uniquely. -/
theorem t2_powertypeUnique [Extensional E] {p t : E} (h : IsPowertypeOf p t) :
    ¬ ∃ t', t' ≠ t ∧ IsPowertypeOf p t' := by
  rintro ⟨t', hne, h'⟩
  have ht : IsType t := h.isType_base
  have ht' : IsType t' := h'.isType_base
  -- `t'` specializes itself, hence instantiates `p`, hence specializes `t`.
  have h₁ : Specializes t' t := (h.2 t').mp ((h'.2 t').mpr (Specializes.refl ht'))
  have h₂ : Specializes t t' := (h'.2 t).mp ((h.2 t).mpr (Specializes.refl ht))
  exact hne (h₁.antisymm h₂)

/-- `t3`: powertypes preserve specialization.  If `t₁` specializes `t₂` then the
powertype of `t₁` specializes the powertype of `t₂`. -/
theorem t3 {t₁ t₂ p₁ p₂ : E}
    (h : Specializes t₁ t₂) (h₁ : IsPowertypeOf p₁ t₁) (h₂ : IsPowertypeOf p₂ t₂) :
    Specializes p₁ p₂ :=
  ⟨h₁.1, fun e he => (h₂.2 e).mpr (((h₁.2 e).mp he).trans h)⟩

/-- `t4`: an Odell powertype (a categorizer) proper specializes the Cardelli
powertype of the same base type. -/
theorem t4 {t p c : E} (hp : IsPowertypeOf p t) (hc : Categorizes c t) :
    ProperSpecializes c p := by
  refine ⟨⟨hc.1, fun e he => (hp.2 e).mpr (hc.2 e he).1⟩, ?_⟩
  rintro rfl
  -- `c = p`, so the base type `t`, being an instance of `p`, would have to
  -- proper specialize itself.
  exact ProperSpecializes.irrefl (hc.2 t hp.iof_base)

/-- `t5`: two types that both partition the same type cannot proper specialize
each other. -/
theorem t5 [Extensional E] {t₁ t₂ t : E}
    (h₁ : Partitions t₁ t) (h₂ : Partitions t₂ t) : ¬ ProperSpecializes t₁ t₂ := by
  intro hps
  have hT₂ : IsType t₂ := h₂.1.1.1
  -- Since `t₁ ≠ t₂` and `t₁` specializes `t₂`, some instance of `t₂` is not an
  -- instance of `t₁`.
  have hex : ∃ s, iof s t₂ ∧ ¬ iof s t₁ := by
    apply Classical.byContradiction
    intro hno
    have hall : ∀ s, iof s t₂ → iof s t₁ := fun s hs =>
      Classical.byContradiction fun hn => hno ⟨s, hs, hn⟩
    exact hps.2 (hps.1.antisymm ⟨hT₂, hall⟩)
  obtain ⟨s, hs₂, hs₁⟩ := hex
  -- `s` categorizes-instance of `t₂`, so it proper specializes `t` and is a type.
  have hst : ProperSpecializes s t := h₂.1.1.2 s hs₂
  obtain ⟨e, he⟩ := hst.isType_left
  have heT : iof e t := hst.1.2 e he
  -- `t₁` completely categorizes `t`, so `e` instantiates some instance of `t₁`.
  obtain ⟨s', hes', hs'₁⟩ := h₁.1.2 e heT
  have hs'₂ : iof s' t₂ := hps.1.2 s' hs'₁
  -- `t₂` disjointly categorizes `t`, and `e` instantiates both `s` and `s'`.
  have hss' : s = s' := h₂.2.2 e s s' hs₂ hs'₂ he hes'
  exact hs₁ (by rw [hss']; exact hs'₁)

/-- `powertypeNotFirstOrder`: a Cardelli powertype is never a first-order type,
because its base type is one of its instances and base types are types, not
individuals. -/
theorem powertypeNotFirstOrder {p t : E} (h : IsPowertypeOf p t) : ¬ FirstOrderType p :=
  fun hfo => hfo.2 t h.iof_base h.isType_base

end MLTStar
