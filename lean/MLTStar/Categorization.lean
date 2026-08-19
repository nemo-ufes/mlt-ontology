import MLTStar.Powertype

/-!
# Categorization and partitioning

Results about Odell powertypes (categorization) and about partitioning that
neither `mlt_star.als` nor `tptp/mlt-star.p` states.

The headline results are:

* `categorizes_iff` — the categorizers of `t` are *exactly* the specializations
  of the Cardelli powertype of `t` that do not have `t` itself as an instance.
  `t4` gives only one half of one direction of this;
* `Partitions.existsUnique` — a partition really does partition: every instance
  of the base type instantiates exactly one instance of the partitioning type.
  This is the property the name promises, and it is nowhere checked in the
  existing specifications;
* `Partitions.eq_of_specializes` — two partitions of the same type ordered by
  specialization are equal, so distinct partitions of a type are
  specialization-incomparable.
-/

namespace MLTStar

universe u

variable {E : Type u} [Domain E]

/-! ## Categorizers are exactly the powertype's specializations that miss `t` -/

/-- A Cardelli powertype never categorizes its own base type: the base type is
one of its instances, and it does not proper specialize itself. -/
theorem IsPowertypeOf.not_categorizes {p t : E} (h : IsPowertypeOf p t) :
    ¬ Categorizes p t :=
  fun hc => ProperSpecializes.irrefl (t4 h hc)

/-- Given the Cardelli powertype `p` of `t`, a type categorizes `t` exactly when
it specializes `p` and does not have `t` among its instances.

The forward direction strengthens `t4`, which records only that a categorizer
proper specializes `p`; the backward direction has no counterpart in either
existing specification. -/
theorem categorizes_iff {p t : E} (hp : IsPowertypeOf p t) (c : E) :
    Categorizes c t ↔ (Specializes c p ∧ ¬ iof t c) := by
  constructor
  · intro hc
    refine ⟨⟨hc.1, fun e he => (hp.2 e).mpr (hc.2 e he).1⟩, fun htc => ?_⟩
    exact (hc.2 t htc).2 rfl
  · rintro ⟨hs, hnt⟩
    refine ⟨hs.1, fun t₃ ht₃ => ⟨(hp.2 t₃).mp (hs.2 t₃ ht₃), ?_⟩⟩
    rintro rfl
    exact hnt ht₃

/-! ## A partition partitions -/

/-- Every instance of the base type instantiates **exactly one** instance of a
type that partitions it.

Completeness supplies at least one and disjointness supplies at most one; the
existing specifications state the two halves separately and never draw the
conclusion. -/
theorem Partitions.existsUnique {t₁ t : E} (h : Partitions t₁ t) {e : E} (he : iof e t) :
    ∃ s, (iof s t₁ ∧ iof e s) ∧ ∀ y, iof y t₁ → iof e y → y = s := by
  obtain ⟨s, hes, hs₁⟩ := h.1.2 e he
  exact ⟨s, ⟨hs₁, hes⟩, fun y hy₁ hey => h.2.2 e y s hy₁ hs₁ hey hes⟩

/-! ## Distinct partitions are incomparable -/

/-- Two types that partition the same type and are ordered by specialization are
equal.  This is the contrapositive form of `t5`. -/
theorem Partitions.eq_of_specializes [Extensional E] {t₁ t₂ t : E}
    (h₁ : Partitions t₁ t) (h₂ : Partitions t₂ t) (hs : Specializes t₁ t₂) : t₁ = t₂ :=
  Classical.byContradiction fun hne => t5 h₁ h₂ ⟨hs, hne⟩

/-- Distinct partitions of the same type are specialization-incomparable. -/
theorem Partitions.not_specializes [Extensional E] {t₁ t₂ t : E}
    (h₁ : Partitions t₁ t) (h₂ : Partitions t₂ t) (hne : t₁ ≠ t₂) : ¬ Specializes t₁ t₂ :=
  fun hs => hne (h₁.eq_of_specializes h₂ hs)

end MLTStar
