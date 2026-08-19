import MLTStar.Constants

/-!
# Anti-patterns

The conjectures `ap1`, `ap2` and `ap3` of `tptp/mlt-star.p`.  Each says that a
modelling configuration that occurs in practice is ruled out by MLT*, so that a
model exhibiting it is provably wrong rather than merely unusual.

Note that `ap1` needs no axioms at all — it is immediate from the definition of
`Individual` — while `ap2` and `ap3` need only the constant `cSot` of `a15`.
Neither needs `a4` or `a9`.
-/

namespace MLTStar

universe u

variable {E : Type u} [Domain E]

/-- No entity is both a first-order and a second-order type: an instance of such
an entity would have to be an individual and a type at once. -/
theorem not_firstOrderType_and_secondOrderType {x : E}
    (h₁ : FirstOrderType x) (h₂ : SecondOrderType x) : False := by
  obtain ⟨y, hy⟩ := h₁.1
  exact h₁.2 y hy (h₂.2 y hy).1

/-- `ap1`: an individual has no instances.  Classifying anything under an
individual is an error. -/
theorem ap1 : ¬ ∃ t₁ t₂ : E, Individual t₁ ∧ iof t₂ t₁ :=
  fun ⟨_, t₂, hi, h⟩ => hi ⟨t₂, h⟩

/-- No second-order type instantiates a second-order type.  This is `ap2` with
the constant `cSot` replaced by the underlying predicate. -/
theorem not_iof_of_secondOrderType {t₁ t₂ : E}
    (h₁ : SecondOrderType t₁) (h₂ : SecondOrderType t₂) : ¬ iof t₂ t₁ :=
  fun h => not_firstOrderType_and_secondOrderType (h₁.2 t₂ h) h₂

/-- `ap2`: no instance of the type of second-order types instantiates another
instance of it. -/
theorem ap2 [Constants E] :
    ¬ ∃ t₁ t₂ : E, iof t₁ (cSot : E) ∧ iof t₂ (cSot : E) ∧ iof t₂ t₁ :=
  fun ⟨_, _, h₁, h₂, h⟩ =>
    not_iof_of_secondOrderType ((iof_cSot_iff _).mp h₁) ((iof_cSot_iff _).mp h₂) h

/-- No second-order type specializes the type of all second-order types: its
instances would be first-order and second-order types at once. -/
theorem not_specializes_cSot_of_secondOrderType [Constants E] {t : E}
    (h : SecondOrderType t) : ¬ Specializes t (cSot : E) := by
  intro hs
  obtain ⟨e, he⟩ := h.1
  exact not_firstOrderType_and_secondOrderType (h.2 e he)
    ((iof_cSot_iff e).mp (hs.2 e he))

/-- `ap3`: no instance of the type of second-order types specializes it. -/
theorem ap3 [Constants E] : ¬ ∃ t : E, iof t (cSot : E) ∧ Specializes t (cSot : E) :=
  fun ⟨_, h₁, h₂⟩ => not_specializes_cSot_of_secondOrderType ((iof_cSot_iff _).mp h₁) h₂

end MLTStar
