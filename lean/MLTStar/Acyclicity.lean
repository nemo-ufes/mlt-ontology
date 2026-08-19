import MLTStar.Powertype

/-!
# What grounding rules out

`a4` is stated in `tptp/mlt-star.p` but no conjecture there uses it, and
`mlt_star.als` assumes the corresponding `typeWellFounded` fact rather than
deriving consequences from it.  This module puts it to work.

Everything here rests on one lemma, `not_all_instances_specialize`: a type
cannot have all of its instances specializing it.  Such a type would be
"self-supporting" — the class of its instances would be closed under
instantiation, since an instance of an instance of `t` would again be an
instance of `t` — and `a4` forbids exactly that.

The consequences are that two shapes of circularity are impossible: no type is
its own Cardelli powertype, and no type categorizes itself.
-/

namespace MLTStar

universe u

variable {E : Type u} [Domain E]

/-- No type has all of its instances specializing it.

Otherwise the class of instances of `t` would be a non-empty class of types
closed under instantiation, contradicting `a4`. -/
theorem not_all_instances_specialize [Grounded E] {t : E} (ht : IsType t) :
    ¬ ∀ w, iof w t → Specializes w t := by
  intro h
  obtain ⟨y, hy, z, hz, hzn⟩ :=
    grounded (fun w => iof w t) ht (fun w hw => (h w hw).isType_left)
  exact hzn ((h y hy).2 z hz)

/-- No type is its own Cardelli powertype.

If `t` were the powertype of `t`, its instances would be precisely its
specializations, making it self-supporting. -/
theorem IsPowertypeOf.ne [Grounded E] {p t : E} (h : IsPowertypeOf p t) : p ≠ t := by
  intro heq
  subst heq
  exact not_all_instances_specialize h.isType_base fun w hw => (h.2 w).mp hw

/-- No type categorizes itself. -/
theorem not_categorizes_self [Grounded E] {t : E} : ¬ Categorizes t t := by
  intro h
  exact not_all_instances_specialize h.1 fun w hw => (h.2 w hw).1

/-- A categorizer is never the type it categorizes. -/
theorem Categorizes.ne [Grounded E] {c t : E} (h : Categorizes c t) : c ≠ t := by
  intro heq
  subst heq
  exact not_categorizes_self h

end MLTStar
