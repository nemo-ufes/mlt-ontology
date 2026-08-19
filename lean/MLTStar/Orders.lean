import MLTStar.AntiPatterns

/-!
# Order structure

Results about how the order of a type behaves under specialization and under
the powertype construction.  None of these appears in `mlt_star.als` or
`tptp/mlt-star.p`; the TPTP fragment says only that a powertype is never
first-order (`powertypeNotFirstOrder`), which is the weakest shadow of
`IsPowertypeOf.secondOrderType` below.

The headline results are:

* order is inherited *downwards* along specialization
  (`firstOrderType_of_specializes`, `secondOrderType_of_specializes`), hence
  specialization never crosses orders in either direction;
* the Cardelli powertype of a first-order type is a *second*-order type
  (`IsPowertypeOf.secondOrderType`) — powertypes raise the order by exactly one;
* `cIndividual` and `cFot` are the *tops* of their orders
  (`firstOrderType_iff_specializes_cIndividual` and its second-order analogue),
  so that `a13`–`a15` pin down the bottom of the MLT stratification completely:
  they are the unique powertypes of one another (`IsPowertypeOf.eq_cFot`,
  `IsPowertypeOf.eq_cSot`).
-/

namespace MLTStar

universe u

variable {E : Type u} [Domain E]

/-! ## Self-instantiation and order -/

/-- A first-order type does not instantiate itself: it would have to be one of
its own instances, hence an individual, hence not a type. -/
theorem FirstOrderType.not_iof_self {x : E} (h : FirstOrderType x) : ¬ iof x x :=
  fun hx => h.2 x hx h.1

/-- A second-order type does not instantiate itself. -/
theorem SecondOrderType.not_iof_self {x : E} (h : SecondOrderType x) : ¬ iof x x :=
  fun hx => not_firstOrderType_and_secondOrderType (h.2 x hx) h

/-! ## Order is inherited downwards along specialization -/

theorem firstOrderType_of_specializes {a b : E}
    (hs : Specializes a b) (hb : FirstOrderType b) : FirstOrderType a :=
  ⟨hs.1, fun y hy => hb.2 y (hs.2 y hy)⟩

theorem secondOrderType_of_specializes {a b : E}
    (hs : Specializes a b) (hb : SecondOrderType b) : SecondOrderType a :=
  ⟨hs.1, fun y hy => hb.2 y (hs.2 y hy)⟩

/-- Specialization never goes from a first-order type up to a second-order one:
`a` would inherit `b`'s order and be of both orders at once. -/
theorem not_specializes_of_firstOrder_secondOrder {a b : E}
    (ha : FirstOrderType a) (hb : SecondOrderType b) : ¬ Specializes a b :=
  fun hs => not_firstOrderType_and_secondOrderType ha (secondOrderType_of_specializes hs hb)

/-- Nor the other way round. -/
theorem not_specializes_of_secondOrder_firstOrder {a b : E}
    (ha : SecondOrderType a) (hb : FirstOrderType b) : ¬ Specializes a b :=
  fun hs => not_firstOrderType_and_secondOrderType (firstOrderType_of_specializes hs hb) ha

/-! ## Powertypes raise the order -/

/-- The Cardelli powertype of a first-order type is a second-order type.

Every instance of `p` specializes `t`, and a specialization of a first-order
type is first-order; so every instance of `p` is first-order, which is what it
takes for `p` to be second-order.  `powertypeNotFirstOrder` in
`tptp/mlt-star.p` is the special case that `p` is not first-order. -/
theorem IsPowertypeOf.secondOrderType {p t : E}
    (hp : IsPowertypeOf p t) (ht : FirstOrderType t) : SecondOrderType p :=
  ⟨hp.1, fun y hy => firstOrderType_of_specializes ((hp.2 y).mp hy) ht⟩

/-! ## The constants are the tops of their orders -/

variable [Constants E]

/-- Being first-order is the same as specializing the type of all individuals.
So `cIndividual` is the top of the first order. -/
theorem firstOrderType_iff_specializes_cIndividual {t : E} :
    FirstOrderType t ↔ Specializes t (cIndividual : E) :=
  ⟨fun h => ⟨h.1, fun e he => (iof_cIndividual_iff e).mpr (h.2 e he)⟩,
   fun h => ⟨h.1, fun e he => (iof_cIndividual_iff e).mp (h.2 e he)⟩⟩

/-- Being second-order is the same as specializing the type of all first-order
types.  So `cFot` is the top of the second order. -/
theorem secondOrderType_iff_specializes_cFot {t : E} :
    SecondOrderType t ↔ Specializes t (cFot : E) :=
  ⟨fun h => ⟨h.1, fun e he => (iof_cFot_iff e).mpr (h.2 e he)⟩,
   fun h => ⟨h.1, fun e he => (iof_cFot_iff e).mp (h.2 e he)⟩⟩

/-- `cFot` is *the* Cardelli powertype of `cIndividual` — not merely one. -/
theorem IsPowertypeOf.eq_cFot [Extensional E] {p : E}
    (h : IsPowertypeOf p (cIndividual : E)) : p = (cFot : E) :=
  typeExtensionality h.1 cFot_isType fun x =>
    (h.2 x).trans (firstOrderType_iff_specializes_cIndividual.symm.trans
      (iof_cFot_iff x).symm)

/-- `cSot` is *the* Cardelli powertype of `cFot`. -/
theorem IsPowertypeOf.eq_cSot [Extensional E] {p : E}
    (h : IsPowertypeOf p (cFot : E)) : p = (cSot : E) :=
  typeExtensionality h.1 cSot_isType fun x =>
    (h.2 x).trans (secondOrderType_iff_specializes_cFot.symm.trans
      (iof_cSot_iff x).symm)

end MLTStar
