module

public import Langlib.Grammars.Indexed.NormalForm.Aho.Scheduler.BoundedAccounting

@[expose]
public section

/-!
# Global embeddings of productive-node owners

The local productive nodes of a pending parse occupy one contiguous window in the root carrier
`Fin (10 * input.length)`.  A binary root owns the first slot; its left and right children
occupy the two following consecutive subwindows.  These embeddings agree definitionally, up to
the arithmetic offsets, with `NFParse.eventOwnerNat`.
-/

variable {T : Type}

namespace IndexedGrammar

namespace NFParse

/-- Productive nodes split into the binary root, the left subtree, and the right subtree. -/
public theorem productiveCount_binary
    {g : IndexedGrammar T} {A B C : g.nt} {stack : List g.flag}
    {u v : List T} {r : IRule T g.nt g.flag}
    (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
    (hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
    (left : NFParse g B stack u) (right : NFParse g C stack v) :
    (NFParse.binary hr hlhs hc hrhs left right).productiveCount =
      left.productiveCount + right.productiveCount + 1 := by
  simp only [productiveCount, binaryCount, terminalCount]
  omega

/-- Embed a left-child productive-node ID into the parent's preorder numbering. -/
public def embedBinaryLeftProductive
    {g : IndexedGrammar T} {A B C : g.nt} {stack : List g.flag}
    {u v : List T} {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    (left : NFParse g B stack u) (right : NFParse g C stack v)
    (owner : Fin left.productiveCount) :
    Fin (NFParse.binary hr hlhs hc hrhs left right).productiveCount :=
  ⟨owner.val + 1, by
    rw [productiveCount_binary hr hlhs hc hrhs left right]
    have := owner.isLt
    have := right.nodeCount_pos
    omega⟩

/-- Embed a right-child productive-node ID after the root and left-subtree ranges. -/
public def embedBinaryRightProductive
    {g : IndexedGrammar T} {A B C : g.nt} {stack : List g.flag}
    {u v : List T} {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    (left : NFParse g B stack u) (right : NFParse g C stack v)
    (owner : Fin right.productiveCount) :
    Fin (NFParse.binary hr hlhs hc hrhs left right).productiveCount :=
  ⟨left.productiveCount + owner.val + 1, by
    rw [productiveCount_binary hr hlhs hc hrhs left right]
    have := owner.isLt
    omega⟩

public theorem embedBinaryLeftProductive_injective
    {g : IndexedGrammar T} {A B C : g.nt} {stack : List g.flag}
    {u v : List T} {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    (left : NFParse g B stack u) (right : NFParse g C stack v) :
    Function.Injective (embedBinaryLeftProductive
      (hr := hr) (hlhs := hlhs) (hc := hc) (hrhs := hrhs) left right) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simp only [embedBinaryLeftProductive] at this
  omega

public theorem embedBinaryRightProductive_injective
    {g : IndexedGrammar T} {A B C : g.nt} {stack : List g.flag}
    {u v : List T} {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    (left : NFParse g B stack u) (right : NFParse g C stack v) :
    Function.Injective (embedBinaryRightProductive
      (hr := hr) (hlhs := hlhs) (hc := hc) (hrhs := hrhs) left right) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simp only [embedBinaryRightProductive] at this
  omega

end NFParse

namespace Aho

private theorem neutral_of_push_neutral_pop_for_owner_transport
    {g : IndexedGrammar T} {A B X Y : g.nt} {f : g.flag}
    (hpush : PushRule g A B f) (hneutral : Neutral g B X)
    (hpop : AugPop g f X Y) : Neutral g A Y := by
  have h₁ : g.Derives [ISym.indexed A []] [ISym.indexed B [f]] :=
    deri_of_tran (pushRule_transforms hpush [])
  have h₂ : g.Derives [ISym.indexed B [f]] [ISym.indexed X [f]] :=
    Neutral.lift_suffix hneutral [f]
  have h₃ : g.Derives [ISym.indexed X [f]] [ISym.indexed Y []] :=
    augPop_derives hpop []
  exact h₁.trans (h₂.trans h₃)

/-- A binary-free consumed route preserves the canonical productive-node owner numbering when
its popped prefix is removed.  This is the owner-aware form of
`consumeRoute_popContinuation_noBinary_with_consumption`; it lives here because
`NFParse.eventOwnerNat` is defined after that earlier continuation theorem. -/
public theorem consumeRoute_popContinuation_noBinary_with_owners
    {g : IndexedGrammar T} {A : g.nt} {stack : List g.flag} {w : List T}
    {p : NFParse g A stack w} {k : ℕ}
    (route : NFParse.ConsumeRoute g p k) (hroute : route.NoBinary) :
    ∃ Y suffix, ∃ rest : NFParse g Y suffix w,
      suffix = stack.drop (k + 1) ∧
      PopPath g A (stack.take (k + 1)) Y ∧
      rest.nodeCount < p.nodeCount ∧
      (∀ j, rest.ConsumesAt j ↔ p.ConsumesAt (k + 1 + j)) ∧
      (∀ d, d ∈ rest.eventDepths ↔ k + 1 + d ∈ p.eventDepths) ∧
      ∀ d, rest.eventOwnerNat d = p.eventOwnerNat (k + 1 + d) := by
  induction route with
  | @binaryLeft A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      exact False.elim hroute
  | @binaryRight A B C stack u v r hr hlhs hc hrhs left right k route ih =>
      exact False.elim hroute
  | @popHere A B f stack w r hr hlhs hc hrhs rest =>
      refine ⟨B, stack, rest, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using (PopPath.one (popRule_aug ⟨r, hr, hlhs, hc, hrhs⟩))
      · simp [NFParse.nodeCount]
      · intro j
        have hidx : 0 + 1 + j = j + 1 := by omega
        rw [hidx]
        exact (NFParse.consumesAt_pop_succ_iff hr hlhs hc hrhs rest j).symm
      · intro d
        constructor
        · intro hd
          exact Finset.mem_image.mpr ⟨d, hd, by omega⟩
        · intro hd
          rcases Finset.mem_image.mp hd with ⟨e, he, hed⟩
          have : e = d := by omega
          simpa [this] using he
      · intro d
        simp [Nat.add_comm]
  | @popTail A B f stack w r hr hlhs hc hrhs rest k route ih =>
      rcases ih hroute with
        ⟨Y, suffix, residual, hsuffix, path, hcount, hconsumes, hevents, howners⟩
      refine ⟨Y, suffix, residual, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [Nat.add_assoc] using hsuffix
      · simpa [Nat.add_assoc] using
          (PopPath.cons (popRule_aug ⟨r, hr, hlhs, hc, hrhs⟩) path)
      · simp only [NFParse.nodeCount]
        omega
      · intro j
        rw [hconsumes j]
        have hidx : (k + 1) + 1 + j = (k + 1 + j) + 1 := by omega
        rw [hidx]
        exact (NFParse.consumesAt_pop_succ_iff hr hlhs hc hrhs rest
          (k + 1 + j)).symm
      · intro d
        constructor
        · intro hd
          have hrest := (hevents d).1 hd
          exact Finset.mem_image.mpr ⟨k + 1 + d, hrest, by omega⟩
        · intro hd
          rcases Finset.mem_image.mp hd with ⟨e, he, hed⟩
          have heq : e = k + 1 + d := by omega
          exact (hevents d).2 (by simpa [heq] using he)
      · intro d
        calc
          residual.eventOwnerNat d = rest.eventOwnerNat (k + 1 + d) := howners d
          _ = (NFParse.pop hr hlhs hc hrhs rest).eventOwnerNat
              ((k + 1) + 1 + d) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (NFParse.eventOwnerNat_pop_succ hr hlhs hc hrhs rest
                (k + 1 + d)).symm
  | @push A B f stack w r hr hlhs hc hrhs rest k route ih =>
      have hused : (NFParse.push hr hlhs hc hrhs rest).ConsumesAt k :=
        route.toConsumesAt
      have hk : k < stack.length :=
        (NFParse.push hr hlhs hc hrhs rest).consumesAt_lt_stack_length hused
      cases stack with
      | nil => simp at hk
      | cons f' stack =>
          rcases ih hroute with
            ⟨Y, suffix, residual, hsuffix, path, hcount, hconsumes, hevents, howners⟩
          have path' : PopPath g B (f :: f' :: stack.take k) Y := by
            simpa [Nat.add_assoc] using path
          rcases path'.uncons with ⟨Z, hpop, restPath⟩
          have hcancel : Neutral g A Z :=
            neutral_of_push_neutral_pop_for_owner_transport
              ⟨r, hr, hlhs, hc, hrhs⟩ (Neutral.refl g B) hpop
          refine ⟨Y, suffix, residual, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [Nat.add_assoc] using hsuffix
          · simpa using restPath.preNeutral hcancel
          · simp only [NFParse.nodeCount]
            omega
          · intro j
            rw [hconsumes j]
            have hidx : (k + 1) + 1 + j = (k + 1 + j) + 1 := by omega
            rw [hidx]
            exact (NFParse.consumesAt_push_iff hr hlhs hc hrhs rest
              (k + 1 + j)).symm
          · intro d
            constructor
            · intro hd
              have hrest := (hevents d).1 hd
              exact Finset.mem_image.mpr ⟨k + 2 + d, hrest, by
                simp [Nat.add_comm, Nat.add_left_comm]⟩
            · intro hd
              rcases Finset.mem_image.mp hd with ⟨e, he, hed⟩
              have heq : e = k + 2 + d := by
                cases e with
                | zero => simp at hed; omega
                | succ e =>
                    simp only [Nat.pred_succ] at hed
                    omega
              exact (hevents d).2 (by simpa [heq, Nat.add_assoc] using he)
          · intro d
            calc
              residual.eventOwnerNat d = rest.eventOwnerNat (k + 2 + d) := by
                simpa [Nat.add_assoc] using howners d
              _ = (NFParse.push hr hlhs hc hrhs rest).eventOwnerNat
                  (k + 1 + d) := by
                rw [NFParse.eventOwnerNat_push]
                congr 1
                simp [NFParse.pushEventPreimage]
                omega

/-- A contiguous slice of the root productive-node carrier assigned to one pending parse. -/
public structure ProductiveOwnerWindow
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
  (parse : NFParse g A stack w) where
  base : ℕ
  /-- Productive nodes use only the initial `2|input|-1` slots. -/
  end_le : base + parse.productiveCount ≤ 2 * input.length - 1

/-- Start of the generic ghost-owner pool.  The preceding interval contains the primary and
shadow semantic windows together with the two dedicated temporary labels; every pooled label is
therefore outside both semantic windows and distinct from both temporary labels. -/
public def genericOwnerOffset (input : List T) : ℕ :=
  4 * input.length

/-- Embed one of the `6|input|` reusable pool slots into the generic owner bank. -/
public def genericOwner
    {g : IndexedGrammar T} {input : List T}
    (slot : Fin (6 * input.length)) : Fin (10 * input.length) :=
  let _ := g
  ⟨genericOwnerOffset input + slot.val, by
    have := slot.isLt
    simp only [genericOwnerOffset]
    omega⟩

@[simp] public theorem genericOwner_val
    {g : IndexedGrammar T} {input : List T}
    (slot : Fin (6 * input.length)) :
    (genericOwner (g := g) slot).val = genericOwnerOffset input + slot.val := rfl

public theorem genericOwner_injective
    {g : IndexedGrammar T} {input : List T} :
    Function.Injective (genericOwner (g := g) (input := input)) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [genericOwner_val] at hval
  omega

/-- The complete reusable owner universe.  Its cardinality, not the ambient carrier size,
is what bounds the number of persistent indices on the erased work tape. -/
public def genericOwnerRange
    (g : IndexedGrammar T) (input : List T) : List (Fin (10 * input.length)) :=
  List.ofFn (fun slot : Fin (6 * input.length) => genericOwner (g := g) slot)

@[simp] public theorem genericOwnerRange_length
    (g : IndexedGrammar T) (input : List T) :
    (genericOwnerRange g input).length = 6 * input.length := by
  simp [genericOwnerRange]

public theorem genericOwnerRange_nodup
    (g : IndexedGrammar T) (input : List T) :
    (genericOwnerRange g input).Nodup := by
  exact List.nodup_ofFn.mpr genericOwner_injective

public theorem mem_genericOwnerRange_iff
    {g : IndexedGrammar T} {input : List T}
    {owner : Fin (10 * input.length)} :
    owner ∈ genericOwnerRange g input ↔
      ∃ slot : Fin (6 * input.length), owner = genericOwner (g := g) slot := by
  constructor
  · intro hmem
    rcases List.mem_ofFn.mp hmem with ⟨slot, hslot⟩
    exact ⟨slot, hslot.symm⟩
  · rintro ⟨slot, rfl⟩
    exact List.mem_ofFn.mpr ⟨slot, rfl⟩

public theorem genericOwnerRange_val_ge
    {g : IndexedGrammar T} {input : List T}
    {owner : Fin (10 * input.length)}
    (howner : owner ∈ genericOwnerRange g input) :
    genericOwnerOffset input ≤ owner.val := by
  rcases mem_genericOwnerRange_iff.mp howner with ⟨slot, rfl⟩
  simp [genericOwnerOffset]

namespace ProductiveOwnerWindow

/-- The first of the two labels between the semantic banks and the generic owner pool. -/
public def scratchOwner
    {g : IndexedGrammar T} {input : List T}
    (hinput : 0 < input.length) : Fin (10 * input.length) :=
  let _ := g
  ⟨4 * input.length - 2, by omega⟩

@[simp] public theorem scratchOwner_val
    {g : IndexedGrammar T} {input : List T}
    (hinput : 0 < input.length) :
    (scratchOwner (g := g) hinput).val = 4 * input.length - 2 := rfl

/-- The second of the two labels between the semantic banks and the generic owner pool. -/
public def transientOwner
    {g : IndexedGrammar T} {input : List T}
    (hinput : 0 < input.length) : Fin (10 * input.length) :=
  let _ := g
  ⟨4 * input.length - 1, by omega⟩

@[simp] public theorem transientOwner_val
    {g : IndexedGrammar T} {input : List T}
    (hinput : 0 < input.length) :
    (transientOwner (g := g) hinput).val = 4 * input.length - 1 := rfl

public theorem scratchOwner_ne_transientOwner
    {g : IndexedGrammar T} {input : List T}
    (hinput : 0 < input.length) :
    scratchOwner (g := g) hinput ≠ transientOwner (g := g) hinput := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [scratchOwner_val, transientOwner_val] at hval
  omega

/-- Embed a local productive-node ID into its root-capacity owner window. -/
public def owner
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} (window : ProductiveOwnerWindow (input := input) parse)
    (node : Fin parse.productiveCount) : Fin (10 * input.length) :=
  ⟨window.base + node.val, by
    have hlocal := node.isLt
    have hend := window.end_le
    omega⟩

@[simp] public theorem owner_val
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} (window : ProductiveOwnerWindow (input := input) parse)
    (node : Fin parse.productiveCount) :
    (window.owner node).val = window.base + node.val := rfl

/-- A productive window embeds local IDs injectively into the root carrier. -/
public theorem owner_injective
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} (window : ProductiveOwnerWindow (input := input) parse) :
    Function.Injective window.owner := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [owner_val] at hval
  omega

/-- Globally embed the canonical owner selected for an event depth. -/
public def eventOwner
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} (window : ProductiveOwnerWindow (input := input) parse)
    (d : ℕ) (hd : d ∈ parse.eventDepths) : Fin (10 * input.length) :=
  window.owner (parse.eventOwner d hd)

@[simp] public theorem eventOwner_val
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} (window : ProductiveOwnerWindow (input := input) parse)
    (d : ℕ) (hd : d ∈ parse.eventDepths) :
    (window.eventOwner d hd).val = window.base + parse.eventOwnerNat d := rfl

/-- Distinct event depths in one task receive distinct global owners. -/
public theorem eventOwner_injective
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} (window : ProductiveOwnerWindow (input := input) parse) :
    ∀ {d e : ℕ} (hd : d ∈ parse.eventDepths) (he : e ∈ parse.eventDepths),
      window.eventOwner d hd = window.eventOwner e he → d = e := by
  intro d e hd he howner
  apply parse.eventOwner_injective hd he
  exact window.owner_injective howner

/-- The root parse owns the complete root productive-node carrier. -/
public def root
    {g : IndexedGrammar T} {input : List T}
    (parse : NFParse g g.initial [] input) :
    ProductiveOwnerWindow (input := input) parse where
  base := 0
  end_le := by
    rw [parse.productiveCount_eq_twice_yield_length_sub_one]
    omega

@[simp] public theorem root_base
    {g : IndexedGrammar T} {input : List T}
    (parse : NFParse g g.initial [] input) :
    (root parse).base = 0 := rfl

/-- Transport a window across a parse change which preserves productive-node count. -/
public def transport
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {parse' : NFParse g B stack' w'}
    (window : ProductiveOwnerWindow (input := input) parse)
    (hcount : parse'.productiveCount = parse.productiveCount) :
    ProductiveOwnerWindow (input := input) parse' where
  base := window.base
  end_le := by simpa [hcount] using window.end_le

@[simp] public theorem transport_base
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {stack stack' : List g.flag} {w w' : List T}
    {parse : NFParse g A stack w} {parse' : NFParse g B stack' w'}
    (window : ProductiveOwnerWindow (input := input) parse)
    (hcount : parse'.productiveCount = parse.productiveCount) :
    (window.transport hcount).base = window.base := rfl

/-- Unary pop constructors preserve the productive-node window. -/
public def popChild
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = some f}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B none]}
    {rest : NFParse g B stack w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.pop hr hlhs hc hrhs rest)) :
    ProductiveOwnerWindow (input := input) rest :=
  window.transport (by rfl)

/-- Unary push constructors preserve the productive-node window. -/
public def pushChild
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)) :
    ProductiveOwnerWindow (input := input) rest :=
  window.transport (by rfl)

@[simp] public theorem popChild_base
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = some f}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B none]}
    {rest : NFParse g B stack w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.pop hr hlhs hc hrhs rest)) :
    window.popChild.base = window.base := rfl

@[simp] public theorem pushChild_base
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest)) :
    window.pushChild.base = window.base := rfl

/-- Event owners commute with the one-position depth shift of a pop. -/
public theorem eventOwner_pop_succ
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = some f}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B none]}
    {rest : NFParse g B stack w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.pop hr hlhs hc hrhs rest))
    {d : ℕ} (hd : d ∈ rest.eventDepths) :
    window.eventOwner (d + 1) (Finset.mem_image.mpr ⟨d, hd, by omega⟩) =
      window.popChild.eventOwner d hd := by
  apply Fin.ext
  simp only [eventOwner_val, popChild_base]
  rw [NFParse.eventOwnerNat_pop_succ]

/-- Event owners commute with the canonical preimage selected through a push. -/
public theorem eventOwner_push
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    {d : ℕ} (hd : d ∈ (NFParse.push hr hlhs hc hrhs rest).eventDepths) :
    window.eventOwner d hd =
      window.pushChild.eventOwner (NFParse.pushEventPreimage rest.eventDepths d)
        (NFParse.pushEventPreimage_mem hd) := by
  apply Fin.ext
  simp only [eventOwner_val, pushChild_base]
  rw [NFParse.eventOwnerNat_push]

/-- Away from depth zero, a push has the unique event-depth preimage `d + 1`. -/
public theorem eventOwner_push_pos
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    {d : ℕ} (hdpos : 0 < d) (hd : d + 1 ∈ rest.eventDepths) :
    window.eventOwner d (Finset.mem_image.mpr ⟨d + 1, hd, by simp⟩) =
      window.pushChild.eventOwner (d + 1) hd := by
  apply Fin.ext
  simp only [eventOwner_val, pushChild_base]
  rw [NFParse.eventOwnerNat_push]
  simp [NFParse.pushEventPreimage, Nat.ne_of_gt hdpos]

/-- Every positive parent event has the unique child preimage one position deeper. -/
public theorem exists_child_eventDepth_of_push_parent_pos
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (_window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    {d : ℕ} (hdpos : 0 < d)
    (hd : d ∈ (NFParse.push hr hlhs hc hrhs rest).eventDepths) :
    d + 1 ∈ rest.eventDepths := by
  rcases Finset.mem_image.mp hd with ⟨e, he, hpred⟩
  have heq : e = d + 1 := by
    cases e with
    | zero => simp at hpred; omega
    | succ e => simp only [Nat.pred_succ] at hpred; omega
  simpa [heq] using he

/-- A child event newly exposed at depth one cannot collide with any positive parent event. -/
public theorem eventOwner_one_ne_parent_positive
    {g : IndexedGrammar T} {input : List T}
    {A B : g.nt} {f : g.flag} {stack : List g.flag} {w : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)]}
    {rest : NFParse g B (f :: stack) w}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.push hr hlhs hc hrhs rest))
    (hone : 1 ∈ rest.eventDepths) {d : ℕ} (hdpos : 0 < d)
    (hd : d ∈ (NFParse.push hr hlhs hc hrhs rest).eventDepths) :
    window.pushChild.eventOwner 1 hone ≠ window.eventOwner d hd := by
  intro heq
  have hchild : d + 1 ∈ rest.eventDepths :=
    window.exists_child_eventDepth_of_push_parent_pos hdpos hd
  have htransport := window.eventOwner_push_pos hdpos hchild
  have howners : window.pushChild.eventOwner 1 hone =
      window.pushChild.eventOwner (d + 1) hchild := heq.trans htransport
  have hdepth := window.pushChild.eventOwner_injective hone hchild howners
  omega

/-- The immediately preceding global slot is a canonical scratch owner for any non-root
productive window. -/
public def predecessor
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} (window : ProductiveOwnerWindow (input := input) parse)
    (hbase : 0 < window.base) : Fin (10 * input.length) :=
  ⟨window.base - 1, by
    have hend := window.end_le
    omega⟩

@[simp] public theorem predecessor_val
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} (window : ProductiveOwnerWindow (input := input) parse)
    (hbase : 0 < window.base) :
    (window.predecessor hbase).val = window.base - 1 := rfl

public theorem predecessor_lt_base
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} (window : ProductiveOwnerWindow (input := input) parse)
    (hbase : 0 < window.base) :
    (window.predecessor hbase).val < window.base := by
  simp only [predecessor_val]
  omega

/-- The distinguished scratch slot is outside, and hence distinct from, every local owner. -/
public theorem predecessor_ne_owner
    {g : IndexedGrammar T} {input : List T}
    {A : g.nt} {stack : List g.flag} {w : List T}
    {parse : NFParse g A stack w} (window : ProductiveOwnerWindow (input := input) parse)
    (hbase : 0 < window.base) (node : Fin parse.productiveCount) :
    window.predecessor hbase ≠ window.owner node := by
  intro heq
  have hval := congrArg Fin.val heq
  have hlt := window.predecessor_lt_base hbase
  simp only [owner_val] at hval
  omega

/-- The left child occupies the subwindow immediately after the binary root. -/
public def binaryLeft
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right)) :
    ProductiveOwnerWindow (input := input) left where
  base := window.base + 1
  end_le := by
    have hend := window.end_le
    rw [NFParse.productiveCount_binary hr hlhs hc hrhs left right] at hend
    omega

/-- The right child occupies the subwindow after the root and complete left subtree. -/
public def binaryRight
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right)) :
    ProductiveOwnerWindow (input := input) right where
  base := window.base + left.productiveCount + 1
  end_le := by
    have hend := window.end_le
    rw [NFParse.productiveCount_binary hr hlhs hc hrhs left right] at hend
    omega

@[simp] public theorem binaryLeft_base
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right)) :
    window.binaryLeft.base = window.base + 1 := rfl

@[simp] public theorem binaryRight_base
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right)) :
    window.binaryRight.base = window.base + left.productiveCount + 1 := rfl

/-- Embedding through the left subwindow agrees with embedding its local ID into the parent. -/
public theorem owner_embedBinaryLeft
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    (node : Fin left.productiveCount) :
    window.owner (NFParse.embedBinaryLeftProductive left right node) =
      window.binaryLeft.owner node := by
  apply Fin.ext
  simp only [owner_val, binaryLeft_base, NFParse.embedBinaryLeftProductive]
  omega

/-- Embedding through the right subwindow agrees with embedding its local ID into the parent. -/
public theorem owner_embedBinaryRight
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    (node : Fin right.productiveCount) :
    window.owner (NFParse.embedBinaryRightProductive left right node) =
      window.binaryRight.owner node := by
  apply Fin.ext
  simp only [owner_val, binaryRight_base, NFParse.embedBinaryRightProductive]
  omega

/-- A positive event inherited from the left child has the same global owner in both windows. -/
public theorem eventOwner_binaryLeft
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    {d : ℕ} (hd0 : d ≠ 0) (hd : d ∈ left.eventDepths) :
    window.eventOwner d (by
      simp only [NFParse.eventDepths, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inl hd)) =
      window.binaryLeft.eventOwner d hd := by
  apply Fin.ext
  simp only [eventOwner_val, binaryLeft_base]
  rw [NFParse.eventOwnerNat_binary_left hr hlhs hc hrhs left right hd0 hd]
  omega

/-- A positive event selected from the right child has the same global owner in both windows. -/
public theorem eventOwner_binaryRight
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right))
    {d : ℕ} (hd0 : d ≠ 0) (hleft : d ∉ left.eventDepths)
    (hd : d ∈ right.eventDepths) :
    window.eventOwner d (by
      simp only [NFParse.eventDepths, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr hd)) =
      window.binaryRight.eventOwner d hd := by
  apply Fin.ext
  simp only [eventOwner_val, binaryRight_base]
  rw [NFParse.eventOwnerNat_binary_right hr hlhs hc hrhs left right hd0 hleft]
  omega

/-- The binary root's productive event is exactly the first owner of its window. -/
public theorem eventOwner_binary_zero_val
    {g : IndexedGrammar T} {input : List T}
    {A B C : g.nt} {stack : List g.flag} {u v : List T}
    {r : IRule T g.nt g.flag}
    {hr : r ∈ g.rules} {hlhs : r.lhs = A} {hc : r.consume = none}
    {hrhs : r.rhs =
      [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none]}
    {left : NFParse g B stack u} {right : NFParse g C stack v}
    (window : ProductiveOwnerWindow (input := input)
      (NFParse.binary hr hlhs hc hrhs left right)) :
    (window.eventOwner 0 (by simp [NFParse.eventDepths])).val = window.base := by
  simp [eventOwner_val, NFParse.eventOwnerNat_binary_zero]

end ProductiveOwnerWindow

end Aho
end IndexedGrammar
