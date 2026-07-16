module

public import Langlib.Grammars.Indexed.Shrinking.Scope

@[expose]
public section

/-!
# Critical scopes in indexed parse trees

For a finite set `Z` of small frontier words, a critical parse node is the
last node on some branch whose `beta` word lies outside `Z`.  Thus its own
frontier is large while every proper descendant has a frontier in `Z`.
This file locates such a node and proves Gilman's quadratic bound on its
frontier length.
-/

variable {T : Type}

namespace IndexedGrammar.NFParse

/-- Every parse node in `p`, including its root, has beta word in `Z`. -/
public inductive AllBetaIn {g : IndexedGrammar T} (Z : Set (List (g.nt ⊕ T))) :
    {A : g.nt} → {sigma : List g.flag} → {w : List T} →
      NFParse g A sigma w → Prop where
  | binary {A B C : g.nt} {sigma : List g.flag} {u v : List T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
      (hrhs : r.rhs =
        [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none])
      (left : NFParse g B sigma u) (right : NFParse g C sigma v)
      (root : (NFParse.binary hr hlhs hc hrhs left right).beta ∈ Z)
      (leftAll : AllBetaIn Z left) (rightAll : AllBetaIn Z right) :
      AllBetaIn Z (NFParse.binary hr hlhs hc hrhs left right)
  | pop {A B : g.nt} {f : g.flag} {suffix : List g.flag} {w : List T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = some f)
      (hrhs : r.rhs = [IRhsSymbol.nonterminal B none])
      (rest : NFParse g B suffix w)
      (root : (NFParse.pop hr hlhs hc hrhs rest).beta ∈ Z)
      (restAll : AllBetaIn Z rest) :
      AllBetaIn Z (NFParse.pop hr hlhs hc hrhs rest)
  | push {A B : g.nt} {f : g.flag} {sigma : List g.flag} {w : List T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
      (hrhs : r.rhs = [IRhsSymbol.nonterminal B (some f)])
      (rest : NFParse g B (f :: sigma) w)
      (root : (NFParse.push hr hlhs hc hrhs rest).beta ∈ Z)
      (restAll : AllBetaIn Z rest) :
      AllBetaIn Z (NFParse.push hr hlhs hc hrhs rest)
  | terminal {A : g.nt} {sigma : List g.flag} {a : T}
      {r : IRule T g.nt g.flag}
      (hr : r ∈ g.rules) (hlhs : r.lhs = A) (hc : r.consume = none)
      (hrhs : r.rhs = [IRhsSymbol.terminal a])
      (root : (NFParse.terminal (σ := sigma) hr hlhs hc hrhs).beta ∈ Z) :
      AllBetaIn Z (NFParse.terminal (σ := sigma) hr hlhs hc hrhs)

/-- Every proper descendant of the root of `p` has beta word in `Z`. -/
public def ProperBetaIn {g : IndexedGrammar T} (Z : Set (List (g.nt ⊕ T)))
    {A : g.nt} {sigma : List g.flag} {w : List T}
    (p : NFParse g A sigma w) : Prop :=
  match p with
  | .binary _ _ _ _ left right => AllBetaIn Z left ∧ AllBetaIn Z right
  | .pop _ _ _ _ rest => AllBetaIn Z rest
  | .push _ _ _ _ rest => AllBetaIn Z rest
  | .terminal _ _ _ _ => True

/-- A node outside `Z` all of whose proper descendants lie in `Z`. -/
public def IsCritical {g : IndexedGrammar T} (Z : Set (List (g.nt ⊕ T)))
    {A : g.nt} {sigma : List g.flag} {w : List T}
    (p : NFParse g A sigma w) : Prop :=
  p.beta ∉ Z ∧ p.ProperBetaIn Z

public theorem beta_mem_of_allBetaIn {g : IndexedGrammar T}
    {Z : Set (List (g.nt ⊕ T))} {A : g.nt} {sigma : List g.flag}
    {w : List T} {p : NFParse g A sigma w} (h : p.AllBetaIn Z) :
    p.beta ∈ Z := by
  cases h <;> assumption

public theorem properBetaIn_of_allBetaIn {g : IndexedGrammar T}
    {Z : Set (List (g.nt ⊕ T))} {A : g.nt} {sigma : List g.flag}
    {w : List T} {p : NFParse g A sigma w} (h : p.AllBetaIn Z) :
    p.ProperBetaIn Z := by
  cases h with
  | binary _ _ _ _ _ _ _ hleft hright =>
      exact ⟨hleft, hright⟩
  | pop _ _ _ _ _ _ hrest => exact hrest
  | push _ _ _ _ _ _ hrest => exact hrest
  | terminal => trivial

/-- A critical subparse together with its position in the surrounding yield. -/
public structure LocatedCritical (g : IndexedGrammar T)
    (Z : Set (List (g.nt ⊕ T))) (rootNT : g.nt)
    (rootStack : List g.flag) (whole : List T) where
  leftContext : List T
  factor : List T
  rightContext : List T
  nt : g.nt
  stack : List g.flag
  parse : NFParse g nt stack factor
  whole_eq : whole = leftContext ++ factor ++ rightContext
  critical : parse.IsCritical Z
  rebuild : ∀ {replacement : List T}, NFParse g nt stack replacement →
    NFParse g rootNT rootStack (leftContext ++ replacement ++ rightContext)

private def parsedWord {g : IndexedGrammar T} {A : g.nt}
    {sigma : List g.flag} {w : List T} (_ : NFParse g A sigma w) : List T :=
  w

private def parsedStack {g : IndexedGrammar T} {A : g.nt}
    {sigma : List g.flag} {w : List T} (_ : NFParse g A sigma w) : List g.flag :=
  sigma

/-- Every parse tree containing a beta word outside `Z` contains a last such
node, located as a contiguous factor of the original yield. -/
public theorem exists_locatedCritical_of_not_allBetaIn
    {g : IndexedGrammar T} (Z : Set (List (g.nt ⊕ T)))
    {A : g.nt} {sigma : List g.flag} {w : List T}
    (p : NFParse g A sigma w) (hout : ¬ p.AllBetaIn Z) :
    Nonempty (LocatedCritical g Z A sigma w) := by
  induction p with
  | binary hr hlhs hc hrhs left right ihleft ihrigh =>
      by_cases hproper :
          (NFParse.binary hr hlhs hc hrhs left right).ProperBetaIn Z
      · have hall : left.AllBetaIn Z ∧ right.AllBetaIn Z := by
          simpa [ProperBetaIn] using hproper
        have hroot : (NFParse.binary hr hlhs hc hrhs left right).beta ∉ Z := by
          intro hbeta
          exact hout (AllBetaIn.binary hr hlhs hc hrhs left right
            hbeta hall.1 hall.2)
        exact ⟨{
          leftContext := []
          factor := parsedWord (NFParse.binary hr hlhs hc hrhs left right)
          rightContext := []
          nt := _
          stack := parsedStack (NFParse.binary hr hlhs hc hrhs left right)
          parse := NFParse.binary hr hlhs hc hrhs left right
          whole_eq := by simp [parsedWord]
          critical := ⟨hroot, hproper⟩
          rebuild := fun replacement => by simpa using replacement
        }⟩
      · change ¬ (left.AllBetaIn Z ∧ right.AllBetaIn Z) at hproper
        by_cases hleft : left.AllBetaIn Z
        · obtain ⟨located⟩ := ihrigh (fun hright => hproper ⟨hleft, hright⟩)
          exact ⟨{
            leftContext := parsedWord left ++ located.leftContext
            factor := located.factor
            rightContext := located.rightContext
            nt := located.nt
            stack := located.stack
            parse := located.parse
            whole_eq := by
              calc
                parsedWord left ++ parsedWord right =
                    parsedWord left ++
                      (located.leftContext ++ located.factor ++ located.rightContext) :=
                  congrArg (parsedWord left ++ ·) located.whole_eq
                _ = (parsedWord left ++ located.leftContext) ++
                      located.factor ++ located.rightContext := by
                  simp [List.append_assoc]
            critical := located.critical
            rebuild := fun replacement => by
              simpa [List.append_assoc] using
                NFParse.binary hr hlhs hc hrhs left (located.rebuild replacement)
          }⟩
        · obtain ⟨located⟩ := ihleft hleft
          exact ⟨{
            leftContext := located.leftContext
            factor := located.factor
            rightContext := located.rightContext ++ parsedWord right
            nt := located.nt
            stack := located.stack
            parse := located.parse
            whole_eq := by
              calc
                parsedWord left ++ parsedWord right =
                    (located.leftContext ++ located.factor ++ located.rightContext) ++
                      parsedWord right :=
                  congrArg (· ++ parsedWord right) located.whole_eq
                _ = located.leftContext ++ located.factor ++
                      (located.rightContext ++ parsedWord right) := by
                  simp [List.append_assoc]
            critical := located.critical
            rebuild := fun replacement => by
              simpa [List.append_assoc] using
                NFParse.binary hr hlhs hc hrhs (located.rebuild replacement) right
          }⟩
  | pop hr hlhs hc hrhs rest ih =>
      by_cases hproper : (NFParse.pop hr hlhs hc hrhs rest).ProperBetaIn Z
      · have hall : rest.AllBetaIn Z := by simpa [ProperBetaIn] using hproper
        have hroot : (NFParse.pop hr hlhs hc hrhs rest).beta ∉ Z := by
          intro hbeta
          exact hout (AllBetaIn.pop hr hlhs hc hrhs rest hbeta hall)
        exact ⟨{
          leftContext := []
          factor := parsedWord (NFParse.pop hr hlhs hc hrhs rest)
          rightContext := []
          nt := _
          stack := parsedStack (NFParse.pop hr hlhs hc hrhs rest)
          parse := NFParse.pop hr hlhs hc hrhs rest
          whole_eq := by simp [parsedWord]
          critical := ⟨hroot, hproper⟩
          rebuild := fun replacement => by simpa using replacement
        }⟩
      · obtain ⟨located⟩ := ih hproper
        exact ⟨{
          leftContext := located.leftContext
          factor := located.factor
          rightContext := located.rightContext
          nt := located.nt
          stack := located.stack
          parse := located.parse
          whole_eq := located.whole_eq
          critical := located.critical
          rebuild := fun replacement =>
            NFParse.pop hr hlhs hc hrhs (located.rebuild replacement)
        }⟩
  | push hr hlhs hc hrhs rest ih =>
      by_cases hproper : (NFParse.push hr hlhs hc hrhs rest).ProperBetaIn Z
      · have hall : rest.AllBetaIn Z := by simpa [ProperBetaIn] using hproper
        have hroot : (NFParse.push hr hlhs hc hrhs rest).beta ∉ Z := by
          intro hbeta
          exact hout (AllBetaIn.push hr hlhs hc hrhs rest hbeta hall)
        exact ⟨{
          leftContext := []
          factor := parsedWord (NFParse.push hr hlhs hc hrhs rest)
          rightContext := []
          nt := _
          stack := parsedStack (NFParse.push hr hlhs hc hrhs rest)
          parse := NFParse.push hr hlhs hc hrhs rest
          whole_eq := by simp [parsedWord]
          critical := ⟨hroot, hproper⟩
          rebuild := fun replacement => by simpa using replacement
        }⟩
      · obtain ⟨located⟩ := ih hproper
        exact ⟨{
          leftContext := located.leftContext
          factor := located.factor
          rightContext := located.rightContext
          nt := located.nt
          stack := located.stack
          parse := located.parse
          whole_eq := located.whole_eq
          critical := located.critical
          rebuild := fun replacement =>
            NFParse.push hr hlhs hc hrhs (located.rebuild replacement)
        }⟩
  | terminal hr hlhs hc hrhs =>
      rename_i terminalA terminalStack terminalLetter terminalRule
      let q : NFParse g terminalA terminalStack [terminalLetter] :=
        NFParse.terminal hr hlhs hc hrhs
      exact ⟨{
        leftContext := []
        factor := parsedWord q
        rightContext := []
        nt := _
        stack := parsedStack q
        parse := q
        whole_eq := by simp [parsedWord]
        critical := ⟨
          fun hbeta => hout (AllBetaIn.terminal hr hlhs hc hrhs hbeta),
          by simp [q, ProperBetaIn, parsedStack, parsedWord]⟩
        rebuild := fun replacement => by simpa using replacement
      }⟩

/-! ## The quadratic critical-frontier bound -/

/-- Advancing the cut from one inherited flag occurrence to the next expands
the frontier by at most the uniform beta-word bound. -/
public theorem scopeAt_succ_length_le_of_allBetaIn
    {g : IndexedGrammar T} {Z : Set (List (g.nt ⊕ T))} {C : Nat}
    (hC : 1 ≤ C) (hbound : ∀ z ∈ Z, z.length ≤ C)
    {A : g.nt} {sigma : List g.flag} {w : List T}
    {p : NFParse g A sigma w} (hall : p.AllBetaIn Z)
    (k : Nat) (hk : k + 1 < sigma.length) :
    (p.scopeAt (k + 1)).length ≤ (p.scopeAt k).length * C := by
  induction hall generalizing k with
  | binary hr hlhs hc hrhs left right _ leftAll rightAll ihleft ihrigh =>
      have hleft := ihleft k hk
      have hright := ihrigh k hk
      simpa [scopeAt, List.length_append, Nat.add_mul] using
        Nat.add_le_add hleft hright
  | pop hr hlhs hc hrhs rest _ restAll ih =>
      cases k with
      | zero =>
          have hstack : (parsedStack rest) ≠ [] := by
            apply List.ne_nil_of_length_pos
            simpa [parsedStack] using hk
          have hbeta := hbound rest.beta (beta_mem_of_allBetaIn restAll)
          have hlen := rest.beta_length_eq_scopeAt_zero_of_stack_ne_nil hstack
          simpa [scopeAt, hlen] using hbeta
      | succ k =>
          have hk' : k + 1 < (parsedStack rest).length := by
            simp only [List.length_cons] at hk
            dsimp [parsedStack]
            omega
          simpa [scopeAt, Nat.add_assoc] using ih k hk'
  | push hr hlhs hc hrhs rest _ restAll ih =>
      have hk' : (k + 1) + 1 < (parsedStack rest).length := by
        dsimp [parsedStack]
        omega
      simpa [scopeAt, Nat.add_assoc] using ih (k + 1) hk'
  | terminal hr hlhs hc hrhs _ =>
      simpa [scopeAt] using hC

/-- If the cut occurrence is the bottom flag, the terminal yield is at most
`C` times the size of its scope frontier. -/
public theorem yield_length_le_scopeAt_mul_of_bottom
    {g : IndexedGrammar T} {Z : Set (List (g.nt ⊕ T))} {C : Nat}
    (hC : 1 ≤ C) (hbound : ∀ z ∈ Z, z.length ≤ C)
    {A : g.nt} {sigma : List g.flag} {w : List T}
    {p : NFParse g A sigma w} (hall : p.AllBetaIn Z)
    (k : Nat) (hk : k < sigma.length) (hbottom : sigma.drop (k + 1) = []) :
    w.length ≤ (p.scopeAt k).length * C := by
  induction hall generalizing k with
  | binary hr hlhs hc hrhs left right _ leftAll rightAll ihleft ihrigh =>
      have hleft := ihleft k hk hbottom
      have hright := ihrigh k hk hbottom
      simpa [scopeAt, List.length_append, Nat.add_mul] using
        Nat.add_le_add hleft hright
  | pop hr hlhs hc hrhs rest _ restAll ih =>
      cases k with
      | zero =>
          have hstack : parsedStack rest = [] := by
            simpa [parsedStack] using hbottom
          have hbeta := hbound rest.beta (beta_mem_of_allBetaIn restAll)
          have hlen := rest.beta_length_eq_yield_of_stack_eq_nil hstack
          simpa [scopeAt, hlen] using hbeta
      | succ k =>
          have hk' : k < (parsedStack rest).length := by
            simp only [List.length_cons] at hk
            dsimp [parsedStack]
            omega
          have hbottom' : (parsedStack rest).drop (k + 1) = [] := by
            simpa [parsedStack, Nat.add_assoc] using hbottom
          simpa [scopeAt] using ih k hk' hbottom'
  | push hr hlhs hc hrhs rest _ restAll ih =>
      have hk' : k + 1 < (parsedStack rest).length := by
        dsimp [parsedStack]
        omega
      have hbottom' : (parsedStack rest).drop ((k + 1) + 1) = [] := by
        simpa [parsedStack, Nat.add_assoc] using hbottom
      simpa [scopeAt, Nat.add_assoc] using ih (k + 1) hk' hbottom'
  | terminal hr hlhs hc hrhs _ =>
      simpa [scopeAt] using hC

/-- Gilman's critical-scope estimate: if every proper descendant has beta
length at most `C`, then the critical beta word has length at most `C^2`. -/
public theorem beta_length_le_sq_of_critical
    {g : IndexedGrammar T} {Z : Set (List (g.nt ⊕ T))} {C : Nat}
    (hC : 2 ≤ C) (hbound : ∀ z ∈ Z, z.length ≤ C)
    {A : g.nt} {sigma : List g.flag} {w : List T}
    {p : NFParse g A sigma w} (hcritical : p.IsCritical Z) :
    p.beta.length ≤ C * C := by
  have hC1 : 1 ≤ C := by omega
  cases p with
  | binary hr hlhs hc hrhs left right =>
      have hall : left.AllBetaIn Z ∧ right.AllBetaIn Z := by
        simpa [IsCritical, ProperBetaIn] using hcritical.2
      have hleft := hbound left.beta (beta_mem_of_allBetaIn hall.1)
      have hright := hbound right.beta (beta_mem_of_allBetaIn hall.2)
      calc
        (NFParse.binary hr hlhs hc hrhs left right).beta.length =
            left.beta.length + right.beta.length := by simp
        _ ≤ C + C := Nat.add_le_add hleft hright
        _ = 2 * C := by omega
        _ ≤ C * C := Nat.mul_le_mul_right C hC
  | pop hr hlhs hc hrhs rest =>
      calc
        (NFParse.pop hr hlhs hc hrhs rest).beta.length = 1 := by simp
        _ ≤ C := hC1
        _ ≤ C * C := Nat.le_mul_of_pos_right C (by omega)
  | push hr hlhs hc hrhs rest =>
      have hrestAll : rest.AllBetaIn Z := by
        simpa [IsCritical, ProperBetaIn] using hcritical.2
      have hrestBound := hbound rest.beta (beta_mem_of_allBetaIn hrestAll)
      let q := NFParse.push hr hlhs hc hrhs rest
      by_cases hstack : parsedStack q = []
      · have hyield : (parsedWord q).length ≤ (rest.scopeAt 0).length * C := by
          have hbottom : (parsedStack rest).drop (0 + 1) = [] := by
            simpa [q, parsedStack] using hstack
          have hk : 0 < (parsedStack rest).length := by
            simp [q, parsedStack]
          simpa [q, parsedWord] using
            yield_length_le_scopeAt_mul_of_bottom hC1 hbound hrestAll 0 hk hbottom
        have hscope : (rest.scopeAt 0).length ≤ C := by
          rw [← rest.beta_length_eq_scopeAt_zero_of_stack_ne_nil]
          · exact hrestBound
          · simp [q, parsedStack]
        have hbetaYield : q.beta.length = (parsedWord q).length :=
          q.beta_length_eq_yield_of_stack_eq_nil hstack
        rw [hbetaYield]
        exact hyield.trans (Nat.mul_le_mul_right C hscope)
      · have hsucc : (rest.scopeAt 1).length ≤ (rest.scopeAt 0).length * C := by
          have hk : 0 + 1 < (parsedStack rest).length := by
            dsimp [q, parsedStack] at hstack ⊢
            cases sigma <;> simp_all
          simpa using scopeAt_succ_length_le_of_allBetaIn hC1 hbound hrestAll 0 hk
        have hscope : (rest.scopeAt 0).length ≤ C := by
          rw [← rest.beta_length_eq_scopeAt_zero_of_stack_ne_nil]
          · exact hrestBound
          · simp [q, parsedStack]
        have hbetaScope : q.beta.length = (q.scopeAt 0).length :=
          q.beta_length_eq_scopeAt_zero_of_stack_ne_nil hstack
        rw [hbetaScope]
        change (rest.scopeAt 1).length ≤ C * C
        exact hsucc.trans (Nat.mul_le_mul_right C hscope)
  | terminal hr hlhs hc hrhs =>
      calc
        (NFParse.terminal hr hlhs hc hrhs).beta.length = 1 := by simp
        _ ≤ C := hC1
        _ ≤ C * C := Nat.le_mul_of_pos_right C (by omega)

end IndexedGrammar.NFParse
