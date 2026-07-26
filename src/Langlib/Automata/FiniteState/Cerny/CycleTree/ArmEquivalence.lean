module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.Coordinates

@[expose]
public section

/-!
# Equivalence with the three-arm presentation

The construction was originally described by a central `p`-cycle
`e → a → k → b → e`, three alternating arms, and a terminal state `z`.
This file gives that presentation a state type independent of the
hidden-cycle coordinates.
-/

namespace DFA.CycleTree

/-- States in the original three-arm presentation.  `left` and `right`
refer to the endpoints of a `p`-transposition, numbered from the root. -/
inductive ArmState (P : Params)
  | e
  | a
  | k
  | b
  | xLeft (index : Fin P.X)
  | xRight (index : Fin P.X)
  | rLeft (index : Fin P.R)
  | rRight (index : Fin P.R)
  | lLeft (index : Fin P.L)
  | lRight (index : Fin P.L)
  | z
  deriving DecidableEq, Fintype, Repr

/-- The permutation letter in the original arm presentation. -/
def armPMap (P : Params) : ArmState P → ArmState P
  | .e => .a
  | .a => .k
  | .k => .b
  | .b => .e
  | .xLeft index => .xRight index
  | .xRight index => .xLeft index
  | .rLeft index => .rRight index
  | .rRight index => .rLeft index
  | .lLeft index => .lRight index
  | .lRight index => .lLeft index
  | .z => .z

/-- The involution `π` that alternates with `p` along the three arms. -/
def armPiMap (P : Params) : ArmState P → ArmState P
  | .e => .e
  | .a =>
      if h : 0 < P.X then .xLeft ⟨0, h⟩ else .a
  | .xLeft index =>
      if h : index.val = 0 then .a
      else .xRight ⟨index.val - 1, by omega⟩
  | .xRight index =>
      if h : index.val + 1 < P.X
      then .xLeft ⟨index.val + 1, h⟩
      else .xRight index
  | .k =>
      if h : 0 < P.R then .rLeft ⟨0, h⟩ else .k
  | .rLeft index =>
      if h : index.val = 0 then .k
      else .rRight ⟨index.val - 1, by omega⟩
  | .rRight index =>
      if h : index.val + 1 < P.R
      then .rLeft ⟨index.val + 1, h⟩
      else .rRight index
  | .b =>
      if h : 0 < P.L then .lLeft ⟨0, h⟩ else .z
  | .lLeft index =>
      if h : index.val = 0 then .b
      else .lRight ⟨index.val - 1, by omega⟩
  | .lRight index =>
      if h : index.val + 1 < P.L
      then .lLeft ⟨index.val + 1, h⟩
      else .z
  | .z =>
      if h : 0 < P.L
      then .lRight ⟨P.L - 1, by omega⟩
      else .b

/-- The defect-one letter `s = cπ`, where `c` sends `e` to `k`. -/
def armSMap (P : Params) : ArmState P → ArmState P
  | .e => armPiMap P .k
  | state => armPiMap P state

/-- The DFA defined directly from the original alternating-arm wiring. -/
def armAutomaton (P : Params) : DFA Letter (ArmState P) where
  step state
    | .p => armPMap P state
    | .s => armSMap P state
  start := .e
  accept := Set.univ

/-- Natural hidden-cycle coordinate of an arm state.  Physical arm indices
are zero-based from the root. -/
def armCoordinate (P : Params) : ArmState P → ℕ
  | .e => 0
  | .a => 1
  | .xRight index => 2 + index.val
  | .xLeft index => P.ell - 1 - index.val
  | .k => P.ell
  | .rRight index => P.ell + 1 + index.val
  | .rLeft index => P.rho - 1 - index.val
  | .b => P.rho
  | .lRight index => P.rho + 1 + index.val
  | .z => P.rho + P.L + 1
  | .lLeft index => P.order - 1 - index.val

theorem armCoordinate_lt (P : Params) (state : ArmState P) :
    armCoordinate P state < P.order := by
  cases state <;>
    simp [armCoordinate, Params.ell, Params.rho, Params.m,
      Params.order, Params.cycle] <;>
    omega

/-- Relabel an original arm state by its position on the `h = πp` orbit
starting at `e`. -/
def armToCoordinate (P : Params) (state : ArmState P) : State P :=
  ⟨armCoordinate P state, armCoordinate_lt P state⟩

theorem armToCoordinate_injective (P : Params) :
    Function.Injective (armToCoordinate P) := by
  intro left right heq
  have hval := congrArg Fin.val heq
  change armCoordinate P left = armCoordinate P right at hval
  cases left <;> cases right <;>
    simp_all [armCoordinate, Params.ell, Params.rho, Params.m,
      Params.order, Params.cycle, Fin.ext_iff] <;>
    omega

theorem armToCoordinate_surjective (P : Params) :
    Function.Surjective (armToCoordinate P) := by
  intro coordinate
  let x := coordinate.val
  have hxOrder : x < P.order := coordinate.isLt
  by_cases hxZero : x = 0
  · refine ⟨.e, Fin.ext ?_⟩
    simpa [armToCoordinate, armCoordinate, x] using hxZero.symm
  by_cases hxOne : x = 1
  · refine ⟨.a, Fin.ext ?_⟩
    simpa [armToCoordinate, armCoordinate, x] using hxOne.symm
  by_cases hxBeforeEll : x < P.ell
  · by_cases hxRight : x ≤ P.X + 1
    · let index : Fin P.X := ⟨x - 2, by
        simp [Params.ell] at hxBeforeEll
        omega⟩
      refine ⟨.xRight index, Fin.ext ?_⟩
      change 2 + (x - 2) = x
      omega
    · let index : Fin P.X := ⟨P.ell - 1 - x, by
        simp [Params.ell] at hxBeforeEll ⊢
        omega⟩
      refine ⟨.xLeft index, Fin.ext ?_⟩
      change P.ell - 1 - (P.ell - 1 - x) = x
      omega
  by_cases hxEll : x = P.ell
  · refine ⟨.k, Fin.ext ?_⟩
    simpa [armToCoordinate, armCoordinate, x] using hxEll.symm
  by_cases hxBeforeRho : x < P.rho
  · by_cases hxRight : x ≤ P.ell + P.R
    · let index : Fin P.R := ⟨x - P.ell - 1, by
        rw [P.rho_eq] at hxBeforeRho
        omega⟩
      refine ⟨.rRight index, Fin.ext ?_⟩
      change P.ell + 1 + (x - P.ell - 1) = x
      omega
    · let index : Fin P.R := ⟨P.rho - 1 - x, by
        rw [P.rho_eq] at hxBeforeRho ⊢
        omega⟩
      refine ⟨.rLeft index, Fin.ext ?_⟩
      change P.rho - 1 - (P.rho - 1 - x) = x
      omega
  by_cases hxRho : x = P.rho
  · refine ⟨.b, Fin.ext ?_⟩
    simpa [armToCoordinate, armCoordinate, x] using hxRho.symm
  by_cases hxRight : x ≤ P.rho + P.L
  · let index : Fin P.L := ⟨x - P.rho - 1, by omega⟩
    refine ⟨.lRight index, Fin.ext ?_⟩
    change P.rho + 1 + (x - P.rho - 1) = x
    omega
  by_cases hxZ : x = P.rho + P.L + 1
  · refine ⟨.z, Fin.ext ?_⟩
    simpa [armToCoordinate, armCoordinate, x] using hxZ.symm
  · let index : Fin P.L := ⟨P.order - 1 - x, by
      have horder : P.order = P.rho + 2 * P.L + 2 := by
        simp [Params.order, Params.cycle, Params.rho, Params.m,
          Params.ell]
        omega
      rw [horder] at hxOrder ⊢
      omega⟩
    refine ⟨.lLeft index, Fin.ext ?_⟩
    change P.order - 1 - (P.order - 1 - x) = x
    omega

/-- The explicit conjugating bijection from arm states to hidden-cycle
coordinates. -/
noncomputable def armStateEquiv (P : Params) : ArmState P ≃ State P :=
  Equiv.ofBijective (armToCoordinate P)
    ⟨armToCoordinate_injective P, armToCoordinate_surjective P⟩

@[simp]
theorem armStateEquiv_apply (P : Params) (state : ArmState P) :
    armStateEquiv P state = armToCoordinate P state :=
  rfl

@[simp]
theorem armToCoordinate_val (P : Params) (state : ArmState P) :
    (armToCoordinate P state).val = armCoordinate P state :=
  rfl

@[simp]
theorem stateOfNat_armCoordinate (P : Params) (state : ArmState P) :
    P.stateOfNat (armCoordinate P state) = armToCoordinate P state := by
  rw [← armToCoordinate_val]
  exact stateOfNat_state_val P (armToCoordinate P state)

theorem armToCoordinate_eq_stateOfNat (P : Params)
    (state : ArmState P) (coordinate : ℕ)
    (hcoordinate : armCoordinate P state = coordinate) :
    armToCoordinate P state = P.stateOfNat coordinate := by
  conv_lhs => rw [← stateOfNat_armCoordinate P state]
  rw [hcoordinate]

/-- The explicit orbit relabeling conjugates the original permutation
letter to the coordinate formula. -/
theorem armToCoordinate_p (P : Params) (state : ArmState P) :
    armToCoordinate P (armPMap P state) =
      pMap P (armToCoordinate P state) := by
  cases state with
  | e =>
      rw [pMap_at_zero P _ (by rfl)]
      change armToCoordinate P .a = P.stateOfNat 1
      conv_lhs => rw [← stateOfNat_armCoordinate P .a]
      rfl
  | a =>
      rw [pMap_at_one P _ (by rfl)]
      change armToCoordinate P .k = P.stateOfNat P.ell
      conv_lhs => rw [← stateOfNat_armCoordinate P .k]
      rfl
  | k =>
      rw [pMap_at_ell P _ (by rfl)]
      change armToCoordinate P .b = P.stateOfNat P.rho
      conv_lhs => rw [← stateOfNat_armCoordinate P .b]
      rfl
  | b =>
      rw [pMap_at_rho P _ (by rfl)]
      change armToCoordinate P .e = P.stateOfNat 0
      conv_lhs => rw [← stateOfNat_armCoordinate P .e]
      rfl
  | xLeft index =>
      have htwo : 2 ≤ (armToCoordinate P (.xLeft index)).val := by
        change 2 ≤ P.ell - 1 - index.val
        simp [Params.ell]
        omega
      have hell :
          (armToCoordinate P (.xLeft index)).val < P.ell := by
        change P.ell - 1 - index.val < P.ell
        have := P.ell_pos
        omega
      rw [pMap_before_ell P _ htwo hell]
      change armToCoordinate P (.xRight index) =
        P.stateOfNat (P.ell + 1 -
          (armToCoordinate P (.xLeft index)).val)
      conv_lhs => rw [← stateOfNat_armCoordinate P (.xRight index)]
      apply congrArg P.stateOfNat
      change 2 + index.val =
        P.ell + 1 - (P.ell - 1 - index.val)
      simp [Params.ell]
      omega
  | xRight index =>
      have htwo : 2 ≤ (armToCoordinate P (.xRight index)).val := by
        change 2 ≤ 2 + index.val
        omega
      have hell :
          (armToCoordinate P (.xRight index)).val < P.ell := by
        change 2 + index.val < P.ell
        simp [Params.ell]
        omega
      rw [pMap_before_ell P _ htwo hell]
      change armToCoordinate P (.xLeft index) =
        P.stateOfNat (P.ell + 1 -
          (armToCoordinate P (.xRight index)).val)
      conv_lhs => rw [← stateOfNat_armCoordinate P (.xLeft index)]
      apply congrArg P.stateOfNat
      change P.ell - 1 - index.val =
        P.ell + 1 - (2 + index.val)
      omega
  | rLeft index =>
      have hell : P.ell <
          (armToCoordinate P (.rLeft index)).val := by
        change P.ell < P.rho - 1 - index.val
        rw [P.rho_eq]
        omega
      have hrho :
          (armToCoordinate P (.rLeft index)).val < P.rho := by
        change P.rho - 1 - index.val < P.rho
        have hrhoPos : 0 < P.rho := by
          simp [Params.rho, Params.m]
        omega
      rw [pMap_between_ell_rho P _ hell hrho]
      change armToCoordinate P (.rRight index) =
        P.stateOfNat (P.ell + P.rho -
          (armToCoordinate P (.rLeft index)).val)
      conv_lhs => rw [← stateOfNat_armCoordinate P (.rRight index)]
      apply congrArg P.stateOfNat
      change P.ell + 1 + index.val =
        P.ell + P.rho - (P.rho - 1 - index.val)
      rw [P.rho_eq]
      omega
  | rRight index =>
      have hell : P.ell <
          (armToCoordinate P (.rRight index)).val := by
        change P.ell < P.ell + 1 + index.val
        omega
      have hrho :
          (armToCoordinate P (.rRight index)).val < P.rho := by
        change P.ell + 1 + index.val < P.rho
        rw [P.rho_eq]
        omega
      rw [pMap_between_ell_rho P _ hell hrho]
      change armToCoordinate P (.rLeft index) =
        P.stateOfNat (P.ell + P.rho -
          (armToCoordinate P (.rRight index)).val)
      conv_lhs => rw [← stateOfNat_armCoordinate P (.rLeft index)]
      apply congrArg P.stateOfNat
      change P.rho - 1 - index.val =
        P.ell + P.rho - (P.ell + 1 + index.val)
      omega
  | lLeft index =>
      have hrho : P.rho <
          (armToCoordinate P (.lLeft index)).val := by
        change P.rho < P.order - 1 - index.val
        simp [Params.order, Params.cycle, P.rho_eq]
        omega
      rw [pMap_after_rho P _ hrho]
      change armToCoordinate P (.lRight index) =
        P.stateOfNat (P.rho + P.order -
          (armToCoordinate P (.lLeft index)).val)
      conv_lhs => rw [← stateOfNat_armCoordinate P (.lRight index)]
      apply congrArg P.stateOfNat
      change P.rho + 1 + index.val =
        P.rho + P.order - (P.order - 1 - index.val)
      have horder : P.order = P.rho + 2 * P.L + 2 := by
        simp [Params.order, Params.cycle, Params.rho, Params.m,
          Params.ell]
        omega
      rw [horder]
      omega
  | lRight index =>
      have hrho : P.rho <
          (armToCoordinate P (.lRight index)).val := by
        change P.rho < P.rho + 1 + index.val
        omega
      rw [pMap_after_rho P _ hrho]
      change armToCoordinate P (.lLeft index) =
        P.stateOfNat (P.rho + P.order -
          (armToCoordinate P (.lRight index)).val)
      conv_lhs => rw [← stateOfNat_armCoordinate P (.lLeft index)]
      apply congrArg P.stateOfNat
      change P.order - 1 - index.val =
        P.rho + P.order - (P.rho + 1 + index.val)
      have horder : P.order = P.rho + 2 * P.L + 2 := by
        simp [Params.order, Params.cycle, Params.rho, Params.m,
          Params.ell]
        omega
      rw [horder]
      omega
  | z =>
      have hrho : P.rho < (armToCoordinate P .z).val := by
        change P.rho < P.rho + P.L + 1
        omega
      rw [pMap_after_rho P _ hrho]
      change armToCoordinate P .z =
        P.stateOfNat (P.rho + P.order -
          (armToCoordinate P .z).val)
      conv_lhs => rw [← stateOfNat_armCoordinate P .z]
      apply congrArg P.stateOfNat
      change P.rho + P.L + 1 =
        P.rho + P.order - (P.rho + P.L + 1)
      have horder : P.order = P.rho + 2 * P.L + 2 := by
        simp [Params.order, Params.cycle, Params.rho, Params.m,
          Params.ell]
        omega
      rw [horder]
      omega

/-- The same orbit relabeling conjugates the original defect-one letter to
the coordinate formula.  The proof includes all three zero-arm boundary
cases. -/
theorem armToCoordinate_s (P : Params) (state : ArmState P) :
    armToCoordinate P (armSMap P state) =
      sMap P (armToCoordinate P state) := by
  cases state with
  | e =>
      rw [sMap_at_zero P _ (by rfl)]
      apply armToCoordinate_eq_stateOfNat
      by_cases hR : 0 < P.R
      · simp [armSMap, armPiMap, hR, armCoordinate]
      · have hRzero : P.R = 0 := by omega
        simp [armSMap, armPiMap, armCoordinate, P.rho_eq,
          hRzero]
  | a =>
      have hzero : 0 < (armToCoordinate P .a).val := by
        change 0 < 1
        omega
      have hell : (armToCoordinate P .a).val < P.ell := by
        change 1 < P.ell
        simp [Params.ell]
      rw [sMap_between_zero_ell P _ hzero hell]
      apply armToCoordinate_eq_stateOfNat
      by_cases hX : 0 < P.X
      · simp [armSMap, armPiMap, hX, armCoordinate]
      · have hXzero : P.X = 0 := by omega
        simp [armSMap, armPiMap, armCoordinate, Params.ell,
          hXzero]
  | k =>
      rw [sMap_at_ell P _ (by rfl)]
      apply armToCoordinate_eq_stateOfNat
      by_cases hR : 0 < P.R
      · simp [armSMap, armPiMap, hR, armCoordinate]
      · have hRzero : P.R = 0 := by omega
        simp [armSMap, armPiMap, armCoordinate, P.rho_eq,
          hRzero]
  | b =>
      rw [sMap_at_or_after_rho P _ (by rfl)]
      apply armToCoordinate_eq_stateOfNat
      by_cases hL : 0 < P.L
      · simp only [armSMap, armPiMap, hL, armCoordinate,
          armToCoordinate_val]
        change P.order - 1 =
          P.rho + P.order - 1 - P.rho
        omega
      · have hLzero : P.L = 0 := by omega
        simp only [armSMap, armPiMap, hL, armCoordinate,
          armToCoordinate_val]
        change P.rho + P.L + 1 =
          P.rho + P.order - 1 - P.rho
        have horder : P.order = P.rho + 2 * P.L + 2 := by
          simp [Params.order, Params.cycle, Params.rho, Params.m,
            Params.ell]
          omega
        rw [horder, hLzero]
        omega
  | xLeft index =>
      have hzero :
          0 < (armToCoordinate P (.xLeft index)).val := by
        change 0 < P.ell - 1 - index.val
        simp [Params.ell]
        omega
      have hell :
          (armToCoordinate P (.xLeft index)).val < P.ell := by
        change P.ell - 1 - index.val < P.ell
        have := P.ell_pos
        omega
      rw [sMap_between_zero_ell P _ hzero hell]
      apply armToCoordinate_eq_stateOfNat
      by_cases hfirst : index.val = 0
      · simp [armSMap, armPiMap, hfirst, armCoordinate]
        omega
      · simp [armSMap, armPiMap, hfirst, armCoordinate]
        simp [Params.ell]
        omega
  | xRight index =>
      have hzero :
          0 < (armToCoordinate P (.xRight index)).val := by
        change 0 < 2 + index.val
        omega
      have hell :
          (armToCoordinate P (.xRight index)).val < P.ell := by
        change 2 + index.val < P.ell
        simp [Params.ell]
        omega
      rw [sMap_between_zero_ell P _ hzero hell]
      apply armToCoordinate_eq_stateOfNat
      by_cases hnext : index.val + 1 < P.X
      · simp [armSMap, armPiMap, hnext, armCoordinate]
        omega
      · simp [armSMap, armPiMap, hnext, armCoordinate]
        simp [Params.ell]
        omega
  | rLeft index =>
      have hell : P.ell <
          (armToCoordinate P (.rLeft index)).val := by
        change P.ell < P.rho - 1 - index.val
        rw [P.rho_eq]
        omega
      have hrho :
          (armToCoordinate P (.rLeft index)).val < P.rho := by
        change P.rho - 1 - index.val < P.rho
        have hrhoPos : 0 < P.rho := by
          simp [Params.rho, Params.m]
        omega
      rw [sMap_between_ell_rho P _ hell hrho]
      apply armToCoordinate_eq_stateOfNat
      by_cases hfirst : index.val = 0
      · simp [armSMap, armPiMap, hfirst, armCoordinate]
        omega
      · simp [armSMap, armPiMap, hfirst, armCoordinate]
        rw [P.rho_eq]
        omega
  | rRight index =>
      have hell : P.ell <
          (armToCoordinate P (.rRight index)).val := by
        change P.ell < P.ell + 1 + index.val
        omega
      have hrho :
          (armToCoordinate P (.rRight index)).val < P.rho := by
        change P.ell + 1 + index.val < P.rho
        rw [P.rho_eq]
        omega
      rw [sMap_between_ell_rho P _ hell hrho]
      apply armToCoordinate_eq_stateOfNat
      by_cases hnext : index.val + 1 < P.R
      · simp [armSMap, armPiMap, hnext, armCoordinate]
        omega
      · simp [armSMap, armPiMap, hnext, armCoordinate]
        rw [P.rho_eq]
        omega
  | lLeft index =>
      have hrho : P.rho ≤
          (armToCoordinate P (.lLeft index)).val := by
        change P.rho ≤ P.order - 1 - index.val
        have horder : P.order = P.rho + 2 * P.L + 2 := by
          simp [Params.order, Params.cycle, Params.rho, Params.m,
            Params.ell]
          omega
        rw [horder]
        omega
      rw [sMap_at_or_after_rho P _ hrho]
      apply armToCoordinate_eq_stateOfNat
      by_cases hfirst : index.val = 0
      · simp [armSMap, armPiMap, hfirst, armCoordinate]
        omega
      · simp [armSMap, armPiMap, hfirst, armCoordinate]
        have horder : P.order = P.rho + 2 * P.L + 2 := by
          simp [Params.order, Params.cycle, Params.rho, Params.m,
            Params.ell]
          omega
        rw [horder]
        omega
  | lRight index =>
      have hrho : P.rho ≤
          (armToCoordinate P (.lRight index)).val := by
        change P.rho ≤ P.rho + 1 + index.val
        omega
      rw [sMap_at_or_after_rho P _ hrho]
      apply armToCoordinate_eq_stateOfNat
      by_cases hnext : index.val + 1 < P.L
      · simp [armSMap, armPiMap, hnext, armCoordinate]
        have horder : P.order = P.rho + 2 * P.L + 2 := by
          simp [Params.order, Params.cycle, Params.rho, Params.m,
            Params.ell]
          omega
        rw [horder]
        omega
      · simp [armSMap, armPiMap, hnext, armCoordinate]
        have horder : P.order = P.rho + 2 * P.L + 2 := by
          simp [Params.order, Params.cycle, Params.rho, Params.m,
            Params.ell]
          omega
        rw [horder]
        omega
  | z =>
      have hrho : P.rho ≤ (armToCoordinate P .z).val := by
        change P.rho ≤ P.rho + P.L + 1
        omega
      rw [sMap_at_or_after_rho P _ hrho]
      apply armToCoordinate_eq_stateOfNat
      by_cases hL : 0 < P.L
      · simp [armSMap, armPiMap, hL, armCoordinate]
        have horder : P.order = P.rho + 2 * P.L + 2 := by
          simp [Params.order, Params.cycle, Params.rho, Params.m,
            Params.ell]
          omega
        rw [horder]
        omega
      · have hLzero : P.L = 0 := by omega
        simp [armSMap, armPiMap, armCoordinate, hLzero]
        have horder : P.order = P.rho + 2 * P.L + 2 := by
          simp [Params.order, Params.cycle, Params.rho, Params.m,
            Params.ell]
          omega
        rw [horder, hLzero]
        omega

/-- Letter-by-letter conjugacy of the original and coordinate DFAs. -/
theorem armToCoordinate_step (P : Params) (state : ArmState P)
    (letter : Letter) :
    armToCoordinate P ((armAutomaton P).step state letter) =
      (automaton P).step (armToCoordinate P state) letter := by
  cases letter with
  | p => exact armToCoordinate_p P state
  | s => exact armToCoordinate_s P state

/-- Conjugacy extends from generators to every input word. -/
theorem armToCoordinate_evalFrom (P : Params) (state : ArmState P)
    (word : List Letter) :
    armToCoordinate P ((armAutomaton P).evalFrom state word) =
      (automaton P).evalFrom (armToCoordinate P state) word := by
  induction word generalizing state with
  | nil => rfl
  | cons letter word ih =>
      simp only [DFA.evalFrom_cons]
      rw [← armToCoordinate_step P state letter]
      exact ih _

/-- Reindexing the original arm transition along `armStateEquiv` gives the
coordinate transition. -/
theorem reindex_armAutomaton_step (P : Params) (state : State P)
    (letter : Letter) :
    ((DFA.reindex (armStateEquiv P)) (armAutomaton P)).step state letter =
      (automaton P).step state letter := by
  let original := (armStateEquiv P).symm state
  have hstate : armToCoordinate P original = state := by
    change armStateEquiv P original = state
    exact (armStateEquiv P).apply_symm_apply state
  change armToCoordinate P
      ((armAutomaton P).step original letter) =
    (automaton P).step state letter
  rw [armToCoordinate_step, hstate]

/-- A word resets the original three-arm presentation exactly when it
resets the hidden-cycle coordinate DFA. -/
theorem arm_isResetWord_iff (P : Params) (word : List Letter) :
    (armAutomaton P).IsResetWord word ↔
      (automaton P).IsResetWord word := by
  constructor
  · rintro ⟨target, htarget⟩
    refine ⟨armToCoordinate P target, ?_⟩
    intro coordinate
    let state := (armStateEquiv P).symm coordinate
    have hcoordinate : armToCoordinate P state = coordinate := by
      change armStateEquiv P state = coordinate
      exact (armStateEquiv P).apply_symm_apply coordinate
    calc
      (automaton P).evalFrom coordinate word =
          (automaton P).evalFrom (armToCoordinate P state) word := by
            rw [hcoordinate]
      _ = armToCoordinate P
          ((armAutomaton P).evalFrom state word) :=
            (armToCoordinate_evalFrom P state word).symm
      _ = armToCoordinate P target := by rw [htarget state]
  · rintro ⟨target, htarget⟩
    refine ⟨(armStateEquiv P).symm target, ?_⟩
    intro state
    apply armToCoordinate_injective P
    rw [armToCoordinate_evalFrom, htarget]
    change target = armStateEquiv P ((armStateEquiv P).symm target)
    exact (armStateEquiv P).apply_symm_apply target |>.symm

theorem arm_synchronizing_iff (P : Params) :
    (armAutomaton P).Synchronizing ↔
      (automaton P).Synchronizing := by
  simp only [DFA.Synchronizing]
  constructor
  · rintro ⟨word, hword⟩
    exact ⟨word, (arm_isResetWord_iff P word).mp hword⟩
  · rintro ⟨word, hword⟩
    exact ⟨word, (arm_isResetWord_iff P word).mpr hword⟩

theorem card_armState (P : Params) :
    Fintype.card (ArmState P) = P.order := by
  calc
    Fintype.card (ArmState P) = Fintype.card (State P) :=
      Fintype.card_congr (armStateEquiv P)
    _ = P.order := Fintype.card_fin P.order

theorem arm_cernyBound_eq (P : Params) :
    (armAutomaton P).cernyBound = (automaton P).cernyBound := by
  simp [DFA.cernyBound, card_armState]

/-- The Černý-bound conclusion is invariant under the explicit arm/coordinate
conjugacy. -/
theorem arm_satisfiesCerny_iff (P : Params) :
    (armAutomaton P).SatisfiesCerny ↔
      (automaton P).SatisfiesCerny := by
  constructor
  · rintro ⟨word, hreset, hlength⟩
    exact ⟨word, (arm_isResetWord_iff P word).mp hreset,
      hlength.trans_eq (arm_cernyBound_eq P)⟩
  · rintro ⟨word, hreset, hlength⟩
    exact ⟨word, (arm_isResetWord_iff P word).mpr hreset,
      hlength.trans_eq (arm_cernyBound_eq P).symm⟩

/-- Exact Černý statement for the family in its original three-arm
presentation. -/
def CompleteArmFamilySatisfiesCerny : Prop :=
  ∀ P : Params,
    (armAutomaton P).Synchronizing →
      (armAutomaton P).SatisfiesCerny

/-- The original-family theorem and the coordinate-family theorem are
logically identical under the explicit conjugacy. -/
theorem completeArmFamily_iff_coordinateFamily :
    CompleteArmFamilySatisfiesCerny ↔
      ∀ P : Params,
        (automaton P).Synchronizing →
          (automaton P).SatisfiesCerny := by
  constructor
  · intro hfamily P hsynchronizing
    exact (arm_satisfiesCerny_iff P).mp
      (hfamily P ((arm_synchronizing_iff P).mpr hsynchronizing))
  · intro hfamily P hsynchronizing
    exact (arm_satisfiesCerny_iff P).mpr
      (hfamily P ((arm_synchronizing_iff P).mp hsynchronizing))

end DFA.CycleTree
