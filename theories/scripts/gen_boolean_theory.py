#!/usr/bin/env python3
"""
Generate the full BooleanStringDiagrams.geolog theory.

Design: axioms are layered so the chase can fire them in sequence:
  Layer 1: rewrite type + structure relations -> gate types, boundary membership
  Layer 2: gate types + port relations -> boundary membership, wire rank  
  Layer 3: rewrite type + structure + port wiring -> wire identifications

This avoids circularity where axioms require wiring info to derive wiring info.
"""

from dataclasses import dataclass, field

@dataclass
class Gate:
    name: str
    n_inputs: int
    n_outputs: int

GATES = [
    Gate("not", 1, 1),
    Gate("and", 2, 1),
    Gate("copy", 1, 2),
    Gate("discard", 1, 0),
    Gate("const0", 0, 1),
    Gate("const1", 0, 1),
    Gate("sym", 2, 2),
    # id_wire removed — use bare equalities (a = b;) instead
]

@dataclass 
class RewriteRule:
    name: str
    # LHS gates: list of (gate_name, input_wire_names, output_wire_names)
    lhs: list[tuple[str, list[str], list[str]]]
    # RHS gates: same format
    rhs: list[tuple[str, list[str], list[str]]]
    # Wire identifications the rewrite implies (pairs of wire names that become equal)
    identifications: list[tuple[str, str]] = field(default_factory=list)

def gate_by_name(name: str) -> Gate:
    for g in GATES:
        if g.name == name:
            return g
    raise ValueError(f"Unknown gate: {name}")

def port_name(gate_name: str, is_input: bool, idx: int, gate: Gate) -> str:
    n = gate.n_inputs if is_input else gate.n_outputs
    direction = "in" if is_input else "out"
    suffix = f"_{idx}" if n > 1 else ""
    return f"{gate_name}_{direction}{suffix}"

RULES = [
    # NOT ; NOT = id: x->NOT->m->NOT->y becomes x==y
    RewriteRule("not_not",
        lhs=[("not", ["x"], ["m"]), ("not", ["m"], ["y"])],
        rhs=[],
        identifications=[("x", "y")]),
    
    # const0 ; NOT = const1
    RewriteRule("const0_not",
        lhs=[("const0", [], ["m"]), ("not", ["m"], ["y"])],
        rhs=[("const1", [], ["y"])]),
    
    # const1 ; NOT = const0
    RewriteRule("const1_not",
        lhs=[("const1", [], ["m"]), ("not", ["m"], ["y"])],
        rhs=[("const0", [], ["y"])]),

    # (id ⊗ const1) ; AND = id  i.e. x AND 1 = x
    RewriteRule("and_const1",
        lhs=[("const1", [], ["c"]), ("and", ["x", "c"], ["y"])],
        rhs=[],
        identifications=[("x", "y")]),

    # (id ⊗ const0) ; AND = discard ; const0  i.e. x AND 0 = 0
    RewriteRule("and_const0",
        lhs=[("const0", [], ["c"]), ("and", ["x", "c"], ["y"])],
        rhs=[("discard", ["x"], []), ("const0", [], ["y"])]),

    # sym ; AND = AND (commutativity)
    RewriteRule("and_comm",
        lhs=[("sym", ["a", "b"], ["sa", "sb"]), ("and", ["sa", "sb"], ["y"])],
        rhs=[("and", ["a", "b"], ["y"])]),

    # copy ; AND = id (idempotent)
    RewriteRule("and_idem",
        lhs=[("copy", ["x"], ["a", "b"]), ("and", ["a", "b"], ["y"])],
        rhs=[],
        identifications=[("x", "y")]),

    # copy ; (NOT ⊗ NOT) = NOT ; copy
    RewriteRule("copy_not",
        lhs=[("copy", ["x"], ["a", "b"]), ("not", ["a"], ["y1"]), ("not", ["b"], ["y2"])],
        rhs=[("not", ["x"], ["m"]), ("copy", ["m"], ["y1", "y2"])]),

    # copy ; (discard ⊗ id) = id
    RewriteRule("copy_counit_left",
        lhs=[("copy", ["x"], ["a", "y"]), ("discard", ["a"], [])],
        rhs=[],
        identifications=[("x", "y")]),

    # copy ; (id ⊗ discard) = id
    RewriteRule("copy_counit_right",
        lhs=[("copy", ["x"], ["y", "b"]), ("discard", ["b"], [])],
        rhs=[],
        identifications=[("x", "y")]),

    # copy ; sym = copy
    RewriteRule("copy_cosym",
        lhs=[("copy", ["x"], ["a", "b"]), ("sym", ["a", "b"], ["y1", "y2"])],
        rhs=[("copy", ["x"], ["y1", "y2"])]),

    # const0 ; copy = const0 ⊗ const0
    RewriteRule("const0_copy",
        lhs=[("const0", [], ["m"]), ("copy", ["m"], ["y1", "y2"])],
        rhs=[("const0", [], ["y1"]), ("const0", [], ["y2"])]),

    # const1 ; copy = const1 ⊗ const1
    RewriteRule("const1_copy",
        lhs=[("const1", [], ["m"]), ("copy", ["m"], ["y1", "y2"])],
        rhs=[("const1", [], ["y1"]), ("const1", [], ["y2"])]),

    # NOT ; discard = discard
    RewriteRule("not_discard",
        lhs=[("not", ["x"], ["m"]), ("discard", ["m"], [])],
        rhs=[("discard", ["x"], [])]),

    # AND ; discard = discard ⊗ discard
    RewriteRule("and_discard",
        lhs=[("and", ["a", "b"], ["m"]), ("discard", ["m"], [])],
        rhs=[("discard", ["a"], []), ("discard", ["b"], [])]),

    # const0 ; discard = id (on 0 wires)
    RewriteRule("const0_discard",
        lhs=[("const0", [], ["m"]), ("discard", ["m"], [])],
        rhs=[]),

    # const1 ; discard = id (on 0 wires)
    RewriteRule("const1_discard",
        lhs=[("const1", [], ["m"]), ("discard", ["m"], [])],
        rhs=[]),

    # copy ; (discard ⊗ discard) = discard
    RewriteRule("copy_discard",
        lhs=[("copy", ["x"], ["a", "b"]), ("discard", ["a"], []), ("discard", ["b"], [])],
        rhs=[("discard", ["x"], [])]),

    # copy ; (id ⊗ NOT) ; AND = discard ; const0  (x AND NOT x = 0)
    RewriteRule("and_not",
        lhs=[("copy", ["x"], ["a", "b"]), ("not", ["b"], ["nb"]),
             ("and", ["a", "nb"], ["y"])],
        rhs=[("discard", ["x"], []), ("const0", [], ["y"])]),
]


def emit_theory():
    lines = []
    L = lines.append

    L("// Boolean String Diagrams as Cell Complexes")
    L("// AUTO-GENERATED by scripts/gen_boolean_theory.py")
    L("//")
    L("// 0-cells = wires, 1-cells = gates, 2-cells = rewrite steps")
    L("// Axioms are layered for chase evaluation:")
    L("//   Layer 1: rewrite structure -> gate types + boundary")
    L("//   Layer 2: gate ports -> boundary + wire rank + uniqueness")
    L("//   Layer 3: rewrite + ports -> wire identifications")
    L("")
    L("theory BoolCircuits {")
    L("  Cell : Sort;")
    L("")
    L("  // Rank predicates")
    L("  is_wire : Cell -> Prop;")
    L("  is_gate : Cell -> Prop;")
    L("  is_rewrite : Cell -> Prop;")
    L("")
    L("  // Boundary relations")
    L("  neg : [higher: Cell, lower: Cell] -> Prop;")
    L("  pos : [higher: Cell, lower: Cell] -> Prop;")
    L("")

    # Gate type predicates
    L("  // === Gate types ===")
    for g in GATES:
        L(f"  is_{g.name} : Cell -> Prop;")
    L("")

    # Port relations
    L("  // === Port relations ===")
    for g in GATES:
        for i in range(g.n_inputs):
            L(f"  {port_name(g.name, True, i, g)} : [gate: Cell, wire: Cell] -> Prop;")
        for i in range(g.n_outputs):
            L(f"  {port_name(g.name, False, i, g)} : [gate: Cell, wire: Cell] -> Prop;")
    L("")

    # Rewrite rule predicates
    L("  // === Rewrite rule types ===")
    for r in RULES:
        L(f"  is_{r.name} : Cell -> Prop;")
    L("")

    # Rewrite structure relations (which gates are on each side)
    L("  // === Rewrite structure relations ===")
    for r in RULES:
        for i, _ in enumerate(r.lhs):
            L(f"  {r.name}_lhs_{i} : [rw: Cell, gate: Cell] -> Prop;")
        for i, _ in enumerate(r.rhs):
            L(f"  {r.name}_rhs_{i} : [rw: Cell, gate: Cell] -> Prop;")
    L("")

    # ========== AXIOMS ==========
    L("  // ========== LAYER 1: Rank constraints ==========")
    L("")
    L("  ax/neg_gate_wire : forall g: Cell, w: Cell.")
    L("    g is_gate, [higher: g, lower: w] neg |- w is_wire;")
    L("  ax/pos_gate_wire : forall g: Cell, w: Cell.")
    L("    g is_gate, [higher: g, lower: w] pos |- w is_wire;")
    L("  ax/neg_rw_gate : forall r: Cell, c: Cell.")
    L("    r is_rewrite, [higher: r, lower: c] neg |- c is_gate;")
    L("  ax/pos_rw_gate : forall r: Cell, c: Cell.")
    L("    r is_rewrite, [higher: r, lower: c] pos |- c is_gate;")
    L("")

    # ========== LAYER 2: Gate port axioms ==========
    L("  // ========== LAYER 2: Gate port axioms ==========")
    L("")
    for g in GATES:
        L(f"  // --- {g.name} ---")
        for i in range(g.n_inputs):
            pn = port_name(g.name, True, i, g)
            L(f"  ax/{pn}_neg : forall g: Cell, w: Cell.")
            L(f"    g is_{g.name}, [gate: g, wire: w] {pn} |- [higher: g, lower: w] neg;")
            L(f"  ax/{pn}_wire : forall g: Cell, w: Cell.")
            L(f"    [gate: g, wire: w] {pn} |- w is_wire;")
            L(f"  ax/{pn}_uniq : forall g: Cell, w1: Cell, w2: Cell.")
            L(f"    [gate: g, wire: w1] {pn}, [gate: g, wire: w2] {pn} |- w1 = w2;")

        for i in range(g.n_outputs):
            pn = port_name(g.name, False, i, g)
            L(f"  ax/{pn}_pos : forall g: Cell, w: Cell.")
            L(f"    g is_{g.name}, [gate: g, wire: w] {pn} |- [higher: g, lower: w] pos;")
            L(f"  ax/{pn}_wire : forall g: Cell, w: Cell.")
            L(f"    [gate: g, wire: w] {pn} |- w is_wire;")
            L(f"  ax/{pn}_uniq : forall g: Cell, w1: Cell, w2: Cell.")
            L(f"    [gate: g, wire: w1] {pn}, [gate: g, wire: w2] {pn} |- w1 = w2;")
        L("")


    # --- Gate type mutual exclusivity ---
    L("  // --- Gate type mutual exclusivity ---")
    for i in range(len(GATES)):
        for j in range(i + 1, len(GATES)):
            gi, gj = GATES[i], GATES[j]
            L(f"  ax/excl_{gi.name}_{gj.name} : forall g: Cell. g is_{gi.name}, g is_{gj.name} |- false;")
    L("")

    # ========== LAYER 3: Rewrite rule axioms ==========
    L("  // ========== LAYER 3: Rewrite rule axioms ==========")
    L("")
    
    for r in RULES:
        L(f"  // --- {r.name} ---")
        
        # Layer 3a: rewrite + structure -> gate type + boundary (2-variable axioms)
        for i, (gname, _, _) in enumerate(r.lhs):
            L(f"  ax/{r.name}_lhs{i}_type : forall rw: Cell, g: Cell.")
            L(f"    rw is_{r.name}, [rw: rw, gate: g] {r.name}_lhs_{i}")
            L(f"    |- g is_{gname} /\\ g is_gate /\\ [higher: rw, lower: g] neg;")
        
        for i, (gname, _, _) in enumerate(r.rhs):
            L(f"  ax/{r.name}_rhs{i}_type : forall rw: Cell, g: Cell.")
            L(f"    rw is_{r.name}, [rw: rw, gate: g] {r.name}_rhs_{i}")
            L(f"    |- g is_{gname} /\\ g is_gate /\\ [higher: rw, lower: g] pos;")
        
        # Layer 3a': distinctness — different slots must have different gates
        all_slots = [("lhs", i) for i in range(len(r.lhs))] + [("rhs", i) for i in range(len(r.rhs))]
        for si in range(len(all_slots)):
            for sj in range(si + 1, len(all_slots)):
                side_i, idx_i = all_slots[si]
                side_j, idx_j = all_slots[sj]
                rel_i = f"{r.name}_{side_i}_{idx_i}"
                rel_j = f"{r.name}_{side_j}_{idx_j}"
                L(f"  strict ax/{r.name}_distinct_{si}_{sj} : forall rw: Cell, g: Cell.")
                L(f"    rw is_{r.name}, [rw: rw, gate: g] {rel_i}, [rw: rw, gate: g] {rel_j}")
                L(f"    |- false;")

        # Layer 3b: wire identifications from rewrite rules
        # These need to connect ports of different gates.
        # Strategy: for each identification (w1, w2), find the gates+ports
        # that produce w1 and w2, and emit an axiom linking them.
        
        # First, build a map from wire name -> which gate/port produces/consumes it
        wire_producers = {}  # wire -> (side, gate_idx, is_input, port_idx)
        wire_consumers = {}
        
        for i, (gname, ins, outs) in enumerate(r.lhs):
            g = gate_by_name(gname)
            for j, w in enumerate(ins):
                wire_consumers.setdefault(w, []).append(("lhs", i, gname, True, j, g))
            for j, w in enumerate(outs):
                wire_producers.setdefault(w, []).append(("lhs", i, gname, False, j, g))

        for i, (gname, ins, outs) in enumerate(r.rhs):
            g = gate_by_name(gname)
            for j, w in enumerate(ins):
                wire_consumers.setdefault(w, []).append(("rhs", i, gname, True, j, g))
            for j, w in enumerate(outs):
                wire_producers.setdefault(w, []).append(("rhs", i, gname, False, j, g))

        # For each wire that appears on multiple ports, emit axioms linking them.
        # This handles both internal wiring (composition) and identifications.
        all_wires = set()
        for _, ins, outs in r.lhs + r.rhs:
            all_wires.update(ins)
            all_wires.update(outs)
        
        for w in sorted(all_wires):
            # All appearances of this wire across all gates
            appearances = []
            for side_gates, side_name in [(r.lhs, "lhs"), (r.rhs, "rhs")]:
                for gi, (gname, ins, outs) in enumerate(side_gates):
                    g = gate_by_name(gname)
                    for pi, win in enumerate(ins):
                        if win == w:
                            appearances.append((side_name, gi, gname, True, pi, g))
                    for pi, wout in enumerate(outs):
                        if wout == w:
                            appearances.append((side_name, gi, gname, False, pi, g))
            
            # For each pair of appearances, the wire must be the same
            # We only need to chain them (a=b, b=c implies a=c)
            for k in range(1, len(appearances)):
                a = appearances[0]
                b = appearances[k]
                
                a_side, a_gi, a_gname, a_is_in, a_pi, a_g = a
                b_side, b_gi, b_gname, b_is_in, b_pi, b_g = b
                
                a_port = port_name(a_gname, a_is_in, a_pi, a_g)
                b_port = port_name(b_gname, b_is_in, b_pi, b_g)
                a_struct = f"{r.name}_{a_side}_{a_gi}"
                b_struct = f"{r.name}_{b_side}_{b_gi}"
                
                a_var = f"g{a_side}{a_gi}"
                b_var = f"g{b_side}{b_gi}"
                
                # Axiom: if rw is this rewrite, and ga is the a-th gate, and gb is the b-th gate,
                # and ga has wire w on port a_port, then gb also has w on port b_port
                L(f"  strict ax/{r.name}_wire_{w}_{k} : forall rw: Cell, {a_var}: Cell, {b_var}: Cell, w: Cell.")
                L(f"    rw is_{r.name},")
                L(f"    [rw: rw, gate: {a_var}] {a_struct},")
                L(f"    [rw: rw, gate: {b_var}] {b_struct},")
                L(f"    [gate: {a_var}, wire: w] {a_port}")
                L(f"    |- [gate: {b_var}, wire: w] {b_port};")
        
        # Wire identifications (explicit equalities like x=y in not_not)
        for eq_idx, (w1, w2) in enumerate(r.identifications):
            # Find one appearance of w1 and one of w2
            def find_appearance(wname):
                for side_gates, side_name in [(r.lhs, "lhs"), (r.rhs, "rhs")]:
                    for gi, (gname, ins, outs) in enumerate(side_gates):
                        g = gate_by_name(gname)
                        for pi, win in enumerate(ins):
                            if win == wname:
                                return (side_name, gi, gname, True, pi, g)
                        for pi, wout in enumerate(outs):
                            if wout == wname:
                                return (side_name, gi, gname, False, pi, g)
                return None
            
            a = find_appearance(w1)
            b = find_appearance(w2)
            
            if a and b:
                a_side, a_gi, a_gname, a_is_in, a_pi, a_g = a
                b_side, b_gi, b_gname, b_is_in, b_pi, b_g = b
                
                a_port = port_name(a_gname, a_is_in, a_pi, a_g)
                b_port = port_name(b_gname, b_is_in, b_pi, b_g)
                a_struct = f"{r.name}_{a_side}_{a_gi}"
                b_struct = f"{r.name}_{b_side}_{b_gi}"
                a_var = f"g{a_side}{a_gi}"
                b_var = f"g{b_side}{b_gi}"
                
                if a_var == b_var:
                    # Same gate: wire w1 on port a = wire w2 on port b
                    L(f"  ax/{r.name}_eq_{eq_idx} : forall rw: Cell, {a_var}: Cell, wa: Cell, wb: Cell.")
                    L(f"    rw is_{r.name},")
                    L(f"    [rw: rw, gate: {a_var}] {a_struct},")
                    L(f"    [gate: {a_var}, wire: wa] {a_port},")
                    L(f"    [gate: {a_var}, wire: wb] {b_port}")
                    L(f"    |- wa = wb;")
                else:
                    L(f"  ax/{r.name}_eq_{eq_idx} : forall rw: Cell, {a_var}: Cell, {b_var}: Cell, wa: Cell, wb: Cell.")
                    L(f"    rw is_{r.name},")
                    L(f"    [rw: rw, gate: {a_var}] {a_struct},")
                    L(f"    [rw: rw, gate: {b_var}] {b_struct},")
                    L(f"    [gate: {a_var}, wire: wa] {a_port},")
                    L(f"    [gate: {b_var}, wire: wb] {b_port}")
                    L(f"    |- wa = wb;")
        
        L("")


    # ========== LAYER 4: Proof well-formedness ==========
    L("  // ========== LAYER 4: Proof well-formedness ==========")
    L("")
    L("  // LHS/RHS membership (marked by the problem definition)")
    L("  in_lhs : Cell -> Prop;")
    L("  in_rhs : Cell -> Prop;")
    L("")
    L("  // Reachability: transitive closure of the proof-order relation")
    L("  before : [from: Cell, to: Cell] -> Prop;")
    L("")
    L("  // Base cases: boundary implies ordering")
    L("  ax/before_neg : forall a: Cell, b: Cell.")
    L("    [higher: b, lower: a] neg |- [from: a, to: b] before;")
    L("  ax/before_pos : forall a: Cell, b: Cell.")
    L("    [higher: a, lower: b] pos |- [from: b, to: a] before;")
    L("  // Transitivity")
    L("  ax/before_trans : forall a: Cell, b: Cell, c: Cell.")
    L("    [from: a, to: b] before, [from: b, to: c] before")
    L("    |- [from: a, to: c] before;")
    L("")
    L("  // ACYCLICITY: no cell is before itself")
    L("  strict ax/acyclic : forall a: Cell. [from: a, to: a] before |- false;")
    L("")
    L("  // GLOBULARITY / DOUBLE-BOUNDARY COHERENCE")
    L("  // A wire seen across a rewrite via mixed polarity (pos→neg or neg→pos)")
    L("  // must also be seen via same polarity (pos→pos or neg→neg), and conversely.")
    L("  // This prevents holes where a rewrite touches gates whose boundary wires do not")
    L("  // line up as a genuine 2-cell boundary.")
    L("  strict ax/glob_pos_neg : forall rw: Cell, g: Cell, w: Cell.")
    L("    rw is_rewrite, [higher: rw, lower: g] pos, [higher: g, lower: w] neg")
    L("    |- (exists gp: Cell. [higher: rw, lower: gp] pos, [higher: gp, lower: w] pos) \\/")
    L("       (exists gn: Cell. [higher: rw, lower: gn] neg, [higher: gn, lower: w] neg);")
    L("  strict ax/glob_neg_pos : forall rw: Cell, g: Cell, w: Cell.")
    L("    rw is_rewrite, [higher: rw, lower: g] neg, [higher: g, lower: w] pos")
    L("    |- (exists gp: Cell. [higher: rw, lower: gp] pos, [higher: gp, lower: w] pos) \\/")
    L("       (exists gn: Cell. [higher: rw, lower: gn] neg, [higher: gn, lower: w] neg);")
    L("  strict ax/glob_pos_pos : forall rw: Cell, g: Cell, w: Cell.")
    L("    rw is_rewrite, [higher: rw, lower: g] pos, [higher: g, lower: w] pos")
    L("    |- (exists gp: Cell. [higher: rw, lower: gp] pos, [higher: gp, lower: w] neg) \\/")
    L("       (exists gn: Cell. [higher: rw, lower: gn] neg, [higher: gn, lower: w] pos);")
    L("  strict ax/glob_neg_neg : forall rw: Cell, g: Cell, w: Cell.")
    L("    rw is_rewrite, [higher: rw, lower: g] neg, [higher: g, lower: w] neg")
    L("    |- (exists gp: Cell. [higher: rw, lower: gp] pos, [higher: gp, lower: w] neg) \\/")
    L("       (exists gn: Cell. [higher: rw, lower: gn] neg, [higher: gn, lower: w] pos);")
    L("")
    L("  // COVERAGE: every gate must be accounted for")
    L("  // Intuition: this literally checks that there are no holes in the proof.")
    L("  // A gate is covered on the positive side if it is explicitly part of the starting LHS")
    L("  // or is produced by the positive boundary of some rewrite.")
    L("  // A gate is covered on the negative side if it is explicitly part of the final RHS")
    L("  // or is consumed by the negative boundary of some rewrite.")
    L("  // If a gate is unchanged by the proof (a whiskered / passthrough gate), it can simply")
    L("  // be marked both `in_lhs` and `in_rhs` rather than being mentioned in any rewrite.")
    L("  strict ax/coverage_pos : forall c: Cell.")
    L("    c is_gate")
    L("    |- c in_lhs \\/ (exists h: Cell. [higher: h, lower: c] pos);")
    L("  strict ax/coverage_neg : forall c: Cell.")
    L("    c is_gate")
    L("    |- c in_rhs \\/ (exists h: Cell. [higher: h, lower: c] neg);")
    L("")
    L("}")

    return "\n".join(lines)


if __name__ == "__main__":
    print(emit_theory())
